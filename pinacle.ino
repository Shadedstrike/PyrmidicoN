// ESP32 (WROOM) + UDA1334A (CJMCU-1334)aaaaa
// Calm stereo synth with scale switching, pressure-controlled vibrato, and per-side note lock
// I2S: BCLK=GPIO33, WSEL/LRCLK=GPIO32, DATA=GPIO23
// Touch: LEFT=GPIO27 (T7), RIGHT=GPIO14 (T6)
// Gestures:
//   • Hold BOTH pads ~1.5 s  -> cycle musical scale
//   • Hold LEFT pad  ~1.0 s  -> toggle LEFT note lock (latch current note)
//   • Hold RIGHT pad ~1.0 s  -> toggle RIGHT note lock
// Locks persist until toggled off; idle sweeps disabled while any lock is active.

#include <driver/i2s.h>
#include <math.h>
#include <esp_random.h>

// ---------- I2S pins ----------
#define I2S_BCLK  33
#define I2S_LRCK  32
#define I2S_DATA  23

// ---------- Touch pins (GPIO numbers) ----------
#define TOUCH_L_GPIO  27   // T7
#define TOUCH_R_GPIO  14   // T6

// ---------- Audio ----------
const int   SR            = 44100;    // calm; 22050 also fine
const size_t BUF_SAMPLES  = 512;
const int   DMA_COUNT     = 12;
const float MASTER_VOL    = 0.80f;

// ---------- Musical scales (relative to A3=220 Hz) ----------
const float BASE_HZ = 220.0f;
struct ScaleDef { const char* name; const int8_t* steps; uint8_t count; };
const int8_t MAJ_PENTA[]  = { 0,2,4,7,9,12,14,16,19,21,24 };
const int8_t MIN_PENTA[]  = { 0,3,5,7,10,12,15,17,19,22,24 };
const int8_t MAJOR[]      = { 0,2,4,5,7,9,11,12,14,16,17,19,21,23,24 };
const int8_t NAT_MINOR[]  = { 0,2,3,5,7,8,10,12,14,15,17,19,20,22,24 };
const int8_t WHOLE[]      = { 0,2,4,6,8,10,12,14,16,18,20,22,24 };
const int8_t CHROMA[]     = { 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24 };
ScaleDef SCALES[] = {
  { "Major Pentatonic", MAJ_PENTA,  (uint8_t)(sizeof(MAJ_PENTA)/sizeof(MAJ_PENTA[0])) },
  { "Minor Pentatonic", MIN_PENTA,  (uint8_t)(sizeof(MIN_PENTA)/sizeof(MIN_PENTA[0])) },
  { "Major (Ionian)",   MAJOR,      (uint8_t)(sizeof(MAJOR)/sizeof(MAJOR[0])) },
  { "Natural Minor",    NAT_MINOR,  (uint8_t)(sizeof(NAT_MINOR)/sizeof(NAT_MINOR[0])) },
  { "Whole Tone",       WHOLE,      (uint8_t)(sizeof(WHOLE)/sizeof(WHOLE[0])) },
  { "Chromatic",        CHROMA,     (uint8_t)(sizeof(CHROMA)/sizeof(CHROMA[0])) }
};
const uint8_t NUM_SCALES = sizeof(SCALES)/sizeof(SCALES[0]);
#define MAX_SCALE_SIZE 32
float SCALE_HZ[MAX_SCALE_SIZE];
uint8_t SCALE_LEN = 0;
uint8_t scaleIndex = 0;

// ---------- Touch smoothing & thresholds ----------
const int   TOUCH_GATE    = 8;     // works well for your ~45 delta
const int   TOUCH_RANGE   = 48;    // ~your delta
const float EMA_ALPHA     = 0.18f;
const uint32_t CONTROL_DT_MS = 20;

// ---------- Vibrato (pressure-controlled) ----------
const float VIB_RATE_HZ         = 3.5f;
const float VIB_DEPTH_MIN_SEMI  = 0.05f;  // feather touch
const float VIB_DEPTH_MAX_SEMI  = 0.35f;  // firm press

// ---------- Envelopes ----------
const float AMP_ATTACK   = 0.01f;
const float AMP_RELEASE  = 0.008f;
const float AMP_FLOOR    = 0.08f;  // avoids clicks

// ---------- Idle mode ----------
const uint32_t IDLE_TIMEOUT_MS     = 60000; // 60 s
const uint32_t IDLE_PATTERN_DUR_MS = 10000; // 10 s
const float IDLE_MIN_HZ   = 140.0f;
const float IDLE_MAX_HZ   = 720.0f;
const float IDLE_SWEEP_RT = 0.05f;

// ---------- Gestures ----------
const uint32_t SCALE_HOLD_MS = 1500; // both pads
const uint32_t LOCK_HOLD_MS  = 1000; // per-side lock

// ---------- State ----------
static int baselineL=-1, baselineR=-1;
static float smoothDL=0.0f, smoothDR=0.0f;
static float ampL=0.0f, ampR=0.0f;
static float phaseL=0.0f, phaseR=0.0f;
static float vibPhaseL=0.0f, vibPhaseR=0.0f;
static float freqL=0.0f, freqR=0.0f;
static uint32_t lastInputMs=0, patternStartMs=0, lastControlMs=0;
static int idlePattern=0;

static bool lockedL=false, lockedR=false;
static float lockedFreqL=0.0f, lockedFreqR=0.0f;
static int lastNoteIdxL=-1, lastNoteIdxR=-1;
static uint32_t holdStartL=0, holdStartR=0;
static bool holdingL=false, holdingR=false;

static bool bothTouched=false, scaleJustSwitched=false;
static uint32_t bothTouchedSince=0;

// adaptive peak for pressure mapping
static float dL_peak = 20, dR_peak = 20;

static inline float clampf(float v,float a,float b){ return (v<a)?a:((v>b)?b:v); }
static inline float semiRatio(float s){ return powf(2.0f, s/12.0f); }

void buildScaleHz(){
  ScaleDef &S = SCALES[scaleIndex];
  SCALE_LEN = S.count;
  for (uint8_t i=0; i<S.count; ++i) SCALE_HZ[i] = BASE_HZ * powf(2.0f, S.steps[i]/12.0f);
  Serial.printf("[woof] scale: %s\n", S.name);
}

float mapDeltaToIndex(float smDelta){
  float dMin= (float)TOUCH_GATE, dMax = dMin + (float)TOUCH_RANGE;
  float x = (smDelta - dMin) / (dMax - dMin);
  x = clampf(x, 0.0f, 1.0f);
  float u = powf(x, 0.7f);
  int idx = (int)roundf(u*(SCALE_LEN-1));
  return (float)idx;
}

float idxToHz(int idx){ idx = (idx<0)?0:((idx>=SCALE_LEN)?(SCALE_LEN-1):idx); return SCALE_HZ[idx]; }

float mapPressureToVibDepth(float smDelta, float peak){
  // peak decays slowly; take ~95% of recent peak as “full press”
  float dMin = (float)TOUCH_GATE;
  float dMax = fmaxf(dMin + 20.0f, peak * 0.95f);
  float x = (smDelta - dMin) / (dMax - dMin);
  x = clampf(x, 0.0f, 1.0f);
  // gentle curve so it ramps smoothly
  x = powf(x, 0.8f);
  return VIB_DEPTH_MIN_SEMI + (VIB_DEPTH_MAX_SEMI - VIB_DEPTH_MIN_SEMI) * x;
}

void pickIdlePattern(){ idlePattern = esp_random() % 4; patternStartMs = millis(); }

void idleFreqs(float &a, float &b){
  float t = (millis() - patternStartMs)/1000.0f;
  float s1 = 0.5f + 0.5f * sinf(t * IDLE_SWEEP_RT * 2.0f * M_PI);
  float s2 = 0.5f + 0.5f * sinf(t * (IDLE_SWEEP_RT*0.77f) * 2.0f * M_PI + 0.9f);
  float f1 = IDLE_MIN_HZ + (IDLE_MAX_HZ - IDLE_MIN_HZ) * s1;
  float f2 = IDLE_MIN_HZ + (IDLE_MAX_HZ - IDLE_MIN_HZ) * s2;

  switch (idlePattern){
    case 0: a=f1; b=f1; break;
    case 1: a=f1; b=IDLE_MIN_HZ + (IDLE_MAX_HZ - (f1 - IDLE_MIN_HZ)); break;
    case 2: a=f1; b=f2; break;
    case 3: a=f1; b=((millis()/20000)%2)? f1 : f2; break;
  }
  if (millis() - patternStartMs > IDLE_PATTERN_DUR_MS) pickIdlePattern();
}

// ---------- I2S init ----------
// Pick one up top:
// const int SR = 22050;  // or 44100; 16000 also works on many boards


void audioInit(){
  i2s_config_t cfg = {
    .mode = (i2s_mode_t)(I2S_MODE_MASTER | I2S_MODE_TX),
    .sample_rate = SR,                               // use the same SR everywhere
    .bits_per_sample = I2S_BITS_PER_SAMPLE_16BIT,
    .channel_format = I2S_CHANNEL_FMT_RIGHT_LEFT,
#if defined(ESP_IDF_VERSION_MAJOR) && (ESP_IDF_VERSION_MAJOR >= 4)
    .communication_format = I2S_COMM_FORMAT_STAND_I2S,
#else
    .communication_format = (i2s_comm_format_t)(I2S_COMM_FORMAT_I2S),
#endif
    .intr_alloc_flags = 0,
    .dma_buf_count = DMA_COUNT,
    .dma_buf_len = BUF_SAMPLES,
    .use_apll = false,                               // try false first; flip to true if needed
    .tx_desc_auto_clear = true,
    .fixed_mclk = 0
  };

  ESP_ERROR_CHECK(i2s_driver_install(I2S_NUM_0, &cfg, 0, NULL));

  i2s_pin_config_t pins = {
    .mck_io_num   = I2S_PIN_NO_CHANGE,               // UDA1334A doesn't need MCLK from ESP32
    .bck_io_num   = I2S_BCLK,                        // 33
    .ws_io_num    = I2S_LRCK,                        // 32
    .data_out_num = I2S_DATA,                        // 23
    .data_in_num  = I2S_PIN_NO_CHANGE
  };
  ESP_ERROR_CHECK(i2s_set_pin(I2S_NUM_0, &pins));

  // Set clocks with the same SR used in your synth math
  ESP_ERROR_CHECK(i2s_set_sample_rates(I2S_NUM_0, SR));
  ESP_ERROR_CHECK(i2s_set_clk(I2S_NUM_0, SR, I2S_BITS_PER_SAMPLE_16BIT, I2S_CHANNEL_STEREO));

  i2s_zero_dma_buffer(I2S_NUM_0);
  ESP_ERROR_CHECK(i2s_start(I2S_NUM_0));
}



// ---------- control update (every ~20 ms, no delays) ----------
void controlUpdate(){
  uint32_t now = millis();

  int rawL = touchRead(TOUCH_L_GPIO);
  int rawR = touchRead(TOUCH_R_GPIO);

  if (baselineL < 0) baselineL = rawL;
  if (baselineR < 0) baselineR = rawR;
  baselineL = (int)(0.998f*baselineL + 0.002f*rawL);
  baselineR = (int)(0.998f*baselineR + 0.002f*rawR);

  int dL = baselineL - rawL;
  int dR = baselineR - rawR;

  // update adaptive peaks (decay then catch)
  dL_peak = fmaxf(0.98f*dL_peak, fminf((float)dL, 200.0f));
  dR_peak = fmaxf(0.98f*dR_peak, fminf((float)dR, 200.0f));

  // EMA smoothing
  smoothDL = (1.0f-EMA_ALPHA)*smoothDL + EMA_ALPHA*max(0, dL);
  smoothDR = (1.0f-EMA_ALPHA)*smoothDR + EMA_ALPHA*max(0, dR);

  bool touchedL = (smoothDL > TOUCH_GATE);
  bool touchedR = (smoothDR > TOUCH_GATE);

  // --- scale switch (both held) ---
  if (touchedL && touchedR) {
    if (!bothTouched) { bothTouched=true; bothTouchedSince=now; }
    if (bothTouched && (now - bothTouchedSince > SCALE_HOLD_MS) && !scaleJustSwitched) {
      scaleIndex = (scaleIndex + 1) % NUM_SCALES;
      buildScaleHz();
      scaleJustSwitched = true;
      // short confirmation: base note both sides
      freqL = BASE_HZ; freqR = BASE_HZ;
      lastInputMs = now;
    }
  } else { bothTouched=false; scaleJustSwitched=false; }

  // --- per-side lock hold detect (only if NOT doing the both-pads gesture) ---
  if (!(touchedL && touchedR)) {
    // LEFT
    if (touchedL) {
      if (!holdingL) { holdingL=true; holdStartL=now; }
      if (holdingL && (now - holdStartL > LOCK_HOLD_MS)) {
        lockedL = !lockedL;
        if (lockedL) {
          // lock current note
          int idx = (int)roundf(mapDeltaToIndex(smoothDL));
          lockedFreqL = idxToHz(idx);
          lastNoteIdxL = idx;
        } else {
          lockedFreqL = 0.0f;
          lastNoteIdxL = -1;
        }
        // confirmation chirp on that side
        lastInputMs = now;
        holdingL=false; // consume this hold
      }
    } else {
      holdingL=false;
    }
    // RIGHT
    if (touchedR) {
      if (!holdingR) { holdingR=true; holdStartR=now; }
      if (holdingR && (now - holdStartR > LOCK_HOLD_MS)) {
        lockedR = !lockedR;
        if (lockedR) {
          int idx = (int)roundf(mapDeltaToIndex(smoothDR));
          lockedFreqR = idxToHz(idx);
          lastNoteIdxR = idx;
        } else {
          lockedFreqR = 0.0f;
          lastNoteIdxR = -1;
        }
        lastInputMs = now;
        holdingR=false;
      }
    } else {
      holdingR=false;
    }
  }

  // --- set target freqs ---
  if (!lockedL && touchedL) {
    int idxL = (int)roundf(mapDeltaToIndex(smoothDL));
    // gentle “snap” when staying on same index
    lastNoteIdxL = idxL;
    freqL = idxToHz(idxL);
    lastInputMs = now;
  } else if (lockedL) {
    freqL = lockedFreqL;
  } else {
    freqL = 0.0f;
  }

  if (!lockedR && touchedR) {
    int idxR = (int)roundf(mapDeltaToIndex(smoothDR));
    lastNoteIdxR = idxR;
    freqR = idxToHz(idxR);
    lastInputMs = now;
  } else if (lockedR) {
    freqR = lockedFreqR;
  } else {
    freqR = 0.0f;
  }

  // no-idle if any lock is active
  if (!lockedL && !lockedR && !touchedL && !touchedR && (now - lastInputMs > IDLE_TIMEOUT_MS)) {
    idleFreqs(freqL, freqR);
  }
}

void audioTaskOnce(){
  const float TAU = 6.28318530718f;
  float vibInc = TAU * VIB_RATE_HZ / SR;

  int16_t buf[BUF_SAMPLES*2];

  for (size_t i=0;i<BUF_SAMPLES;i++){
    // pressure-controlled vibrato depth per side
    float vibDepthL = (freqL>0.0f)? mapPressureToVibDepth(smoothDL, dL_peak) : 0.0f;
    float vibDepthR = (freqR>0.0f)? mapPressureToVibDepth(smoothDR, dR_peak) : 0.0f;

    float tL = (freqL>0.0f || lockedL)? 1.0f : AMP_FLOOR;
    float tR = (freqR>0.0f || lockedR)? 1.0f : AMP_FLOOR;
    ampL += (tL-ampL) * (tL>ampL ? AMP_ATTACK : AMP_RELEASE);
    ampR += (tR-ampR) * (tR>ampR ? AMP_ATTACK : AMP_RELEASE);

    float rL = (freqL>0.0f || lockedL)? semiRatio(vibDepthL * sinf(vibPhaseL)) : 1.0f;
    float rR = (freqR>0.0f || lockedR)? semiRatio(vibDepthR * sinf(vibPhaseR)) : 1.0f;

    float dphiL = (freqL>0.0f || lockedL)? TAU*(freqL*rL)/SR : 0.0f;
    float dphiR = (freqR>0.0f || lockedR)? TAU*(freqR*rR)/SR : 0.0f;

    float sL = (freqL>0.0f || lockedL ? sinf(phaseL) : 0.0f) * (32767.0f*MASTER_VOL*ampL);
    float sR = (freqR>0.0f || lockedR ? sinf(phaseR) : 0.0f) * (32767.0f*MASTER_VOL*ampR);

// After computing sL/sR but before writing to buf:
    if (!(freqL>0.0f || lockedL)) {
  // ~ -70 dBTP triangular dither
   int32_t r = (int32_t)(esp_random() & 0xFFFF) - 32768;
    sL = (float)(r >> 6);  // small value to avoid DAC hard-mute
}
    if (!(freqR>0.0f || lockedR)) {
    int32_t r = (int32_t)(esp_random() & 0xFFFF) - 32768;
    sR = (float)(r >> 6);
}


    buf[2*i+0] = (int16_t)clampf(sL, -32767.f, 32767.f);
    buf[2*i+1] = (int16_t)clampf(sR, -32767.f, 32767.f);

    phaseL += dphiL; if (phaseL > TAU) phaseL -= TAU;
    phaseR += dphiR; if (phaseR > TAU) phaseR -= TAU;
    vibPhaseL += vibInc; if (vibPhaseL > TAU) vibPhaseL -= TAU;
    vibPhaseR += vibInc; if (vibPhaseR > TAU) vibPhaseR -= TAU;
  }

  size_t w;
  i2s_write(I2S_NUM_0, buf, sizeof(buf), &w, portMAX_DELAY);
}

void audioInit(); // fwd

void setup(){
  Serial.begin(115200);
  audioInit();
  buildScaleHz();
  lastInputMs = lastControlMs = patternStartMs = millis();
  pickIdlePattern();
}

void loop(){
  uint32_t now = millis();
  if (now - lastControlMs >= CONTROL_DT_MS) { lastControlMs = now; controlUpdate(); }
  audioTaskOnce();

  // rotate idle pattern while idle (and not locked)
  if (!lockedL && !lockedR && freqL==0.0f && freqR==0.0f && (millis()-lastInputMs > IDLE_TIMEOUT_MS)) {
    if (millis() - patternStartMs > IDLE_PATTERN_DUR_MS) pickIdlePattern();
  }
}

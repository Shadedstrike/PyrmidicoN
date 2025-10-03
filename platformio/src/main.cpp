#include <Arduino.h>

// ESP32 (WROOM) + UDA1334A calm stereo synth
// Solid idle drone + scale browse + tune-by-ear + touch self-heal
//
// I2S (UDA1334A):  BCLK=GPIO26, LRCLK/WSEL=GPIO25, DIN=GPIO23
// Touch pads:      PLAY LEFT=GPIO27 (T7), PLAY RIGHT=GPIO14 (T6)
//                  TUNE UP=GPIO33 (T8),  TUNE DOWN=GPIO32 (T9)

#include <driver/i2s.h>
#include <math.h>
#include <esp_random.h>

// ====== Pins ======
#define I2S_BCLK   26
#define I2S_LRCK   25
#define I2S_DATA   23
#define SWAP_I2S_LR 0

#define TOUCH_PLAY_L   27  // T7
#define TOUCH_PLAY_R   14  // T6
#define TOUCH_TUNE_UP  33  // T8
#define TOUCH_TUNE_DN  32  // T9

// ====== Audio ======
const int   SR            = 22050;
const size_t BUF_SAMPLES  = 512;
const int   DMA_COUNT     = 16;
const float MASTER_VOL    = 0.85f;
const float GAIN_L        = 0.70f;
const float GAIN_R        = 0.70f;

// Envelope (play) and (idle)
const float AMP_ATTACK    = 0.010f;
const float AMP_RELEASE   = 0.008f;
const float IDLE_AMP_ATTACK  = 0.006f;
const float IDLE_AMP_RELEASE = 0.004f;
const float AMP_FLOOR_L   = 0.0f;
const float AMP_FLOOR_R   = 0.0f;

// Vibrato
const float VIB_DEPTH_SEMITONES = 0.12f;
const float VIB_RATE_HZ         = 3.2f;

// Keep-alive (click to prevent DAC mute when silent)
#define KEEPALIVE_ENABLE 1
const uint32_t KA_BURST_MS = 2;
const uint32_t KA_REP_MS   = 800;
const int      KA_SHIFT    = 11;

// ====== Musical scales (A = baseAHz) ======
static float baseAHz = 220.0f; // tune-by-ear moves this
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
static int8_t transpose = 0; // (not used by L/R; placeholder for future buttons)

// ====== Touch processing ======
const uint32_t CONTROL_DT_MS = 20;
const float EMA_ALPHA   = 0.16f;  // smooth the deltas

struct TP { int pin; float noise; bool touched; float smooth; uint32_t lastCross; uint32_t gateAboveSince; uint32_t gateBelowSince; };
TP tpL   = {TOUCH_PLAY_L,  0, false, 0, 0, 0, 0};
TP tpR   = {TOUCH_PLAY_R,  0, false, 0, 0, 0, 0};
TP tpUp  = {TOUCH_TUNE_UP, 0, false, 0, 0, 0, 0};
TP tpDn  = {TOUCH_TUNE_DN, 0, false, 0, 0, 0, 0};

const float NOISE_ALPHA = 0.02f;
const float ON_K  = 3.0f;
const float OFF_K = 1.5f;
const float EXTRA_BIAS_ON  = 2.0f;
const float EXTRA_BIAS_OFF = 1.0f;

const uint32_t TOUCH_ON_DEBOUNCE_MS  = 25;
const uint32_t TOUCH_OFF_DEBOUNCE_MS = 45;
const uint32_t TOUCH_GRACE_MS        = 500;
const uint32_t ACTIVE_HOLD_MS        = 1200;

// ====== Modes / gestures ======
enum UIMode { MODE_NORMAL=0, MODE_SCALE_BROWSE=1, MODE_TUNE=2 };
static UIMode uiMode = MODE_NORMAL;

const uint32_t BOTH_LR_HOLD_FOR_SCALE_MS = 10000;  // hold L+R 10s to browse
const uint32_t SCALE_BROWSE_STEP_MS      = 2000;   // step while held every 2s
static uint32_t bothLRSince = 0;
static uint32_t lastScaleBrowseStep = 0;

const uint32_t BOTH_TUNE_HOLD_MS = 3000;    // hold UP+DN 3s to enter TUNE
const uint32_t TUNE_IDLE_EXIT_MS = 5000;    // exit TUNE after 5s no taps
static uint32_t bothTuneSince = 0;
static uint32_t lastTuneTapMs = 0;

// ====== Idle organ ======
const uint32_t IDLE_TIMEOUT_MS = 30000;     // start idle after 30s
const float IDLE_NOTE_LENS[] = {5.0f, 7.0f, 9.0f, 12.0f};
const int   IDLE_NOTE_LENS_N = sizeof(IDLE_NOTE_LENS)/sizeof(IDLE_NOTE_LENS[0]);
const float IDLE_GAP_MIN_S = 0.8f, IDLE_GAP_MAX_S = 2.0f;
const float IDLE_MIN_HZ = 55.0f, IDLE_MAX_HZ = 220.0f;

static inline float clampIdleHz(float hz){ return fminf(IDLE_MAX_HZ, fmaxf(IDLE_MIN_HZ, hz)); }

// BaseA tuning bounds (independent of idle range)
const float BASEA_MIN_HZ = 55.0f;
const float BASEA_MAX_HZ = 880.0f;
static inline float clampBaseA(float hz){ return fminf(BASEA_MAX_HZ, fmaxf(BASEA_MIN_HZ, hz)); }

static uint32_t lastInputMs=0;

// idle sequencer
struct IdleNote { float freq=0.0f; uint32_t offMs=0; bool active=false; };
static IdleNote idleL={0,0,false}, idleR={0,0,false};
static uint32_t idleNextEventMs = 0;
static int idleIdx = 0;

static int baselineL=-1, baselineR=-1, baselineUp=-1, baselineDn=-1;
static float ampL=0, ampR=0, phaseL=0, phaseR=0, vibPhaseL=0, vibPhaseR=0;
static float freqL=0, freqR=0;         // targets
static float curFreqL=0, curFreqR=0;   // gliding oscillator freqs
const float FREQ_GLIDE_TAU_S = 0.040f;

static uint32_t lastControlMs=0, lastDbg=0;
static int i2s_consec_errors=0; static uint32_t lastGoodI2S=0;

// --- TUNE tap edge detection (raw) ---
static bool prevTapUp=false, prevTapDn=false;
const int RAW_TAP_THRESH = 6;   // try 4..10 depending on pad size

// --- touch self-heal ---
static uint32_t flatlineStartMs = 0;
static int prevRawL= -1, prevRawR= -1, prevRawUp= -1, prevRawDn= -1;
static int zeroStreak = 0;

// ---------- Utils ----------
static inline float clampf(float v,float a,float b){ return (v<a)?a:((v>b)?b:v); }
static inline float semiRatio(float s){ return powf(2.0f, s/12.0f); }
static inline float rand01(){ return (float)(esp_random() & 0xFFFFFF) / 16777216.0f; }
static inline int   randRange(int lo, int hi){ if (hi<lo){int t=lo;lo=hi;hi=t;} return lo + (int)(esp_random() % (uint32_t)(hi - lo + 1)); }
static inline float pickf(const float* arr, int n){ return arr[randRange(0, n-1)]; }
uint32_t secToMs(float s){ return (uint32_t)(s*1000.0f); }

void buildScaleHz(){
  ScaleDef &S = SCALES[scaleIndex];
  SCALE_LEN = S.count;
  float tr = semiRatio((float)transpose);
  for (uint8_t i=0; i<S.count; ++i) SCALE_HZ[i] = baseAHz * powf(2.0f, S.steps[i]/12.0f) * tr;
  Serial.printf("[scale] %s | transpose %+d st | baseA=%.2f Hz\n", S.name, (int)transpose, baseAHz);
}

float deltaToScaleHz(float smDelta){
  // map roughly 0..~50 → scale index, slightly ease-in
  float x = clampf(smDelta / 50.0f, 0.0f, 1.0f);
  float u = powf(x, 0.75f);
  int idx = (int)roundf(u*(SCALE_LEN-1));
  if (idx < 0) idx = 0; else if (idx >= (int)SCALE_LEN) idx = (int)SCALE_LEN-1;
  return SCALE_HZ[idx];
}

// ---------- Idle ----------
void idleResetSequencer(){
  idleL = IdleNote{}; idleR = IdleNote{};
  idleIdx = randRange(0, SCALE_LEN-1);
  idleNextEventMs = millis();
}
void idleUpdateSequencer(float &outL, float &outR){
  uint32_t now = millis();
  if (idleL.active && now >= idleL.offMs) idleL.active = false;
  if (idleR.active && now >= idleR.offMs) idleR.active = false;

  if (now >= idleNextEventMs){
    int jump = randRange(-1,+1);
    idleIdx += jump; if (idleIdx < 0) idleIdx = 0; if (idleIdx >= (int)SCALE_LEN) idleIdx = (int)SCALE_LEN-1;

    float baseHz = SCALE_HZ[idleIdx] * powf(2.0f, (float)randRange(-1,0)); // bias lower octave
    baseHz = clampIdleHz(baseHz);

    float durS = pickf(IDLE_NOTE_LENS, IDLE_NOTE_LENS_N);
    uint32_t durMs = secToMs(durS);

    bool chord = (rand01() < 0.25f);
    bool restL = (rand01() < 0.30f);
    bool restR = (rand01() < 0.30f);
    if (chord && restL && restR) restR = false;

    if (!restL){
      float hz = clampIdleHz(baseHz * semiRatio((rand01()*2.0f-1.0f)*0.03f));
      idleL = {hz, now+durMs, true};
    } else idleL.active=false;

    if (!restR){
      float hzR = baseHz;
      if (!chord){
        int n = idleIdx + randRange(-1,+1); if (n<0) n=0; if (n>=(int)SCALE_LEN) n=(int)SCALE_LEN-1;
        hzR = SCALE_HZ[n] * powf(2.0f,(float)randRange(-1,0));
      }
      hzR = clampIdleHz(hzR * semiRatio((rand01()*2.0f-1.0f)*0.03f));
      idleR = {hzR, now+durMs, true};
    } else idleR.active=false;

    uint32_t endL = idleL.active ? idleL.offMs : now;
    uint32_t endR = idleR.active ? idleR.offMs : now;
    uint32_t latestEnd = (endL > endR ? endL : endR);
    float gap = (float)randRange((int)(IDLE_GAP_MIN_S*10),(int)(IDLE_GAP_MAX_S*10))/10.0f;
    idleNextEventMs = latestEnd + secToMs(gap);
  }

  outL = idleL.active ? idleL.freq : 0.0f;
  outR = idleR.active ? idleR.freq : 0.0f;
}

// ---------- I2S ----------
void audioInit(){
  i2s_config_t cfg = {
    .mode = (i2s_mode_t)(I2S_MODE_MASTER | I2S_MODE_TX),
    .sample_rate = SR,
    .bits_per_sample = I2S_BITS_PER_SAMPLE_16BIT,
    .channel_format = I2S_CHANNEL_FMT_RIGHT_LEFT,
#if defined(ESP_IDF_VERSION_MAJOR) && (ESP_IDF_VERSION_MAJOR >= 4)
    .communication_format = I2S_COMM_FORMAT_STAND_I2S,
#else
    .communication_format = (i2s_comm_format_t)I2S_COMM_FORMAT_I2S,
#endif
    .intr_alloc_flags = 0,
    .dma_buf_count = DMA_COUNT,
    .dma_buf_len = BUF_SAMPLES,
    .use_apll = true,
    .tx_desc_auto_clear = true,
    .fixed_mclk = 0
  };
  i2s_driver_install(I2S_NUM_0, &cfg, 0, NULL);

  i2s_pin_config_t pins = {
    .mck_io_num   = I2S_PIN_NO_CHANGE,
    .bck_io_num   = I2S_BCLK,
    .ws_io_num    = I2S_LRCK,
    .data_out_num = I2S_DATA,
    .data_in_num  = I2S_PIN_NO_CHANGE
  };
  i2s_set_pin(I2S_NUM_0, &pins);
}

// ---------- Touch ----------
int readTouchRaw(int pin){
  return touchRead(pin);
}

void touchRecalibrate(){
  Serial.println("[touch] Recalibrating baselines...");
  int n=32; float avgL=0, avgR=0, avgUp=0, avgDn=0;
  for (int i=0; i<n; ++i){
    avgL += readTouchRaw(tpL.pin); avgR += readTouchRaw(tpR.pin);
    avgUp += readTouchRaw(tpUp.pin); avgDn += readTouchRaw(tpDn.pin);
    delay(5);
  }
  baselineL = (int)roundf(avgL/n); baselineR = (int)roundf(avgR/n);
  baselineUp = (int)roundf(avgUp/n); baselineDn = (int)roundf(avgDn/n);
  Serial.printf("[touch] Baselines: L=%d R=%d Up=%d Dn=%d\n", baselineL, baselineR, baselineUp, baselineDn);
}

void updateOneTP(TP &tp, int raw, int baseline){
  float delta = (float)(baseline - raw);
  if (delta < 0) delta = 0;

  tp.smooth = EMA_ALPHA*delta + (1.0f-EMA_ALPHA)*tp.smooth;

  tp.noise = NOISE_ALPHA*fabsf(delta-tp.smooth) + (1.0f-NOISE_ALPHA)*tp.noise;
  if (tp.noise < 1.0f) tp.noise = 1.0f;

  float onThresh  = ON_K*tp.noise + EXTRA_BIAS_ON;
  float offThresh = OFF_K*tp.noise + EXTRA_BIAS_OFF;

  uint32_t now = millis();
  if (tp.smooth > onThresh){
    if (tp.gateAboveSince == 0) tp.gateAboveSince = now;
    if (now - tp.gateAboveSince > TOUCH_ON_DEBOUNCE_MS) tp.touched = true;
    tp.gateBelowSince = 0;
  } else if (tp.smooth < offThresh){
    if (tp.gateBelowSince == 0) tp.gateBelowSince = now;
    if (now - tp.gateBelowSince > TOUCH_OFF_DEBOUNCE_MS) tp.touched = false;
    tp.gateAboveSince = 0;
  }
}

void controlUpdate(){
  uint32_t now = millis();

  int rawL = readTouchRaw(tpL.pin);
  int rawR = readTouchRaw(tpR.pin);
  int rawUp = readTouchRaw(tpUp.pin);
  int rawDn = readTouchRaw(tpDn.pin);

  // --- self-heal: if all sensors flatline for a while, recalibrate ---
  if (rawL == prevRawL && rawR == prevRawR && rawUp == prevRawUp && rawDn == prevRawDn){
    if (flatlineStartMs == 0) flatlineStartMs = now;
    else if (now - flatlineStartMs > 5000) {
      touchRecalibrate();
      flatlineStartMs = 0;
    }
  } else flatlineStartMs = 0;
  prevRawL=rawL; prevRawR=rawR; prevRawUp=rawUp; prevRawDn=rawDn;

  // --- self-heal: if all sensors read zero for a while, recalibrate ---
  if (rawL==0 && rawR==0 && rawUp==0 && rawDn==0) zeroStreak++; else zeroStreak=0;
  if (zeroStreak > 200) { touchRecalibrate(); zeroStreak=0; }

  updateOneTP(tpL, rawL, baselineL);
  updateOneTP(tpR, rawR, baselineR);
  updateOneTP(tpUp, rawUp, baselineUp);
  updateOneTP(tpDn, rawDn, baselineDn);

  bool anyTouched = (tpL.touched || tpR.touched || tpUp.touched || tpDn.touched);
  if (anyTouched) lastInputMs = now;

  // --- Gestures ---
  if (tpL.touched && tpR.touched){
    if (bothLRSince == 0) bothLRSince = now;
  } else bothLRSince = 0;

  if (tpUp.touched && tpDn.touched){
    if (bothTuneSince == 0) bothTuneSince = now;
  } else bothTuneSince = 0;

  // --- Mode switching ---
  if (uiMode == MODE_NORMAL){
    if (bothLRSince > 0 && (now - bothLRSince > BOTH_LR_HOLD_FOR_SCALE_MS)){
      uiMode = MODE_SCALE_BROWSE;
      Serial.println(">> Enter SCALE BROWSE mode");
      lastScaleBrowseStep = now;
      bothLRSince = 0; // consume
    }
    else if (bothTuneSince > 0 && (now - bothTuneSince > BOTH_TUNE_HOLD_MS)){
      uiMode = MODE_TUNE;
      Serial.println(">> Enter TUNE mode");
      lastTuneTapMs = now;
      bothTuneSince = 0; // consume
    }
  }
  else if (uiMode == MODE_SCALE_BROWSE){
    if (!tpL.touched && !tpR.touched){
      uiMode = MODE_NORMAL;
      Serial.println("<< Exit SCALE BROWSE mode");
    } else {
      if (now - lastScaleBrowseStep > SCALE_BROWSE_STEP_MS){
        scaleIndex = (scaleIndex + 1) % NUM_SCALES;
        buildScaleHz();
        lastScaleBrowseStep = now;
      }
    }
  }
  else if (uiMode == MODE_TUNE){
    if (now - lastTuneTapMs > TUNE_IDLE_EXIT_MS){
      uiMode = MODE_NORMAL;
      Serial.println("<< Exit TUNE mode (idle timeout)");
    }
  }

  // --- Actions ---
  if (uiMode == MODE_NORMAL){
    freqL = tpL.touched ? deltaToScaleHz(tpL.smooth) : 0.0f;
    freqR = tpR.touched ? deltaToScaleHz(tpR.smooth) : 0.0f;

    // if idle, use idle organ
    if (now - lastInputMs > IDLE_TIMEOUT_MS){
      float idleHzL=0, idleHzR=0;
      idleUpdateSequencer(idleHzL, idleHzR);
      freqL = idleHzL; freqR = idleHzR;
    } else {
      idleResetSequencer();
    }
  }
  else if (uiMode == MODE_TUNE){
    // tap detection on raw deltas
    bool tapUp = (baselineUp - rawUp) > RAW_TAP_THRESH;
    bool tapDn = (baselineDn - rawDn) > RAW_TAP_THRESH;
    bool edgeUp = (tapUp && !prevTapUp);
    bool edgeDn = (tapDn && !prevTapDn);

    if (edgeUp) { baseAHz = clampBaseA(baseAHz * semiRatio(+1.0f)); buildScaleHz(); lastTuneTapMs = now; }
    if (edgeDn) { baseAHz = clampBaseA(baseAHz * semiRatio(-1.0f)); buildScaleHz(); lastTuneTapMs = now; }
    prevTapUp = tapUp; prevTapDn = tapDn;
    freqL = 0; freqR = 0; // no sound in tune mode
  }
  else { // scale browse
    freqL = 0; freqR = 0;
  }
}

// ---------- Arduino setup/loop ----------
void setup(){
  Serial.begin(115200);
  Serial.println("\n-- ESP32 Synth --");
  audioInit();
  touchRecalibrate();
  buildScaleHz();
  idleResetSequencer();
  lastInputMs = millis();
}

void loop(){
  uint32_t now = millis();

  if (now - lastControlMs >= CONTROL_DT_MS){
    controlUpdate();
    lastControlMs = now;
  }

  // --- Audio generation ---
  int16_t buf[BUF_SAMPLES * 2];
  size_t bytes_written = 0;

  float dt = 1.0f / (float)SR;
  float glide_k = 1.0f - expf(-dt * 2.0f * M_PI * (1.0f/FREQ_GLIDE_TAU_S));

  for (int i=0; i<BUF_SAMPLES; ++i){
    // glide freqs
    curFreqL += (freqL - curFreqL) * glide_k;
    curFreqR += (freqR - curFreqR) * glide_k;

    // update amps
    float targetAmpL = (freqL > 0) ? GAIN_L : AMP_FLOOR_L;
    float targetAmpR = (freqR > 0) ? GAIN_R : AMP_FLOOR_R;
    bool isIdle = (now - lastInputMs > IDLE_TIMEOUT_MS);
    float attack = isIdle ? IDLE_AMP_ATTACK : AMP_ATTACK;
    float release = isIdle ? IDLE_AMP_RELEASE : AMP_RELEASE;

    if (ampL < targetAmpL) ampL += attack; else ampL -= release;
    if (ampR < targetAmpR) ampR += attack; else ampR -= release;
    ampL = clampf(ampL, AMP_FLOOR_L, GAIN_L);
    ampR = clampf(ampR, AMP_FLOOR_R, GAIN_R);

    // vibrato
    float vibL = 1.0f + VIB_DEPTH_SEMITONES * sinf(vibPhaseL);
    float vibR = 1.0f + VIB_DEPTH_SEMITONES * sinf(vibPhaseR);
    vibPhaseL += 2.0f * M_PI * VIB_RATE_HZ * dt; if (vibPhaseL > 2.0f*M_PI) vibPhaseL -= 2.0f*M_PI;
    vibPhaseR += 2.0f * M_PI * VIB_RATE_HZ * dt * 1.03f; if (vibPhaseR > 2.0f*M_PI) vibPhaseR -= 2.0f*M_PI;

    // sine osc
    float smpL = sinf(phaseL) * ampL;
    float smpR = sinf(phaseR) * ampR;
    phaseL += 2.0f * M_PI * curFreqL * vibL * dt; if (phaseL > 2.0f*M_PI) phaseL -= 2.0f*M_PI;
    phaseR += 2.0f * M_PI * curFreqR * vibR * dt; if (phaseR > 2.0f*M_PI) phaseR -= 2.0f*M_PI;

    int16_t sL = (int16_t)(smpL * 32767.0f * MASTER_VOL);
    int16_t sR = (int16_t)(smpR * 32767.0f * MASTER_VOL);

    #if SWAP_I2S_LR
      buf[i*2+0] = sR; buf[i*2+1] = sL;
    #else
      buf[i*2+0] = sL; buf[i*2+1] = sR;
    #endif
  }

  // --- Keep-alive click ---
  #if KEEPALIVE_ENABLE
  if (ampL < 0.01f && ampR < 0.01f && (now % KA_REP_MS < KA_BURST_MS)){
    for (int i=0; i<BUF_SAMPLES; ++i) { buf[i*2] += (i%2==0?1:-1) << KA_SHIFT; }
  }
  #endif

  esp_err_t res = i2s_write(I2S_NUM_0, buf, sizeof(buf), &bytes_written, portMAX_DELAY);
  if (res != ESP_OK) {
    i2s_consec_errors++;
    if (i2s_consec_errors > 100 && (now - lastGoodI2S > 1000)){
      Serial.printf("I2S error %d, consecutive=%d\n", res, i2s_consec_errors);
    }
  } else {
    i2s_consec_errors = 0;
    lastGoodI2S = now;
  }

  if (now - lastDbg > 1000){
    //Serial.printf("L sm=%.1f n=%.1f | R sm=%.1f n=%.1f | Up sm=%.1f n=%.1f | Dn sm=%.1f n=%.1f\n", tpL.smooth, tpL.noise, tpR.smooth, tpR.noise, tpUp.smooth, tpUp.noise, tpDn.smooth, tpDn.noise);
    //Serial.printf("L=%d R=%d Up=%d Dn=%d\n", tpL.touched, tpR.touched, tpUp.touched, tpDn.touched);
    //Serial.printf("freqL=%.1f, freqR=%.1f\n", freqL, freqR);
    lastDbg = now;
  }
}
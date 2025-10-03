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
#define SWAP_I2S_LR 0  // set to 1 if self-test sounds swapped

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
  i2s_set_sample_rates(I2S_NUM_0, SR);
  i2s_set_clk(I2S_NUM_0, SR, I2S_BITS_PER_SAMPLE_16BIT, I2S_CHANNEL_STEREO);
  i2s_zero_dma_buffer(I2S_NUM_0);
  i2s_start(I2S_NUM_0);
  lastGoodI2S = millis();
}

// ---------- Stereo self-test (Left then Right) ----------
void stereoSelfTest() {
  const float TAU = 6.28318530718f;
  const int16_t A = 4000;  // test amplitude
  int16_t buf[BUF_SAMPLES*2];

  auto play = [&](float fL, float fR, uint32_t ms) {
    uint32_t start = millis();
    float phL = 0.0f, phR = 0.0f;
    while (millis() - start < ms) {
      for (size_t i = 0; i < BUF_SAMPLES; ++i) {
        int16_t sL = (fL > 0) ? (int16_t)(A * sinf(phL)) : 0;
        int16_t sR = (fR > 0) ? (int16_t)(A * sinf(phR)) : 0;

        // Your stream format is I2S_CHANNEL_FMT_RIGHT_LEFT.
        // Default branch writes R then L. Flip with SWAP_I2S_LR if needed.
        #if SWAP_I2S_LR
          buf[2*i + 0] = sL;  // Left first
          buf[2*i + 1] = sR;  // Right second
        #else
          buf[2*i + 0] = sR;  // Right first
          buf[2*i + 1] = sL;  // Left second
        #endif

        phL += TAU * fL / SR; if (phL > TAU) phL -= TAU;
        phR += TAU * fR / SR; if (phR > TAU) phR -= TAU;
      }
      size_t w;
      i2s_write(I2S_NUM_0, buf, sizeof(buf), &w, pdMS_TO_TICKS(50));
    }
  };

  // 1s Left only @ 440 Hz, then 1s Right only @ 660 Hz
  play(440.0f, 0.0f, 1000);
  play(0.0f, 660.0f, 1000);
}

// ---------- Touch helpers ----------
int readTouchRaw(int pin){ return touchRead(pin); }

void touchRecalibrate(){
  baselineL = touchRead(TOUCH_PLAY_L);
  baselineR = touchRead(TOUCH_PLAY_R);
  baselineUp= touchRead(TOUCH_TUNE_UP);
  baselineDn= touchRead(TOUCH_TUNE_DN);

  tpL = {TOUCH_PLAY_L,  1, false, 0, 0, 0, 0};
  tpR = {TOUCH_PLAY_R,  1, false, 0, 0, 0, 0};
  tpUp= {TOUCH_TUNE_UP, 1, false, 0, 0, 0, 0};
  tpDn= {TOUCH_TUNE_DN, 1, false, 0, 0, 0, 0};

  bothLRSince = 0; lastScaleBrowseStep = 0;
  bothTuneSince = 0; lastTuneTapMs = 0;
  prevTapUp = prevTapDn = false;

  Serial.printf("[touch] Recalibrate baselines L:%d R:%d Up:%d Dn:%d\n",
                baselineL, baselineR, baselineUp, baselineDn);
}

void updateOneTP(TP& t, int baseline, int raw, uint32_t now, uint32_t &activeStamp){
  int d = baseline - raw; if (d < 0) d = -d;              // <<< magnitude-based
  t.smooth = (1.0f-EMA_ALPHA)*t.smooth + EMA_ALPHA*(float)d;
  if (!t.touched) t.noise = (1.0f-NOISE_ALPHA)*t.noise + NOISE_ALPHA*(float)d;

  float gateOn  = t.noise * ON_K  + EXTRA_BIAS_ON;
  float gateOff = t.noise * OFF_K + EXTRA_BIAS_OFF;

  if (!t.touched){
    if (t.smooth > gateOn){
      if (!t.gateAboveSince) t.gateAboveSince = now;
      if (now - t.gateAboveSince >= TOUCH_ON_DEBOUNCE_MS){
        t.touched = true; t.lastCross = now; t.gateAboveSince = 0;
      }
    } else t.gateAboveSince = 0;
  } else {
    bool wantOff = (t.smooth <= gateOff) && (now - t.lastCross > TOUCH_GRACE_MS) && (now - activeStamp > ACTIVE_HOLD_MS);
    if (wantOff){
      if (!t.gateBelowSince) t.gateBelowSince = now;
      if (now - t.gateBelowSince >= TOUCH_OFF_DEBOUNCE_MS){
        t.touched = false; t.gateBelowSince=0;
      }
    } else t.gateBelowSince = 0;
  }
}

// ---------- Control ----------
void controlUpdate(){
  uint32_t now = millis();

  // RAW reads
  int rawL  = readTouchRaw(TOUCH_PLAY_L);
  int rawR  = readTouchRaw(TOUCH_PLAY_R);
  int rawUp = readTouchRaw(TOUCH_TUNE_UP);
  int rawDn = readTouchRaw(TOUCH_TUNE_DN);

  if (baselineL<0){
    baselineL=rawL; baselineR=rawR; baselineUp=rawUp; baselineDn=rawDn;
  }

  // --- self-heal: detect zeros and flatline ---
  bool allZero = (rawL==0 && rawR==0 && rawUp==0 && rawDn==0);
  if (allZero) {
    if (++zeroStreak >= 3) {
      Serial.println("[touch] zero-streak -> recal");
      touchRecalibrate();
      zeroStreak = 0;
      return;
    }
  } else {
    zeroStreak = 0;
  }

  bool noChangeAll =
    (prevRawL == rawL) && (prevRawR == rawR) &&
    (prevRawUp == rawUp) && (prevRawDn == rawDn);

  if (noChangeAll) {
    if (!flatlineStartMs) flatlineStartMs = now;
    bool noActivity = (tpL.smooth<1.0f && tpR.smooth<1.0f && tpUp.smooth<1.0f && tpDn.smooth<1.0f) &&
                      (!tpL.touched && !tpR.touched && !tpUp.touched && !tpDn.touched);
    if (noActivity && (now - flatlineStartMs > 2000)) {
      Serial.println("[touch] flatline ~2s -> recal");
      touchRecalibrate();
      flatlineStartMs = 0;
      return;
    }
  } else {
    flatlineStartMs = 0;
  }
  prevRawL  = rawL;  prevRawR  = rawR;
  prevRawUp = rawUp; prevRawDn = rawDn;

  // NOW compute deltas for raw-edge taps (magnitude-based)
  int dUpRaw = baselineUp - rawUp; if (dUpRaw < 0) dUpRaw = -dUpRaw;
  int dDnRaw = baselineDn - rawDn; if (dDnRaw < 0) dDnRaw = -dDnRaw;

  // activity stamps (magnitude-based)
  static uint32_t lastActiveLms=0, lastActiveRms=0, lastActiveUpms=0, lastActiveDnms=0;
  if ((baselineL - rawL  > 2) || (rawL - baselineL  > 2)) lastActiveLms = now;
  if ((baselineR - rawR  > 2) || (rawR - baselineR  > 2)) lastActiveRms = now;
  if ((baselineUp - rawUp> 2) || (rawUp - baselineUp> 2)) lastActiveUpms= now;
  if ((baselineDn - rawDn> 2) || (rawDn - baselineDn> 2)) lastActiveDnms= now;

  // update smoothed states
  updateOneTP(tpL,  baselineL, rawL,  now, lastActiveLms);
  updateOneTP(tpR,  baselineR, rawR,  now, lastActiveRms);
  updateOneTP(tpUp, baselineUp,rawUp, now, lastActiveUpms);
  updateOneTP(tpDn, baselineDn,rawDn, now, lastActiveDnms);

  // Baseline creep when fully idle
  bool anyTouched = tpL.touched||tpR.touched||tpUp.touched||tpDn.touched;
  if (!anyTouched){
    const float k = 0.0015f;
    baselineL = (int)((1.0f-k)*baselineL + k*rawL);
    baselineR = (int)((1.0f-k)*baselineR + k*rawR);
    baselineUp= (int)((1.0f-k)*baselineUp+ k*rawUp);
    baselineDn= (int)((1.0f-k)*baselineDn+ k*rawDn);
  }

  // ========= Gestures =========
  // 1) Scale browse (disabled while in TUNE)
  if (uiMode != MODE_TUNE) {
    bool bothLR = tpL.touched && tpR.touched;
    if (bothLR) {
      if (!bothLRSince) bothLRSince = now;
      uint32_t held = now - bothLRSince;

      if (held >= BOTH_LR_HOLD_FOR_SCALE_MS) {
        if (uiMode != MODE_SCALE_BROWSE) {
          uiMode = MODE_SCALE_BROWSE;
          lastScaleBrowseStep = 0;
          Serial.println("[ui] SCALE_BROWSE");
        }
        if (lastScaleBrowseStep == 0 ||
            (now - lastScaleBrowseStep >= SCALE_BROWSE_STEP_MS)) {
          scaleIndex = (scaleIndex + 1) % NUM_SCALES;
          buildScaleHz();
          lastScaleBrowseStep = now;
        }
      }
    } else {
      if (uiMode == MODE_SCALE_BROWSE) {
        Serial.printf("[ui] Scale latched: %s\n", SCALES[scaleIndex].name);
      }
      uiMode = MODE_NORMAL;
      bothLRSince = 0;
      lastScaleBrowseStep = 0;
    }
  }

  // 2) Tune-by-ear: hold UP+DN 3s → steady tone; tap UP/DN to adjust ±1/4 semitone
  bool bothTune = tpUp.touched && tpDn.touched;
  if (bothTune) {
    if (!bothTuneSince) bothTuneSince = now;
    if (now - bothTuneSince >= BOTH_TUNE_HOLD_MS) {
      if (uiMode != MODE_TUNE) {
        uiMode = MODE_TUNE;
        lastTuneTapMs = now;                       // avoid instant auto-exit
        // seed raw-edge states so the first tap is clean (magnitude-based)
        int seedUp = baselineUp - readTouchRaw(TOUCH_TUNE_UP); if (seedUp < 0) seedUp = -seedUp;
        int seedDn = baselineDn - readTouchRaw(TOUCH_TUNE_DN); if (seedDn < 0) seedDn = -seedDn;
        prevTapUp = (seedUp > RAW_TAP_THRESH);
        prevTapDn = (seedDn > RAW_TAP_THRESH);
        Serial.printf("[ui] TUNE MODE (steady tone at %.2f Hz). Tap UP/DN to adjust; idle 5s to exit.\n", baseAHz);
      }
    }
  } else {
    bothTuneSince = 0;
  }

  // TUNE taps + steady hum
  if (uiMode == MODE_TUNE) {
    bool tapUpNow = (dUpRaw > RAW_TAP_THRESH);
    bool tapDnNow = (dDnRaw > RAW_TAP_THRESH);

    if (tapUpNow && !prevTapUp) {
      baseAHz = clampBaseA(baseAHz * semiRatio(+1.0f));  // +¼ semitone
      buildScaleHz();
      lastTuneTapMs = now;
      Serial.printf("[tune] +¼ semi → baseA=%.2f\n", baseAHz);
    }
    if (tapDnNow && !prevTapDn) {
      baseAHz = clampBaseA(baseAHz * semiRatio(-1.0f));  // −¼ semitone
      buildScaleHz();
      lastTuneTapMs = now;
      Serial.printf("[tune] −¼ semi → baseA=%.2f\n", baseAHz);
    }
    prevTapUp = tapUpNow;
    prevTapDn = tapDnNow;

    // steady hum while tuning
    freqL = freqR = baseAHz;
    lastInputMs = now;                         // keep idle suppressed
    idleNextEventMs = 0; idleL.active=false; idleR.active=false;

    // auto-exit after 5s of no taps
    if (now - lastTuneTapMs > TUNE_IDLE_EXIT_MS) {
      uiMode = MODE_NORMAL;
      Serial.printf("[ui] Exit TUNE (baseA=%.2f)\n", baseAHz);
    }
  }

  // ========= Set target freqs (normal / idle) =========
  if (uiMode != MODE_TUNE){
    if (tpL.touched || tpR.touched){
      lastInputMs = now;
      freqL = tpL.touched ? deltaToScaleHz(tpL.smooth) : 0.0f;
      freqR = tpR.touched ? deltaToScaleHz(tpR.smooth) : 0.0f;
      idleNextEventMs = 0; idleL.active=false; idleR.active=false;
    } else {
      if (now - lastInputMs > IDLE_TIMEOUT_MS){
        if (idleNextEventMs==0) idleResetSequencer();
        idleUpdateSequencer(freqL, freqR);
      } else {
        freqL = freqR = 0.0f; idleNextEventMs=0;
      }
    }
  }

  // ---- Debug ----
  if (now - lastDbg > 500){
    lastDbg = now;
    int dbgUp = baselineUp - rawUp; if (dbgUp < 0) dbgUp = -dbgUp;
    int dbgDn = baselineDn - rawDn; if (dbgDn < 0) dbgDn = -dbgDn;
    Serial.printf("[dbg] rawL:%d rawR:%d rawUp:%d rawDn:%d | baseL:%d baseR:%d baseUp:%d baseDn:%d\n",
                  rawL, rawR, rawUp, rawDn, baselineL, baselineR, baselineUp, baselineDn);
    Serial.printf("[dbg] L:%d R:%d Up:%d Dn:%d | smL=%.1f smR=%.1f smUp=%.1f smDn=%.1f | dUp=%d dDn=%d | fL=%.1f fR=%.1f | mode=%d\n",
      (int)tpL.touched,(int)tpR.touched,(int)tpUp.touched,(int)tpDn.touched,
      tpL.smooth,tpR.smooth,tpUp.smooth,tpDn.smooth, dbgUp, dbgDn, freqL,freqR,(int)uiMode);
  }
}

// ---------- Arduino ----------
void setup(){
  Serial.begin(115200);
  audioInit();
  buildScaleHz();
  stereoSelfTest();  // Left then Right
  lastInputMs = lastControlMs = millis();
}

void loop(){
  uint32_t now = millis();
  if (now - lastControlMs >= CONTROL_DT_MS){
    lastControlMs = now;
    controlUpdate();
  }

  // glide factors per block
  float blockTime = (float)BUF_SAMPLES / (float)SR;
  float a = expf(-blockTime / FREQ_GLIDE_TAU_S);
  float freqMixKeep = a, freqMixNew = 1.0f - a;

  // audio synth
  const float TAU = 6.28318530718f;
  float vibInc = TAU * VIB_RATE_HZ / SR;
  int16_t buf[BUF_SAMPLES*2];

  static bool wasSilent=false; static uint32_t silentSince=0, lastKABurst=0;

  bool silentTargets = (freqL==0.0f && freqR==0.0f);
  if (silentTargets && !wasSilent){ silentSince=now; lastKABurst=now; }
  wasSilent = silentTargets;

  bool injectKA=false;
#if KEEPALIVE_ENABLE
  if (silentTargets){
    if (now - silentSince < KA_BURST_MS) injectKA=true;
    else if (now - lastKABurst >= KA_REP_MS){ injectKA=true; lastKABurst=now; }
  }
#endif

  bool userPlaying = (uiMode==MODE_TUNE) || tpL.touched || tpR.touched;
  bool idlingTone  = (!userPlaying && (freqL>0.0f || freqR>0.0f));
  float atk = idlingTone ? IDLE_AMP_ATTACK : AMP_ATTACK;
  float rel = idlingTone ? IDLE_AMP_RELEASE : AMP_RELEASE;

  for (size_t i=0;i<BUF_SAMPLES;i++){
    // glide toward targets
    curFreqL = curFreqL*freqMixKeep + freqL*freqMixNew;
    curFreqR = curFreqR*freqMixKeep + freqR*freqMixNew;

    // amps track oscillator activity so they don't stick at zero
    float tL = (curFreqL>0.0f)? 1.0f : AMP_FLOOR_L;
    float tR = (curFreqR>0.0f)? 1.0f : AMP_FLOOR_R;
    ampL += (tL-ampL) * (tL>ampL ? atk : rel);
    ampR += (tR-ampR) * (tR>ampR ? atk : rel);

    float rL = (curFreqL>0.0f)? semiRatio(VIB_DEPTH_SEMITONES * sinf(vibPhaseL)) : 1.0f;
    float rR = (curFreqR>0.0f)? semiRatio(VIB_DEPTH_SEMITONES * sinf(vibPhaseR)) : 1.0f;

    float dphiL = (curFreqL>0.0f)? TAU*(curFreqL*rL)/SR : 0.0f;
    float dphiR = (curFreqR>0.0f)? TAU*(curFreqR*rR)/SR : 0.0f;

    float sL = (curFreqL>0.0f ? sinf(phaseL) : 0.0f) * (32767.0f*MASTER_VOL*GAIN_L*ampL);
    float sR = (curFreqR>0.0f ? sinf(phaseR) : 0.0f) * (32767.0f*MASTER_VOL*GAIN_R*ampR);

    if (injectKA && curFreqL<=0.0f) sL = (int16_t)((((int32_t)(esp_random()&0x7FFF))-16384) >> KA_SHIFT);
    if (injectKA && curFreqR<=0.0f) sR = (int16_t)((((int32_t)(esp_random()&0x7FFF))-16384) >> KA_SHIFT);

    // buffer order: respects I2S_CHANNEL_FMT_RIGHT_LEFT
    #if SWAP_I2S_LR
      buf[2*i+0] = (int16_t)clampf(sL, -32767.f, 32767.f);
      buf[2*i+1] = (int16_t)clampf(sR, -32767.f, 32767.f);
    #else
      buf[2*i+0] = (int16_t)clampf(sR, -32767.f, 32767.f);
      buf[2*i+1] = (int16_t)clampf(sL, -32767.f, 32767.f);
    #endif

    phaseL += dphiL; if (phaseL > TAU) phaseL -= TAU;
    phaseR += dphiR; if (phaseR > TAU) phaseR -= TAU;
    vibPhaseL += vibInc; if (vibPhaseL > TAU) vibPhaseL -= TAU;
    vibPhaseR += vibInc; if (vibPhaseR > TAU) vibPhaseR -= TAU;
  }

  size_t w=0;
  esp_err_t err = i2s_write(I2S_NUM_0, buf, sizeof(buf), &w, pdMS_TO_TICKS(50));
  if (err != ESP_OK || w == 0){
    if (++i2s_consec_errors >= 3 || (millis()-lastGoodI2S>1000)){
      i2s_consec_errors=0;
      Serial.println("[i2s] restart");
      i2s_stop(I2S_NUM_0); i2s_zero_dma_buffer(I2S_NUM_0); i2s_start(I2S_NUM_0);
      lastGoodI2S = millis();
    }
  } else { i2s_consec_errors=0; lastGoodI2S=millis(); }
}

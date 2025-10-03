// ESP32 (WROOM) + UDA1334A calm stereo synth
// Max-biased baselines; debounced raw-delta pitch pads;
// LEFT pitch pad (GPIO33) = DOWN (deeper), RIGHT pitch pad (GPIO32) = UP (higher);
// per-side live pitch nudging while holding that side; sticky offsets + reset gesture;
// 5s LEFT/RIGHT diag, half-length randomized jingle, smooth idle.
//
// I2S (UDA1334A):  BCLK=GPIO26, LRCLK/WSEL=GPIO25, DIN=GPIO23
// Touch pads:      PLAY LEFT=GPIO27 (T7), PLAY RIGHT=GPIO14 (T6)
//                  PITCH LEFT=GPIO33 (T8) -> DOWN
//                  PITCH RIGHT=GPIO32 (T9) -> UP

#include <driver/i2s.h>
#include <math.h>
#include <esp_random.h>

// ================== Pins & Options ==================
#define I2S_BCLK      26
#define I2S_LRCK      25
#define I2S_DATA      23

// If left/right sound swapped on your board, set this to 1.
#define SWAP_I2S_LR   0

#define ENABLE_DIAG_TONES   1   // 5s LEFT, 5s RIGHT on boot
#define ENABLE_BOOT_JINGLE  1   // short randomized jingle after diag
#define DIAG_TONE_MS        5000
#define HARD_MONO_TEST      0

// ================== Touch Pads ==================
#define TOUCH_PLAY_L   27  // T7
#define TOUCH_PLAY_R   14  // T6
#define TOUCH_PITCH_L  33  // T8  (LEFT physical pitch pad)  -> DOWN
#define TOUCH_PITCH_R  32  // T9  (RIGHT physical pitch pad) -> UP

// ================== Audio Core ==================
const int   SR            = 22050;
const size_t BUF_SAMPLES  = 512;
const int   DMA_COUNT     = 16;
const float MASTER_VOL    = 0.85f;
const float GAIN_L        = 0.70f;
const float GAIN_R        = 0.70f;

const float AMP_ATTACK    = 0.010f;
const float AMP_RELEASE   = 0.008f;

const float VIB_DEPTH_SEMITONES = 0.12f;
const float VIB_RATE_HZ         = 3.2f;

// ================== Scale / Tuning ==================
static float baseAHz = 220.0f;
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
float   SCALE_HZ[MAX_SCALE_SIZE];
uint8_t SCALE_LEN = 0;
uint8_t scaleIndex = 0;
static int8_t transpose = 0;

// ================== Touch processing ==================
const uint32_t CONTROL_DT_MS = 20;
const float EMA_ALPHA   = 0.16f;
const float NOISE_ALPHA = 0.02f;

// Adaptive gates (play pads)
const float ON_K  = 3.0f;
const float OFF_K = 1.5f;
const float EXTRA_BIAS_ON  = 2.0f;
const float EXTRA_BIAS_OFF = 1.0f;

// Absolute fallback thresholds (helps if one pad is “blind-ish”)
const int PLAY_ABS_ON  = 3;   // raw delta ≥3 → allow ON
const int PLAY_ABS_OFF = 1;   // raw delta ≤1 → allow OFF

const uint32_t TOUCH_ON_DEBOUNCE_MS  = 25;
const uint32_t TOUCH_OFF_DEBOUNCE_MS = 45;
const uint32_t TOUCH_GRACE_MS        = 500;
const uint32_t ACTIVE_HOLD_MS        = 1200;

// Baseline helpers
const int      BASE_FLOOR_MIN     = 8;
const int      BASE_FAST_DELTA    = 6;
const float    BASE_FAST_K        = 0.28f;
const float    BASE_BURNIN_K      = 0.45f;
const uint32_t BASE_BURNIN_MS     = 4000;

// Pitch pad debounced raw-delta (LEFT pad = DOWN, RIGHT pad = UP)
const int   PITCH_ON_DELTA   = 3;   // need ≥3 consistently to turn ON
const int   PITCH_OFF_DELTA  = 1;   // need ≤1 consistently to turn OFF
const int   PITCH_ON_CONSEC  = 2;   // 40ms
const int   PITCH_OFF_CONSEC = 4;   // 80ms
const uint32_t PITCH_STEP_MS = 160; // auto-repeat while combo held
const int   DEGREE_OFFSET_MIN = -24;
const int   DEGREE_OFFSET_MAX = +24;

// Strong press for TUNE
const int   TUNE_STRONG_DELTA = 4;

// ===== Types =====
struct TP {
  int pin; float noise; bool touched; float smooth;
  uint32_t lastCross; uint32_t gateAboveSince; uint32_t gateBelowSince;
  float prevSmooth; uint32_t lastOffMs;
};
TP tpL={TOUCH_PLAY_L,1,false,0,0,0,0,0,0}, tpR={TOUCH_PLAY_R,1,false,0,0,0,0,0,0};
TP tpPitchL={TOUCH_PITCH_L,1,false,0,0,0,0,0,0}, tpPitchR={TOUCH_PITCH_R,1,false,0,0,0,0,0,0};

static uint32_t lastActiveLms=0, lastActiveRms=0;

// Debounced pitch pad states
static bool pitchLeftOn=false, pitchRightOn=false; // left pad=DOWN, right pad=UP
static int  upOnCnt=0, upOffCnt=0, dnOnCnt=0, dnOffCnt=0;

// Per-side degree offsets (sticky)
static int8_t leftDegOff = 0, rightDegOff = 0;
// Combo auto-repeat timers
static bool prevComboL_Deeper=false, prevComboL_Higher=false, prevComboR_Deeper=false, prevComboR_Higher=false;
static uint32_t nextComboL_Deeper=0, nextComboL_Higher=0, nextComboR_Deeper=0, nextComboR_Higher=0;

// Per-side offset reset edge
static bool prevResetL=false, prevResetR=false;

// For TUNE tap edges
static bool prevPitchLeftOn=false, prevPitchRightOn=false;

// ================== Modes / Gestures ==================
enum UIMode { MODE_NORMAL=0, MODE_SCALE_BROWSE=1, MODE_TUNE=2 };
static UIMode uiMode = MODE_NORMAL;

const uint32_t BOTH_LR_HOLD_FOR_SCALE_MS = 7000;
const uint32_t SCALE_BROWSE_STEP_MS      = 2000;
static uint32_t bothLRSince=0, lastScaleBrowseStep=0;

const uint32_t BOTH_TUNE_HOLD_MS = 3000;
const uint32_t TUNE_IDLE_EXIT_MS = 5000;
static uint32_t bothTuneSince=0, lastTuneTapMs=0;

// ================== Idle (very gentle) ==================
const float IDLE_BREATH_RATE_HZ   = 0.05f;
const float IDLE_BREATH_MIN       = 0.28f, IDLE_BREATH_MAX = 1.00f;
static float idlePhase=0.0f;
static float idleGate=0.0f;

// ================== Synth State ==================
static int baselineL=-1, baselineR=-1, baselinePitchL=-1, baselinePitchR=-1;
static float freqL=0, freqR=0, curFreqL=0, curFreqR=0;
const float FREQ_GLIDE_TAU_S = 0.040f;

static uint32_t lastControlMs=0, lastDbg=0;
static int i2s_consec_errors=0; static uint32_t lastGoodI2S=0;

// --- diag & boot ---
static uint8_t diagStage=0; static uint32_t diagUntil=0;
static bool    bootActive=false, bootInGap=false, bootFinalHold=false, bootStarted=false;
static uint8_t bootIdx=0, bootCycle=0;
static uint32_t bootNextMs=0, bootHoldUntil=0;

// ================== Utils ==================
static inline float clampf(float v,float a,float b){ return (v<a)?a:((v>b)?b:v); }
static inline int   clampi(int v,int a,int b){ if (v<a) return a; if (v>b) return b; return v; }
static inline float semiRatio(float s){ return powf(2.0f, s/12.0f); }
static inline float rand01(){ return (float)(esp_random() & 0xFFFFFF) / 16777216.0f; }
static inline int   randRange(int lo, int hi){ if (hi<lo){int t=lo;lo=hi;hi=t;} return lo + (int)(esp_random() % (uint32_t)(hi - lo + 1)); }
static inline float smooth01(float x){ x = clampf(x,0.f,1.f); return x*x*(3.f-2.f*x); }
uint32_t secToMs(float s){ return (uint32_t)(s*1000.0f); }
static inline float i0_series(float x){ float y=x*x, y2=y*y, y3=y2*y; return 1.0f + 0.25f*y + (1.0f/64.0f)*y2 + (1.0f/2304.0f)*y3; }

// ===== High-quantile baseline sampler (ignore zeros, bias high) =====
static int highQuantileNonZeroBaseline(int pin, int lastBaseline){
  const int N=64;
  int buf[N]; int n=0;
  int vmin=100000, vmax=-1;
  for (int i=0;i<96 && n<N;i++){
    int v = touchRead(pin);
    if (v>0){ buf[n++]=v; if (v<vmin) vmin=v; if (v>vmax) vmax=v; }
    delay(2);
  }
  if (n==0) return (lastBaseline>0? lastBaseline : 20);
  for (int i=1;i<n;i++){
    int key=buf[i], j=i-1;
    while (j>=0 && buf[j]>key){ buf[j+1]=buf[j]; j--; }
    buf[j+1]=key;
  }
  int idx = (int)floorf(0.80f*(n-1));
  int q80 = buf[idx];
  if (q80 < vmax) q80 = vmax;
  if (q80 < BASE_FLOOR_MIN) q80 = BASE_FLOOR_MIN;
  if (lastBaseline>0 && q80 < lastBaseline) q80 = lastBaseline;
  return q80;
}

// ================== Boot Jingle (shorter) ==================
struct BootStep { int8_t lSemi; int8_t rSemi; uint16_t durMs; uint16_t gapMs; };
const BootStep BOOT_POOL[] = {
  {  0,  7, 220, 30 },  // A + E
  {  4,  0, 220, 30 },  // C# + A
  {  7,  4, 220, 30 },  // E + C#
  { 12,  7, 360,  0 },  // A(↑oct) + E
};
const uint8_t BOOT_POOL_LEN = sizeof(BOOT_POOL)/sizeof(BOOT_POOL[0]);

static BootStep bootSeq[BOOT_POOL_LEN];
static uint8_t  bootLen=0;
static float    bootTimeMul=1.0f;
static uint8_t  bootRepeat=1;
static uint32_t bootFinalHoldMs=0;
const float BOOT_GAIN = 0.80f;
const float BOOT_GLOBAL_SCALE = 0.50f;  // half-length jingle

static inline uint32_t scaled(uint16_t ms){ return (uint32_t)roundf(fmaxf(20.0f, ms * bootTimeMul * BOOT_GLOBAL_SCALE)); }
static void bootBuildRandom(){
  float frac = 0.25f + rand01()*(0.35f-0.25f);
  bootTimeMul = 3.0f * frac;
  uint8_t want = (uint8_t)clampf((float)ceilf(BOOT_POOL_LEN * frac), 2.0f, (float)BOOT_POOL_LEN);
  uint8_t idxs[BOOT_POOL_LEN]; for (uint8_t i=0;i<BOOT_POOL_LEN;i++) idxs[i]=i;
  for (int i=BOOT_POOL_LEN-1;i>0;--i){ int j=randRange(0,i); uint8_t t=idxs[i]; idxs[i]=idxs[j]; idxs[j]=t; }
  for (uint8_t i=0;i<want;i++) bootSeq[i]=BOOT_POOL[idxs[i]];
  bootLen = want;
  bootRepeat = (uint8_t)randRange(1,2);
  bootFinalHoldMs = (uint32_t)(4000 * frac * BOOT_GLOBAL_SCALE);
}
static inline void bootStart(){
  bootBuildRandom();
  bootActive = true; bootInGap=false; bootFinalHold=false; bootIdx=0; bootCycle=0;
  bootStarted = true;
  bootNextMs = millis() + scaled(BOOT_POOL[0].durMs);
  Serial.println("[boot] start");
}
static inline void bootStop(){ bootActive=false; bootInGap=false; bootFinalHold=false; Serial.println("[boot] stop"); }

// ================== Scale builder ==================
static void buildScaleHz(){
  ScaleDef &S = SCALES[scaleIndex];
  SCALE_LEN = S.count;
  float tr = semiRatio((float)transpose);
  for (uint8_t i=0;i<S.count;i++) SCALE_HZ[i] = baseAHz * powf(2.0f, S.steps[i]/12.0f) * tr;
  Serial.printf("[scale] %s | baseA=%.2f Hz\n", S.name, baseAHz);
}
static inline int   scaleIdxFromDelta(float smDelta){
  float x = clampf(smDelta/50.0f, 0.0f, 1.0f);
  float u = powf(x, 0.75f);
  int idx = (int)roundf(u*(SCALE_LEN-1));
  return clampi(idx, 0, (int)SCALE_LEN-1);
}
static inline float scaleHzAtIdx(int idx){ return SCALE_HZ[clampi(idx,0,(int)SCALE_LEN-1)]; }

// ================== I2S ==================
static void audioInit(){
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
  i2s_pin_config_t pins = { .mck_io_num=I2S_PIN_NO_CHANGE, .bck_io_num=I2S_BCLK, .ws_io_num=I2S_LRCK, .data_out_num=I2S_DATA, .data_in_num=I2S_PIN_NO_CHANGE };
  i2s_set_pin(I2S_NUM_0, &pins);
  i2s_set_sample_rates(I2S_NUM_0, SR);
  i2s_set_clk(I2S_NUM_0, SR, I2S_BITS_PER_SAMPLE_16BIT, I2S_CHANNEL_STEREO);
  i2s_zero_dma_buffer(I2S_NUM_0);
  i2s_start(I2S_NUM_0);
  lastGoodI2S = millis();
}

// ================== Touch helpers ==================
static void touchRecalibrate(){
  int oldL=baselineL, oldR=baselineR, oldPL=baselinePitchL, oldPR=baselinePitchR;

  baselineL  = highQuantileNonZeroBaseline(TOUCH_PLAY_L,  oldL);
  baselineR  = highQuantileNonZeroBaseline(TOUCH_PLAY_R,  oldR);
  baselinePitchL = highQuantileNonZeroBaseline(TOUCH_PITCH_L, oldPL);
  baselinePitchR = highQuantileNonZeroBaseline(TOUCH_PITCH_R, oldPR);

  if (baselineL<BASE_FLOOR_MIN) baselineL=BASE_FLOOR_MIN;
  if (baselineR<BASE_FLOOR_MIN) baselineR=BASE_FLOOR_MIN;
  if (baselinePitchL<BASE_FLOOR_MIN) baselinePitchL=BASE_FLOOR_MIN;
  if (baselinePitchR<BASE_FLOOR_MIN) baselinePitchR=BASE_FLOOR_MIN;

  tpL = TP{TOUCH_PLAY_L,1,false,0,0,0,0,0,0};
  tpR = TP{TOUCH_PLAY_R,1,false,0,0,0,0,0,0};
  tpPitchL= TP{TOUCH_PITCH_L,1,false,0,0,0,0,0,0};
  tpPitchR= TP{TOUCH_PITCH_R,1,false,0,0,0,0,0,0};

  bothLRSince=0; lastScaleBrowseStep=0; bothTuneSince=0; lastTuneTapMs=0;

  // reset debouncers (offsets stay sticky)
  upOnCnt=upOffCnt=dnOnCnt=dnOffCnt=0; pitchLeftOn=pitchRightOn=false;

  Serial.printf("[touch] Recal L:%d R:%d PL:%d PR:%d\n", baselineL,baselineR,baselinePitchL,baselinePitchR);
}

static void updatePlayTP(TP& t, int baseline, int raw, uint32_t now, uint32_t &activeStamp){
  int d = baseline - raw; if (d<0) d=0;
  t.smooth = (1.0f-EMA_ALPHA)*t.smooth + EMA_ALPHA*(float)d;
  if (!t.touched) t.noise = (1.0f-NOISE_ALPHA)*t.noise + NOISE_ALPHA*(float)d;

  float gateOn  = t.noise * ON_K  + EXTRA_BIAS_ON;
  float gateOff = t.noise * OFF_K + EXTRA_BIAS_OFF;

  // also consider absolute deltas
  int deltaNow = d;

  if (!t.touched){
    bool passAdaptive = (t.smooth > gateOn);
    bool passAbsolute = (deltaNow >= PLAY_ABS_ON);
    if (passAdaptive || passAbsolute){
      if (!t.gateAboveSince) t.gateAboveSince = now;
      if (now - t.gateAboveSince >= TOUCH_ON_DEBOUNCE_MS){
        t.touched = true; t.lastCross = now; t.gateAboveSince = 0;
      }
    } else t.gateAboveSince = 0;
  } else {
    bool wantOff = ((t.smooth <= gateOff) || (deltaNow <= PLAY_ABS_OFF)) &&
                   (now - t.lastCross > TOUCH_GRACE_MS) &&
                   (now - activeStamp > ACTIVE_HOLD_MS);
    if (wantOff){
      if (!t.gateBelowSince) t.gateBelowSince = now;
      if (now - t.gateBelowSince >= TOUCH_OFF_DEBOUNCE_MS){
        t.touched = false; t.gateBelowSince=0; t.lastOffMs=now;
      }
    } else t.gateBelowSince = 0;
  }
}

// ================== Control ==================
static void controlUpdate(){
  static uint32_t firstOkBaselineMs = 0;
  uint32_t now=millis();

  // RAW reads
  int rawL  = touchRead(TOUCH_PLAY_L);
  int rawR  = touchRead(TOUCH_PLAY_R);
  int rawPL = touchRead(TOUCH_PITCH_L);
  int rawPR = touchRead(TOUCH_PITCH_R);

  // First run: seed baselines
  if (baselineL<0 || baselineR<0 || baselinePitchL<0 || baselinePitchR<0){
    touchRecalibrate();
    firstOkBaselineMs = millis();
    return;
  }

  // Zero-guard
  if (rawL==0)  rawL  = baselineL;
  if (rawR==0)  rawR  = baselineR;
  if (rawPL==0) rawPL = baselinePitchL;
  if (rawPR==0) rawPR = baselinePitchR;

  // Quick baseline catch-up (only upward)
  auto baselineQuickCatch=[&](int &b, int raw){
    if (raw>b){
      float k = (millis() - firstOkBaselineMs < BASE_BURNIN_MS) ? BASE_BURNIN_K : BASE_FAST_K;
      int d = raw-b; if (d>BASE_FAST_DELTA) b = (int)roundf(b + k*d);
    }
    if (b<BASE_FLOOR_MIN) b=BASE_FLOOR_MIN;
  };
  baselineQuickCatch(baselineL, rawL);
  baselineQuickCatch(baselineR, rawR);
  baselineQuickCatch(baselinePitchL, rawPL);
  baselineQuickCatch(baselinePitchR, rawPR);

  // update smoothed states for play pads
  updatePlayTP(tpL,  baselineL, rawL,  now, lastActiveLms);
  updatePlayTP(tpR,  baselineR, rawR,  now, lastActiveRms);

  // ----- Pitch pads: debounced raw-delta -----
  int dLeft  = baselinePitchL - rawPL; if (dLeft  < 0) dLeft  = 0;
  int dRight = baselinePitchR - rawPR; if (dRight < 0) dRight = 0;

  // LEFT pitch pad == DOWN (deeper)
  if (dLeft >= PITCH_ON_DELTA)  { dnOnCnt++;  dnOffCnt=0; } else
  if (dLeft <= PITCH_OFF_DELTA) { dnOffCnt++; dnOnCnt=0; }

  if (!pitchLeftOn && dnOnCnt  >= PITCH_ON_CONSEC)  pitchLeftOn = true;
  if ( pitchLeftOn && dnOffCnt >= PITCH_OFF_CONSEC) pitchLeftOn = false;

  // RIGHT pitch pad == UP (higher)
  if (dRight >= PITCH_ON_DELTA)  { upOnCnt++;  upOffCnt=0; } else
  if (dRight <= PITCH_OFF_DELTA) { upOffCnt++; upOnCnt=0; }

  if (!pitchRightOn && upOnCnt  >= PITCH_ON_CONSEC)  pitchRightOn = true;
  if ( pitchRightOn && upOffCnt >= PITCH_OFF_CONSEC) pitchRightOn = false;

  // ----- Per-side offset reset gesture -----
  bool resetLNow = tpL.touched && pitchLeftOn && pitchRightOn;
  bool resetRNow = tpR.touched && pitchLeftOn && pitchRightOn;
  if (resetLNow && !prevResetL){ leftDegOff = 0; Serial.println("[nudge] reset left offset"); }
  if (resetRNow && !prevResetR){ rightDegOff= 0; Serial.println("[nudge] reset right offset"); }
  prevResetL = resetLNow; prevResetR = resetRNow;

  // ----- Enter/Exit TUNE mode (no play pads, both strong, 3s) -----
  bool noPlayTouch = !tpL.touched && !tpR.touched;
  bool bothStrong  = (dLeft>=TUNE_STRONG_DELTA && dRight>=TUNE_STRONG_DELTA);

  if (noPlayTouch && bothStrong && pitchLeftOn && pitchRightOn) {
    if (!bothTuneSince) bothTuneSince = now;
    if (now - bothTuneSince >= BOTH_TUNE_HOLD_MS) {
      if (uiMode != MODE_TUNE) { uiMode = MODE_TUNE; lastTuneTapMs = now; Serial.printf("[ui] TUNE MODE (%.2f Hz). Tap LEFT=down, RIGHT=up; idle 5s to exit.\n", baseAHz); }
    }
  } else bothTuneSince = 0;

  if (uiMode == MODE_TUNE) {
    // only accept XOR taps to avoid chatter
    if ( pitchRightOn && !prevPitchRightOn && !pitchLeftOn) { baseAHz = fminf(880.0f, baseAHz * semiRatio(+1.0f)); buildScaleHz(); lastTuneTapMs = now; Serial.printf("[tune] +1 semi → %.2f\n", baseAHz); }
    if ( pitchLeftOn  && !prevPitchLeftOn  && !pitchRightOn){ baseAHz = fmaxf(55.0f,  baseAHz * semiRatio(-1.0f)); buildScaleHz(); lastTuneTapMs = now; Serial.printf("[tune] −1 semi → %.2f\n", baseAHz); }

    freqL = freqR = baseAHz;
    if (now - lastTuneTapMs > TUNE_IDLE_EXIT_MS) { uiMode = MODE_NORMAL; Serial.printf("[ui] Exit TUNE (%.2f)\n", baseAHz); }
  }

  // ----- Per-side live pitch nudging while holding that side -----
  auto stepUp = [](int8_t &off){ if (off < DEGREE_OFFSET_MAX) off++; };
  auto stepDn = [](int8_t &off){ if (off > DEGREE_OFFSET_MIN) off--; };

  bool comboL_Deeper = tpL.touched && pitchLeftOn;   // LEFT pitch = down
  bool comboL_Higher = tpL.touched && pitchRightOn;  // RIGHT pitch = up
  bool comboR_Deeper = tpR.touched && pitchLeftOn;
  bool comboR_Higher = tpR.touched && pitchRightOn;

  if (uiMode!=MODE_TUNE){
    if (comboL_Deeper && (!prevComboL_Deeper || now >= nextComboL_Deeper)) { stepDn(leftDegOff);  nextComboL_Deeper = now + PITCH_STEP_MS; }
    if (comboL_Higher && (!prevComboL_Higher || now >= nextComboL_Higher)) { stepUp(leftDegOff);  nextComboL_Higher = now + PITCH_STEP_MS; }
    if (comboR_Deeper && (!prevComboR_Deeper || now >= nextComboR_Deeper)) { stepDn(rightDegOff); nextComboR_Deeper = now + PITCH_STEP_MS; }
    if (comboR_Higher && (!prevComboR_Higher || now >= nextComboR_Higher)) { stepUp(rightDegOff); nextComboR_Higher = now + PITCH_STEP_MS; }
  }

  prevComboL_Deeper = comboL_Deeper; prevComboL_Higher = comboL_Higher;
  prevComboR_Deeper = comboR_Deeper; prevComboR_Higher = comboR_Higher;

  // ========= Scale browse (hold both play pads) =========
  if (uiMode != MODE_TUNE && !bootActive) {
    bool bothLR = tpL.touched && tpR.touched;
    if (bothLR) {
      if (!bothLRSince) bothLRSince = now;
      if (now - bothLRSince >= BOTH_LR_HOLD_FOR_SCALE_MS) {
        if (uiMode != MODE_SCALE_BROWSE) { uiMode = MODE_SCALE_BROWSE; lastScaleBrowseStep = 0; Serial.println("[ui] SCALE_BROWSE"); }
        if (lastScaleBrowseStep == 0 || (now - lastScaleBrowseStep >= SCALE_BROWSE_STEP_MS)) {
          scaleIndex = (scaleIndex + 1) % NUM_SCALES; buildScaleHz(); lastScaleBrowseStep = now;
        }
      }
    } else {
      if (uiMode == MODE_SCALE_BROWSE) { Serial.printf("[ui] Scale latched: %s\n", SCALES[scaleIndex].name); }
      uiMode = MODE_NORMAL; bothLRSince = 0; lastScaleBrowseStep = 0;
    }
  }

  // ========= Targets (unless TUNE): play pads drive notes =========
  if (uiMode!=MODE_TUNE){
    if (tpL.touched){
      int idx = scaleIdxFromDelta(tpL.smooth) + leftDegOff;
      freqL = scaleHzAtIdx(idx);
    } else freqL=0.0f;

    if (tpR.touched){
      int idx = scaleIdxFromDelta(tpR.smooth) + rightDegOff;
      freqR = scaleHzAtIdx(idx);
    } else freqR=0.0f;
  }

  // ---- Debug ----
  if (now - lastDbg > 500){
    lastDbg = now;
    Serial.printf("[dbg] rawL:%d rawR:%d rawPL:%d rawPR:%d | baseL:%d baseR:%d basePL:%d basePR:%d\n",
                  rawL, rawR, rawPL, rawPR, baselineL, baselineR, baselinePitchL, baselinePitchR);
    Serial.printf("[dbg] L:%d R:%d | smL=%.1f smR=%.1f | pitchL(down):%d pitchR(up):%d | offL:%d offR:%d | fL=%.1f fR=%.1f | mode=%d\n",
      (int)tpL.touched,(int)tpR.touched, tpL.smooth,tpR.smooth,
      (int)pitchLeftOn,(int)pitchRightOn, (int)leftDegOff,(int)rightDegOff, freqL,freqR,(int)uiMode);
  }

  // remember pitch states for TUNE edges
  prevPitchLeftOn  = pitchLeftOn;
  prevPitchRightOn = pitchRightOn;
}

// ================== Arduino ==================
static float vibPhaseL=0, vibPhaseR=0, phaseL=0, phaseR=0, ampL=0, ampR=0;

void setup(){
  Serial.begin(115200);
  audioInit();
  buildScaleHz();
  delay(800);
  touchRecalibrate();

#if ENABLE_DIAG_TONES
  diagStage=1; diagUntil = millis()+DIAG_TONE_MS; // LEFT 5s then RIGHT 5s
  Serial.println("[diag] left");
#else
  diagStage=0;
#endif
}

void loop(){
  uint32_t now=millis();
  if (now - lastControlMs >= CONTROL_DT_MS){ lastControlMs=now; controlUpdate(); }

  // Start with targets from control
  float wantL=freqL, wantR=freqR;

  // Diagnostic override
#if ENABLE_DIAG_TONES
  if (diagStage==1){
    wantL=baseAHz; wantR=0;
    if (now>=diagUntil){ diagStage=2; diagUntil=now+DIAG_TONE_MS; Serial.println("[diag] right"); }
  } else if (diagStage==2){
    wantL=0; wantR=baseAHz;
    if (now>=diagUntil){ diagStage=0; Serial.println("[diag] done"); }
  }
#endif

  // Boot jingle after diag
#if ENABLE_BOOT_JINGLE
  if (diagStage==0 && !bootStarted) bootStart();
  if (bootActive){
    auto semi=[&](int8_t s){ return baseAHz*powf(2.0f, s/12.0f); };
    if (!bootInGap){
      wantL = semi(BOOT_POOL[bootIdx].lSemi);
      wantR = semi(BOOT_POOL[bootIdx].rSemi);
      if (now >= bootNextMs){
        uint32_t gap = scaled(BOOT_POOL[bootIdx].gapMs);
        if (gap>0){ bootInGap=true; wantL=wantR=0; bootNextMs = now + gap; }
        else{
          bootIdx++;
          if (bootIdx < bootLen){ bootNextMs = now + scaled(BOOT_POOL[bootIdx].durMs); }
          else{
            if (++bootCycle < bootRepeat){ bootIdx=0; bootInGap=false; bootNextMs = now + scaled(BOOT_POOL[0].durMs); }
            else if (bootFinalHoldMs>0){ bootFinalHold=true; bootHoldUntil = now + bootFinalHoldMs; wantL=wantR=baseAHz; }
            else { bootStop(); }
          }
        }
      }
    } else if (now >= bootNextMs){
      bootInGap=false; bootIdx++;
      if (bootIdx < bootLen){ bootNextMs = now + scaled(BOOT_POOL[bootIdx].durMs); }
      else{
        if (++bootCycle < bootRepeat){ bootIdx=0; bootNextMs = now + scaled(BOOT_POOL[0].durMs); }
        else if (bootFinalHoldMs>0){ bootFinalHold=true; bootHoldUntil = now + bootFinalHoldMs; wantL=wantR=baseAHz; }
        else { bootStop(); }
      }
    }
    if (bootFinalHold && now>=bootHoldUntil){ bootStop(); }
  }
#endif

  // Idle breath when silent from UI and not in diag/jingle or TUNE
  bool inDiag = (diagStage==1 || diagStage==2);
  bool inBoot = bootActive;
  bool userSilent = (wantL==0 && wantR==0) && (uiMode!=MODE_TUNE) && !inDiag && !inBoot;

  // Smooth idle level gate
  float idleTarget = userSilent ? 1.f : 0.f;
  const float IDLE_GATE_ATTACK  = 0.0010f;
  const float IDLE_GATE_RELEASE = 0.0040f;
  idleGate += (idleTarget - idleGate) * (idleTarget>idleGate ? IDLE_GATE_ATTACK : IDLE_GATE_RELEASE);

  // Render block
  float blockTime=(float)BUF_SAMPLES/(float)SR;
  float a=expf(-blockTime/FREQ_GLIDE_TAU_S), keep=a, add=1.f-a;
  const float TAU=6.28318530718f;
  float vibInc = TAU*VIB_RATE_HZ/SR;

  int16_t buf[BUF_SAMPLES*2];
  for (size_t i=0;i<BUF_SAMPLES;i++){
    curFreqL = curFreqL*keep + wantL*add;
    curFreqR = curFreqR*keep + wantR*add;

    float tL = (curFreqL>0.f)? 1.f : 0.f;
    float tR = (curFreqR>0.f)? 1.f : 0.f;
    ampL += (tL-ampL)* (tL>ampL ? AMP_ATTACK : AMP_RELEASE);
    ampR += (tR-ampR)* (tR>ampR ? AMP_ATTACK : AMP_RELEASE);

    float rL = (curFreqL>0.f)? semiRatio(VIB_DEPTH_SEMITONES*sinf(vibPhaseL)) : 1.f;
    float rR = (curFreqR>0.f)? semiRatio(VIB_DEPTH_SEMITONES*sinf(vibPhaseR)) : 1.f;

    float dphiL = (curFreqL>0.f)? TAU*(curFreqL*rL)/SR : 0.f;
    float dphiR = (curFreqR>0.f)? TAU*(curFreqR*rR)/SR : 0.f;

    float sL = (curFreqL>0.f ? sinf(phaseL) : 0.f) * (32767.f*MASTER_VOL*GAIN_L*ampL);
    float sR = (curFreqR>0.f ? sinf(phaseR) : 0.f) * (32767.f*MASTER_VOL*GAIN_R*ampR);

    if (userSilent){
      float br = IDLE_BREATH_MIN + (IDLE_BREATH_MAX-IDLE_BREATH_MIN) * smooth01(fmodf(idlePhase/TAU,1.f));
      sL *= br * idleGate; sR *= br * idleGate;
      idlePhase += TAU*IDLE_BREATH_RATE_HZ/SR; if (idlePhase>TAU) idlePhase-=TAU;
    }

#if HARD_MONO_TEST
    float m = 0.5f*(sL+sR);
  #if SWAP_I2S_LR
    buf[2*i+0] = (int16_t)clampf(m, -32767.f, 32767.f);
    buf[2*i+1] = (int16_t)clampf(m, -32767.f, 32767.f);
  #else
    buf[2*i+0] = (int16_t)clampf(m, -32767.f, 32767.f);
    buf[2*i+1] = (int16_t)clampf(m, -32767.f, 32767.f);
  #endif
#else
  #if SWAP_I2S_LR
    buf[2*i+0] = (int16_t)clampf(sL, -32767.f, 32767.f);
    buf[2*i+1] = (int16_t)clampf(sR, -32767.f, 32767.f);
  #else
    // I2S_CHANNEL_FMT_RIGHT_LEFT: first is RIGHT, second is LEFT
    buf[2*i+0] = (int16_t)clampf(sR, -32767.f, 32767.f);
    buf[2*i+1] = (int16_t)clampf(sL, -32767.f, 32767.f);
  #endif
#endif
    phaseL += dphiL; if (phaseL>TAU) phaseL-=TAU;
    phaseR += dphiR; if (phaseR>TAU) phaseR-=TAU;
    vibPhaseL += vibInc; if (vibPhaseL>TAU) vibPhaseL-=TAU;
    vibPhaseR += vibInc; if (vibPhaseR>TAU) vibPhaseR-=TAU;
  }

  size_t w=0;
  esp_err_t err=i2s_write(I2S_NUM_0, buf, sizeof(buf), &w, pdMS_TO_TICKS(50));
  if (err!=ESP_OK || w==0){
    if (++i2s_consec_errors>=3 || (millis()-lastGoodI2S>1000)){
      i2s_consec_errors=0; Serial.println("[i2s] restart");
      i2s_stop(I2S_NUM_0); i2s_zero_dma_buffer(I2S_NUM_0); i2s_start(I2S_NUM_0);
      lastGoodI2S=millis();
    }
  } else { i2s_consec_errors=0; lastGoodI2S=millis(); }
}

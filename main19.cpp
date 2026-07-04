#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <iomanip>
#include <cstdint>
#include <immintrin.h>

static std::string g_symbols;
static int         g_max_length = 0;

static uint64_t g_bloom[64] = {0};

static inline void bloom_set(unsigned long long uid)
{
    unsigned b = (unsigned)((uid >> 12) & 4095);
    g_bloom[b >> 6] |= (uint64_t)1 << (b & 63);
}

static inline bool bloom_check(unsigned long long uid)
{
    unsigned b = (unsigned)((uid >> 12) & 4095);
    return (g_bloom[b >> 6] >> (b & 63)) & 1;
}

static const size_t HT_MASK = 4095;
static unsigned long long g_ht[4096] = {0};
static int g_ht_count = 0;

static unsigned long long g_targets[4096];
static int g_ntargets = 0;

// Original "0x................" token text as it appears in uids.txt, kept
// parallel to g_targets so a dehashed UID can be rewritten in-place in the file.
static std::string g_target_text[4096];

// Precomp tables: k * K65599_N for k in [0,255] — avoids per-iteration multiplies
alignas(32) static unsigned long long g_precomp_K4[256];
alignas(32) static unsigned long long g_precomp_K3[256];
alignas(32) static unsigned long long g_precomp_K2[256];

static void ht_insert(unsigned long long uid, const std::string& text)
{
    size_t i = (size_t)(uid & HT_MASK);
    while (g_ht[i]) {
        if (g_ht[i] == uid) return;
        i = (i + 1) & HT_MASK;
    }
    g_ht[i] = uid; ++g_ht_count; bloom_set(uid);
    g_target_text[g_ntargets] = text;
    g_targets[g_ntargets++] = uid;
}

static inline bool ht_find(unsigned long long uid)
{
    size_t i = (size_t)(uid & HT_MASK);
    while (g_ht[i]) {
        if (g_ht[i] == uid) return true;
        i = (i + 1) & HT_MASK;
    }
    return false;
}

static inline bool ht_find_at(unsigned long long uid, size_t i)
{
    while (g_ht[i]) {
        if (g_ht[i] == uid) return true;
        i = (i + 1) & HT_MASK;
    }
    return false;
}

static inline bool ht_find_erase(unsigned long long uid)
{
    size_t i = (size_t)(uid & HT_MASK);
    while (g_ht[i]) {
        if (g_ht[i] == uid) { g_ht[i] = 1; --g_ht_count; return true; }
        i = (i + 1) & HT_MASK;
    }
    return false;
}

static inline bool ht_find_erase_at(unsigned long long uid, size_t i)
{
    while (g_ht[i]) {
        if (g_ht[i] == uid) { g_ht[i] = 1; --g_ht_count; return true; }
        i = (i + 1) & HT_MASK;
    }
    return false;
}

static inline __m256i mul65599_v(__m256i v)
{
    return _mm256_sub_epi64(
        _mm256_add_epi64(_mm256_slli_epi64(v, 16), _mm256_slli_epi64(v, 6)), v);
}

// ── Range-check constants ────────────────────────────────────────────────────
// eps_2 < 2^23, eps_3 < 2^39, eps_4 < 2^55 for any suffix (max char = 122 'z').
// eps_5 overflows 2^64, so no useful 5-char range check exists.

static const unsigned long long K65599_2 = 65599ULL * 65599ULL;
static const unsigned long long K65599_3 = 65599ULL * 65599ULL * 65599ULL;
static const unsigned long long K65599_4 = 65599ULL * 65599ULL * 65599ULL * 65599ULL;
static const unsigned long long RANGE1   = 1ULL << 7;
static const unsigned long long RANGE2   = 1ULL << 23;
static const unsigned long long RANGE3   = 1ULL << 39;
static const unsigned long long RANGE4   = 1ULL << 55;

static uint64_t g_rc4_bits[8]       = {0};
static uint64_t g_rc3_pre_bits[1024] = {0};

static void precompute_range_bitmaps()
{
    for (int i = 0; i < g_ntargets; ++i) {
        unsigned long long t = g_targets[i];
        unsigned t9 = (unsigned)(t >> 55) & 0x1FFu;
        for (int d = -1; d <= 1; ++d) {
            unsigned k = (t9 + (unsigned)d) & 0x1FFu;
            g_rc4_bits[k >> 6] |= 1ULL << (k & 63);
        }
        unsigned t16 = (unsigned)(t >> 48) & 0xFFFFu;
        for (int d = -1; d <= 1; ++d) {
            unsigned k = (t16 + (unsigned)d) & 0xFFFFu;
            g_rc3_pre_bits[k >> 6] |= 1ULL << (k & 63);
        }
    }
    // Fill precomp tables: g_precomp_KN[k] = k * K65599_N
    for (int k = 0; k < 256; ++k) {
        g_precomp_K4[k] = (unsigned long long)k * K65599_4;
        g_precomp_K3[k] = (unsigned long long)k * K65599_3;
        g_precomp_K2[k] = (unsigned long long)k * K65599_2;
    }
}

static inline bool range_check_4(unsigned long long hx)
{
    unsigned long long pred = hx * K65599_4;
    unsigned k = (unsigned)(pred >> 55) & 0x1FFu;
    return (g_rc4_bits[k >> 6] >> (k & 63)) & 1u;
}

static inline bool range_check_3(unsigned long long hx)
{
    unsigned long long pred = hx * K65599_3;
    unsigned k16 = (unsigned)(pred >> 48) & 0xFFFFu;
    if (!((g_rc3_pre_bits[k16 >> 6] >> (k16 & 63)) & 1u)) return false;
    for (int i = 0; i < g_ntargets; ++i) {
        unsigned long long d = pred - g_targets[i];
        if (d < RANGE3 || (0ULL - d) < RANGE3) return true;
    }
    return false;
}

static inline bool range_check_2(unsigned long long hx)
{
    unsigned long long pred = hx * K65599_2;
    unsigned k16 = (unsigned)(pred >> 48) & 0xFFFFu;
    if (!((g_rc3_pre_bits[k16 >> 6] >> (k16 & 63)) & 1u)) return false;
    for (int i = 0; i < g_ntargets; ++i) {
        unsigned long long d = pred - g_targets[i];
        if (d < RANGE2 || (0ULL - d) < RANGE2) return true;
    }
    return false;
}

static bool read_settings(const char* path)
{
    std::ifstream f(path);
    if (!f) { std::cerr << "Cannot open " << path << "\n"; return false; }
    std::string line;
    while (std::getline(f, line)) {
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (line.rfind("Symbols:", 0) == 0) {
            size_t colon = line.find(':');
            if (colon == std::string::npos) continue;
            std::string raw = line.substr(colon + 1), token;
            for (size_t i = 0; i <= raw.size(); ++i) {
                if (i == raw.size() || raw[i] == ',') {
                    if (token.size() == 1) g_symbols += token[0];
                    token.clear();
                } else token += raw[i];
            }
        } else if (line.rfind("Check_Lenght:", 0) == 0 || line.rfind("Check_Length:", 0) == 0) {
            size_t colon = line.find(':');
            if (colon != std::string::npos) g_max_length = std::stoi(line.substr(colon + 1));
        }
    }
    return !g_symbols.empty() && g_max_length > 0;
}

static void load_uids(const char* path)
{
    std::ifstream f(path);
    if (!f) { std::cerr << "Cannot open " << path << "\n"; return; }
    std::string line;
    while (std::getline(f, line)) {
        if (!line.empty() && line.back() == '\r') line.pop_back();
        size_t pos = 0;
        while ((pos = line.find("0x", pos)) != std::string::npos) {
            if (pos + 18 > line.size()) { ++pos; continue; }
            unsigned long long v = 0;
            std::istringstream(line.substr(pos + 2, 16)) >> std::hex >> v;
            ht_insert(v, line.substr(pos, 18)); pos += 18;
        }
    }
}

// ── Dehash reporting + in-file replacement ───────────────────────────────────
// Find the original file token for a dehashed UID (rare path → linear scan OK).
static const std::string* find_target_text(unsigned long long uid)
{
    for (int i = 0; i < g_ntargets; ++i)
        if (g_targets[i] == uid) return &g_target_text[i];
    return nullptr;
}

// Read uids.txt whole, replace every occurrence of `search` with `replace`,
// write it back. Mirrors Replace_Text_In_File from the old UID_Dehasher.
static void replace_in_file(const char* path,
                            const std::string& search,
                            const std::string& replace)
{
    std::ifstream in(path);
    if (!in) return;
    std::ostringstream ss; ss << in.rdbuf();
    std::string content = ss.str();
    in.close();

    size_t pos = 0;
    while ((pos = content.find(search, pos)) != std::string::npos) {
        content.replace(pos, search.size(), replace);
        pos += replace.size();
    }

    std::ofstream out(path);
    if (!out) return;
    out << content;
}

// Print the hit AND rewrite the original 0x… token in uids.txt to the word.
static void report_dehash(unsigned long long uid, const std::string& word)
{
    std::cout << "Dehashed! 0x" << std::uppercase << std::hex
              << std::setw(16) << std::setfill('0') << uid
              << std::dec << std::nouppercase << std::setfill(' ')
              << " means: " << word << "\n";
    const std::string* tok = find_target_text(uid);
    if (tok) replace_in_file("uids.txt", *tok, word);
}

// ── Macros (erase versions for generate_4..8) ────────────────────────────────
#define CHECK(UIDn, ...)                                                        \
    if (bloom_check(UIDn) && ht_find_erase(UIDn)) {                            \
        std::ostringstream _oss; _oss << __VA_ARGS__;                          \
        report_dehash((UIDn), _oss.str()); }

#define PRINT_DEHASH(uid, ...)                                                  \
    do { std::ostringstream _oss; _oss << __VA_ARGS__;                         \
         report_dehash((uid), _oss.str()); } while (0)

#define BLOOM4(uid_V, hits_out)                                                 \
    do {                                                                        \
        __m256i _b   = _mm256_and_si256(_mm256_srli_epi64((uid_V), 12), MASK4095); \
        __m256i _w   = _mm256_srli_epi64(_b, 6);                               \
        __m256i _p   = _mm256_and_si256(_b, MASK63);                           \
        __m256i _wds = _mm256_i64gather_epi64((const long long*)g_bloom, _w, 8); \
        (hits_out)   = _mm256_and_si256(_mm256_srlv_epi64(_wds, _p), ONE);     \
    } while(0)

#define EXTR_CHKF(hmask, bits, ureg, lane, penu_base, penu_off)                \
    if ((hmask) & (bits)) {                                                     \
        unsigned long long _u = (unsigned long long)_mm256_extract_epi64((ureg), (lane)); \
        if (ht_find_erase_at(_u, (size_t)(_u & HT_MASK)))                      \
            PRINT_DEHASH(_u, PREFIX<<syms[(penu_base)+(penu_off)]<<syms[LAST_CHAR]); \
    }

#define SCALAR_CHKF(hmask, bits, prev_x, sym_i, sv_val)                        \
    if ((hmask) & (bits)) {                                                     \
        unsigned long long _u = ((prev_x) ^ sval[sym_i]) * 65599ULL ^ (sv_val); \
        if (ht_find_erase_at(_u, (size_t)(_u & HT_MASK)))                      \
            PRINT_DEHASH(_u, PREFIX<<syms[sym_i]<<syms[LAST_CHAR]);             \
    }

#define H12_LOOP(pxa, pxb, pxc, base, px_hash)                                 \
    for (int LAST_CHAR = 0; LAST_CHAR < C; ++LAST_CHAR) {                      \
        __m256i _sv = _mm256_set1_epi64x((long long)sval[LAST_CHAR]);          \
        __m256i _ha; BLOOM4(_mm256_xor_si256((pxa), _sv), _ha);                \
        __m256i _hb; BLOOM4(_mm256_xor_si256((pxb), _sv), _hb);                \
        __m256i _hc; BLOOM4(_mm256_xor_si256((pxc), _sv), _hc);                \
        __m256i _any = _mm256_or_si256(_mm256_or_si256(_ha, _hb), _hc);       \
        if (__builtin_expect(!_mm256_testz_si256(_any, _any), 0)) {            \
            unsigned long long _sv_val = sval[LAST_CHAR];                      \
            int _ma=_mm256_movemask_epi8(_mm256_cmpeq_epi64(_ha, ONE));        \
            int _mb=_mm256_movemask_epi8(_mm256_cmpeq_epi64(_hb, ONE));        \
            int _mc=_mm256_movemask_epi8(_mm256_cmpeq_epi64(_hc, ONE));        \
            SCALAR_CHKF(_ma,0x000000FF,(px_hash),(base)+ 0,_sv_val)            \
            SCALAR_CHKF(_ma,0x0000FF00,(px_hash),(base)+ 1,_sv_val)            \
            SCALAR_CHKF(_ma,0x00FF0000,(px_hash),(base)+ 2,_sv_val)            \
            SCALAR_CHKF(_ma,0xFF000000,(px_hash),(base)+ 3,_sv_val)            \
            SCALAR_CHKF(_mb,0x000000FF,(px_hash),(base)+ 4,_sv_val)            \
            SCALAR_CHKF(_mb,0x0000FF00,(px_hash),(base)+ 5,_sv_val)            \
            SCALAR_CHKF(_mb,0x00FF0000,(px_hash),(base)+ 6,_sv_val)            \
            SCALAR_CHKF(_mb,0xFF000000,(px_hash),(base)+ 7,_sv_val)            \
            SCALAR_CHKF(_mc,0x000000FF,(px_hash),(base)+ 8,_sv_val)            \
            SCALAR_CHKF(_mc,0x0000FF00,(px_hash),(base)+ 9,_sv_val)            \
            SCALAR_CHKF(_mc,0x00FF0000,(px_hash),(base)+10,_sv_val)            \
            SCALAR_CHKF(_mc,0xFF000000,(px_hash),(base)+11,_sv_val)            \
        }                                                                       \
    }

#define H8_LOOP(pxa, pxb, base, px_hash)                                       \
    for (int LAST_CHAR = 0; LAST_CHAR < C; ++LAST_CHAR) {                      \
        __m256i _sv = _mm256_set1_epi64x((long long)sval[LAST_CHAR]);          \
        __m256i _ha; BLOOM4(_mm256_xor_si256((pxa), _sv), _ha);                \
        __m256i _hb; BLOOM4(_mm256_xor_si256((pxb), _sv), _hb);                \
        __m256i _any = _mm256_or_si256(_ha, _hb);                              \
        if (__builtin_expect(!_mm256_testz_si256(_any, _any), 0)) {            \
            unsigned long long _sv_val = sval[LAST_CHAR];                      \
            int _ma=_mm256_movemask_epi8(_mm256_cmpeq_epi64(_ha, ONE));        \
            int _mb=_mm256_movemask_epi8(_mm256_cmpeq_epi64(_hb, ONE));        \
            SCALAR_CHKF(_ma,0x000000FF,(px_hash),(base)+0,_sv_val)             \
            SCALAR_CHKF(_ma,0x0000FF00,(px_hash),(base)+1,_sv_val)             \
            SCALAR_CHKF(_ma,0x00FF0000,(px_hash),(base)+2,_sv_val)             \
            SCALAR_CHKF(_ma,0xFF000000,(px_hash),(base)+3,_sv_val)             \
            SCALAR_CHKF(_mb,0x000000FF,(px_hash),(base)+4,_sv_val)             \
            SCALAR_CHKF(_mb,0x0000FF00,(px_hash),(base)+5,_sv_val)             \
            SCALAR_CHKF(_mb,0x00FF0000,(px_hash),(base)+6,_sv_val)             \
            SCALAR_CHKF(_mb,0xFF000000,(px_hash),(base)+7,_sv_val)             \
        }                                                                       \
    }

// ── generate_4 ────────────────────────────────────────────────────────────────
#define PREFIX    syms[a]<<syms[b]
#define LAST_CHAR d
__attribute__((optimize("O3"), target("avx2")))
static void generate_4()
{
    const int C = (int)g_symbols.size();
    const char* const syms = g_symbols.c_str();
    alignas(32) unsigned long long sval[256];
    for (int i = 0; i < C; ++i) sval[i] = (unsigned char)syms[i];

    const __m256i MASK4095 = _mm256_set1_epi64x(4095);
    const __m256i MASK63   = _mm256_set1_epi64x(63);
    const __m256i ONE      = _mm256_set1_epi64x(1);

    unsigned long long UID1=0,UID1x=0,UID2=0,UID2x=0,UID3=0,UID3x=0,UID4=0;
    std::cout << "[Length 4] Start\n";
    for (int a=0;a<C && g_ht_count>0;++a){ UID1=sval[a]; UID1x=UID1*65599ULL;
    for (int b=0;b<C && g_ht_count>0;++b){ UID2=UID1x^sval[b]; UID2x=UID2*65599ULL;
        __m256i uid2x_v = _mm256_set1_epi64x((long long)UID2x);
        int c = 0;
        for (; c+11 < C && g_ht_count > 0; c += 12) {
            __m256i uid3ax = mul65599_v(_mm256_xor_si256(uid2x_v, _mm256_load_si256((const __m256i*)&sval[c])));
            __m256i uid3bx = mul65599_v(_mm256_xor_si256(uid2x_v, _mm256_load_si256((const __m256i*)&sval[c+4])));
            __m256i uid3cx = mul65599_v(_mm256_xor_si256(uid2x_v, _mm256_load_si256((const __m256i*)&sval[c+8])));
#undef LAST_CHAR
            H12_LOOP(uid3ax, uid3bx, uid3cx, c, UID2x)
#define LAST_CHAR d
        }
        for (; c+7 < C && g_ht_count > 0; c += 8) {
            __m256i uid3ax = mul65599_v(_mm256_xor_si256(uid2x_v, _mm256_load_si256((const __m256i*)&sval[c])));
            __m256i uid3bx = mul65599_v(_mm256_xor_si256(uid2x_v, _mm256_load_si256((const __m256i*)&sval[c+4])));
#undef LAST_CHAR
            H8_LOOP(uid3ax, uid3bx, c, UID2x)
#define LAST_CHAR d
        }
        for (; c+3 < C && g_ht_count > 0; c += 4) {
            __m256i uid3x = mul65599_v(_mm256_xor_si256(uid2x_v, _mm256_load_si256((const __m256i*)&sval[c])));
            for (int d = 0; d < C; ++d) {
                __m256i uid4 = _mm256_xor_si256(uid3x, _mm256_set1_epi64x((long long)sval[d]));
                __m256i hits; BLOOM4(uid4, hits);
                if (__builtin_expect(!_mm256_testz_si256(hits, hits), 0)) {
                    int ah=_mm256_movemask_epi8(_mm256_cmpeq_epi64(hits,ONE));
                    EXTR_CHKF(ah,0x000000FF,uid4,0,c,0) EXTR_CHKF(ah,0x0000FF00,uid4,1,c,1)
                    EXTR_CHKF(ah,0x00FF0000,uid4,2,c,2) EXTR_CHKF(ah,0xFF000000,uid4,3,c,3)
                }
            }
        }
        for (; c < C; ++c){ UID3=UID2x^sval[c]; UID3x=UID3*65599ULL;
            for (int d=0;d<C;++d){ UID4=UID3x^sval[d]; CHECK(UID4, syms[a]<<syms[b]<<syms[c]<<syms[d]) }
        }
    }}
    std::cout << "[Length 4] Finish\n";
}
#undef PREFIX
#undef LAST_CHAR

// ── generate_5 ────────────────────────────────────────────────────────────────
#define PREFIX    syms[a]<<syms[b]<<syms[c]
#define LAST_CHAR e
__attribute__((optimize("O3"), target("avx2")))
static void generate_5()
{
    const int C = (int)g_symbols.size();
    const char* const syms = g_symbols.c_str();
    alignas(32) unsigned long long sval[256];
    for (int i = 0; i < C; ++i) sval[i] = (unsigned char)syms[i];

    const __m256i MASK4095 = _mm256_set1_epi64x(4095);
    const __m256i MASK63   = _mm256_set1_epi64x(63);
    const __m256i ONE      = _mm256_set1_epi64x(1);

    unsigned long long UID1=0,UID1x=0,UID2=0,UID2x=0,UID3=0,UID3x=0,UID4=0,UID4x=0,UID5=0;
    std::cout << "[Length 5] Start\n";
    for (int a=0;a<C && g_ht_count>0;++a){ UID1=sval[a]; UID1x=UID1*65599ULL;
    for (int b=0;b<C;++b){                 UID2=UID1x^sval[b]; UID2x=UID2*65599ULL;
        if (!range_check_3(UID2)) continue;
    for (int c=0;c<C && g_ht_count>0;++c){ UID3=UID2x^sval[c]; UID3x=UID3*65599ULL;
        __m256i uid3x_v = _mm256_set1_epi64x((long long)UID3x);
        int d = 0;
        for (; d+11 < C && g_ht_count > 0; d += 12) {
            __m256i uid4ax = mul65599_v(_mm256_xor_si256(uid3x_v, _mm256_load_si256((const __m256i*)&sval[d])));
            __m256i uid4bx = mul65599_v(_mm256_xor_si256(uid3x_v, _mm256_load_si256((const __m256i*)&sval[d+4])));
            __m256i uid4cx = mul65599_v(_mm256_xor_si256(uid3x_v, _mm256_load_si256((const __m256i*)&sval[d+8])));
#undef LAST_CHAR
            H12_LOOP(uid4ax, uid4bx, uid4cx, d, UID3x)
#define LAST_CHAR e
        }
        for (; d+7 < C && g_ht_count > 0; d += 8) {
            __m256i uid4ax = mul65599_v(_mm256_xor_si256(uid3x_v, _mm256_load_si256((const __m256i*)&sval[d])));
            __m256i uid4bx = mul65599_v(_mm256_xor_si256(uid3x_v, _mm256_load_si256((const __m256i*)&sval[d+4])));
#undef LAST_CHAR
            H8_LOOP(uid4ax, uid4bx, d, UID3x)
#define LAST_CHAR e
        }
        for (; d+3 < C && g_ht_count > 0; d += 4) {
            __m256i uid4x = mul65599_v(_mm256_xor_si256(uid3x_v, _mm256_load_si256((const __m256i*)&sval[d])));
            for (int e = 0; e < C; ++e) {
                __m256i uid5 = _mm256_xor_si256(uid4x, _mm256_set1_epi64x((long long)sval[e]));
                __m256i hits; BLOOM4(uid5, hits);
                if (__builtin_expect(!_mm256_testz_si256(hits, hits), 0)) {
                    int ah=_mm256_movemask_epi8(_mm256_cmpeq_epi64(hits,ONE));
                    EXTR_CHKF(ah,0x000000FF,uid5,0,d,0) EXTR_CHKF(ah,0x0000FF00,uid5,1,d,1)
                    EXTR_CHKF(ah,0x00FF0000,uid5,2,d,2) EXTR_CHKF(ah,0xFF000000,uid5,3,d,3)
                }
            }
        }
        for (; d < C; ++d){ UID4=UID3x^sval[d]; UID4x=UID4*65599ULL;
            for (int e=0;e<C;++e){ UID5=UID4x^sval[e]; CHECK(UID5, syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]) }
        }
    }}}
    std::cout << "[Length 5] Finish\n";
}
#undef PREFIX
#undef LAST_CHAR

// ── generate_6 ────────────────────────────────────────────────────────────────
#define PREFIX    syms[a]<<syms[b]<<syms[c]<<syms[d]
#define LAST_CHAR f
__attribute__((optimize("O3"), target("avx2")))
static void generate_6()
{
    const int C = (int)g_symbols.size();
    const char* const syms = g_symbols.c_str();
    alignas(32) unsigned long long sval[256];
    for (int i = 0; i < C; ++i) sval[i] = (unsigned char)syms[i];

    const __m256i MASK4095 = _mm256_set1_epi64x(4095);
    const __m256i MASK63   = _mm256_set1_epi64x(63);
    const __m256i ONE      = _mm256_set1_epi64x(1);

    unsigned long long UID1=0,UID1x=0,UID2=0,UID2x=0,UID3=0,UID3x=0,
                       UID4=0,UID4x=0,UID5=0,UID5x=0,UID6=0;
    std::cout << "[Length 6] Start\n";
    for (int a=0;a<C && g_ht_count>0;++a){ UID1=sval[a]; UID1x=UID1*65599ULL;
    for (int b=0;b<C;++b){                 UID2=UID1x^sval[b]; UID2x=UID2*65599ULL;
    for (int c=0;c<C;++c){                 UID3=UID2x^sval[c]; UID3x=UID3*65599ULL;
        if (!range_check_3(UID3)) continue;
    for (int d=0;d<C && g_ht_count>0;++d){ UID4=UID3x^sval[d]; UID4x=UID4*65599ULL;
        __m256i uid4x_v = _mm256_set1_epi64x((long long)UID4x);
        int e = 0;
        for (; e+11 < C && g_ht_count > 0; e += 12) {
            __m256i uid5ax = mul65599_v(_mm256_xor_si256(uid4x_v, _mm256_load_si256((const __m256i*)&sval[e])));
            __m256i uid5bx = mul65599_v(_mm256_xor_si256(uid4x_v, _mm256_load_si256((const __m256i*)&sval[e+4])));
            __m256i uid5cx = mul65599_v(_mm256_xor_si256(uid4x_v, _mm256_load_si256((const __m256i*)&sval[e+8])));
#undef LAST_CHAR
            H12_LOOP(uid5ax, uid5bx, uid5cx, e, UID4x)
#define LAST_CHAR f
        }
        for (; e+7 < C && g_ht_count > 0; e += 8) {
            __m256i uid5ax = mul65599_v(_mm256_xor_si256(uid4x_v, _mm256_load_si256((const __m256i*)&sval[e])));
            __m256i uid5bx = mul65599_v(_mm256_xor_si256(uid4x_v, _mm256_load_si256((const __m256i*)&sval[e+4])));
#undef LAST_CHAR
            H8_LOOP(uid5ax, uid5bx, e, UID4x)
#define LAST_CHAR f
        }
        for (; e+3 < C && g_ht_count > 0; e += 4) {
            __m256i uid5x = mul65599_v(_mm256_xor_si256(uid4x_v, _mm256_load_si256((const __m256i*)&sval[e])));
            for (int f = 0; f < C; ++f) {
                __m256i uid6 = _mm256_xor_si256(uid5x, _mm256_set1_epi64x((long long)sval[f]));
                __m256i hits; BLOOM4(uid6, hits);
                if (__builtin_expect(!_mm256_testz_si256(hits, hits), 0)) {
                    int ah=_mm256_movemask_epi8(_mm256_cmpeq_epi64(hits,ONE));
                    EXTR_CHKF(ah,0x000000FF,uid6,0,e,0) EXTR_CHKF(ah,0x0000FF00,uid6,1,e,1)
                    EXTR_CHKF(ah,0x00FF0000,uid6,2,e,2) EXTR_CHKF(ah,0xFF000000,uid6,3,e,3)
                }
            }
        }
        for (; e < C; ++e){ UID5=UID4x^sval[e]; UID5x=UID5*65599ULL;
            for (int f=0;f<C;++f){ UID6=UID5x^sval[f]; CHECK(UID6, syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]<<syms[f]) }
        }
    }}}}
    std::cout << "[Length 6] Finish\n";
}
#undef PREFIX
#undef LAST_CHAR

// ── generate_7 ────────────────────────────────────────────────────────────────
#define PREFIX    syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]
#define LAST_CHAR g
__attribute__((optimize("O3"), target("avx2")))
static void generate_7()
{
    const int C = (int)g_symbols.size();
    const char* const syms = g_symbols.c_str();
    alignas(32) unsigned long long sval[256];
    for (int i = 0; i < C; ++i) sval[i] = (unsigned char)syms[i];

    const __m256i MASK4095 = _mm256_set1_epi64x(4095);
    const __m256i MASK63   = _mm256_set1_epi64x(63);
    const __m256i ONE      = _mm256_set1_epi64x(1);

    unsigned long long UID1=0,UID1x=0,UID2=0,UID2x=0,UID3=0,UID3x=0,
                       UID4=0,UID4x=0,UID5=0,UID5x=0,UID6=0,UID6x=0,UID7=0;
    std::cout << "[Length 7] Start\n";
    for (int a=0;a<C && g_ht_count>0;++a){ UID1=sval[a]; UID1x=UID1*65599ULL;
    for (int b=0;b<C;++b){                 UID2=UID1x^sval[b]; UID2x=UID2*65599ULL;
    for (int c=0;c<C;++c){                 UID3=UID2x^sval[c]; UID3x=UID3*65599ULL;
    for (int d=0;d<C;++d){                 UID4=UID3x^sval[d]; UID4x=UID4*65599ULL;
        if (!range_check_3(UID4)) continue;
    for (int e=0;e<C && g_ht_count>0;++e){ UID5=UID4x^sval[e]; UID5x=UID5*65599ULL;
        __m256i uid5x_v = _mm256_set1_epi64x((long long)UID5x);
        int f = 0;
        for (; f+11 < C && g_ht_count > 0; f += 12) {
            __m256i uid6ax = mul65599_v(_mm256_xor_si256(uid5x_v, _mm256_load_si256((const __m256i*)&sval[f])));
            __m256i uid6bx = mul65599_v(_mm256_xor_si256(uid5x_v, _mm256_load_si256((const __m256i*)&sval[f+4])));
            __m256i uid6cx = mul65599_v(_mm256_xor_si256(uid5x_v, _mm256_load_si256((const __m256i*)&sval[f+8])));
#undef LAST_CHAR
            H12_LOOP(uid6ax, uid6bx, uid6cx, f, UID5x)
#define LAST_CHAR g
        }
        for (; f+7 < C && g_ht_count > 0; f += 8) {
            __m256i uid6ax = mul65599_v(_mm256_xor_si256(uid5x_v, _mm256_load_si256((const __m256i*)&sval[f])));
            __m256i uid6bx = mul65599_v(_mm256_xor_si256(uid5x_v, _mm256_load_si256((const __m256i*)&sval[f+4])));
#undef LAST_CHAR
            H8_LOOP(uid6ax, uid6bx, f, UID5x)
#define LAST_CHAR g
        }
        for (; f+3 < C && g_ht_count > 0; f += 4) {
            __m256i uid6x = mul65599_v(_mm256_xor_si256(uid5x_v, _mm256_load_si256((const __m256i*)&sval[f])));
            for (int g = 0; g < C; ++g) {
                __m256i uid7 = _mm256_xor_si256(uid6x, _mm256_set1_epi64x((long long)sval[g]));
                __m256i hits; BLOOM4(uid7, hits);
                if (__builtin_expect(!_mm256_testz_si256(hits, hits), 0)) {
                    int ah=_mm256_movemask_epi8(_mm256_cmpeq_epi64(hits,ONE));
                    EXTR_CHKF(ah,0x000000FF,uid7,0,f,0) EXTR_CHKF(ah,0x0000FF00,uid7,1,f,1)
                    EXTR_CHKF(ah,0x00FF0000,uid7,2,f,2) EXTR_CHKF(ah,0xFF000000,uid7,3,f,3)
                }
            }
        }
        for (; f < C; ++f){ UID6=UID5x^sval[f]; UID6x=UID6*65599ULL;
            for (int g=0;g<C;++g){ UID7=UID6x^sval[g]; CHECK(UID7, syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]<<syms[f]<<syms[g]) }
        }
    }}}}}
    std::cout << "[Length 7] Finish\n";
}
#undef PREFIX
#undef LAST_CHAR

// ── generate_8 ────────────────────────────────────────────────────────────────
#define PREFIX    syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]<<syms[f]
#define LAST_CHAR h
__attribute__((optimize("O3"), target("avx2")))
static void generate_8()
{
    const int C = (int)g_symbols.size();
    const char* const syms = g_symbols.c_str();
    alignas(32) unsigned long long sval[256];
    for (int i = 0; i < C; ++i) sval[i] = (unsigned char)syms[i];

    const __m256i MASK4095 = _mm256_set1_epi64x(4095);
    const __m256i MASK63   = _mm256_set1_epi64x(63);
    const __m256i ONE      = _mm256_set1_epi64x(1);

    unsigned long long UID1=0,UID1x=0,UID2=0,UID2x=0,UID3=0,UID3x=0,
                       UID4=0,UID4x=0,UID5=0,UID5x=0,UID6=0,UID6x=0,
                       UID7=0,UID7x=0,UID8=0;
    std::cout << "[Length 8] Start\n";
    for (int a=0;a<C && g_ht_count>0;++a){ UID1=sval[a]; UID1x=UID1*65599ULL;
    for (int b=0;b<C;++b){                 UID2=UID1x^sval[b]; UID2x=UID2*65599ULL;
    for (int c=0;c<C;++c){                 UID3=UID2x^sval[c]; UID3x=UID3*65599ULL;
    for (int d=0;d<C;++d){                 UID4=UID3x^sval[d]; UID4x=UID4*65599ULL;
    for (int e=0;e<C;++e){                 UID5=UID4x^sval[e];
        if (__builtin_expect(!range_check_3(UID5), 1)) continue;
        UID5x=UID5*65599ULL;
    for (int f=0;f<C && g_ht_count>0;++f){ UID6=UID5x^sval[f]; UID6x=UID6*65599ULL;
        __m256i uid6x_v = _mm256_set1_epi64x((long long)UID6x);
        int g = 0;
        for (; g+11 < C && g_ht_count > 0; g += 12) {
            __m256i uid7ax = mul65599_v(_mm256_xor_si256(uid6x_v, _mm256_load_si256((const __m256i*)&sval[g])));
            __m256i uid7bx = mul65599_v(_mm256_xor_si256(uid6x_v, _mm256_load_si256((const __m256i*)&sval[g+4])));
            __m256i uid7cx = mul65599_v(_mm256_xor_si256(uid6x_v, _mm256_load_si256((const __m256i*)&sval[g+8])));
#undef LAST_CHAR
            H12_LOOP(uid7ax, uid7bx, uid7cx, g, UID6x)
#define LAST_CHAR h
        }
        for (; g+7 < C && g_ht_count > 0; g += 8) {
            __m256i uid7ax = mul65599_v(_mm256_xor_si256(uid6x_v, _mm256_load_si256((const __m256i*)&sval[g])));
            __m256i uid7bx = mul65599_v(_mm256_xor_si256(uid6x_v, _mm256_load_si256((const __m256i*)&sval[g+4])));
#undef LAST_CHAR
            H8_LOOP(uid7ax, uid7bx, g, UID6x)
#define LAST_CHAR h
        }
        for (; g+3 < C && g_ht_count > 0; g += 4) {
            __m256i uid7x = mul65599_v(_mm256_xor_si256(uid6x_v, _mm256_load_si256((const __m256i*)&sval[g])));
            for (int h = 0; h < C; ++h) {
                __m256i uid8 = _mm256_xor_si256(uid7x, _mm256_set1_epi64x((long long)sval[h]));
                __m256i hits; BLOOM4(uid8, hits);
                if (__builtin_expect(!_mm256_testz_si256(hits, hits), 0)) {
                    int ah=_mm256_movemask_epi8(_mm256_cmpeq_epi64(hits,ONE));
                    EXTR_CHKF(ah,0x000000FF,uid8,0,g,0) EXTR_CHKF(ah,0x0000FF00,uid8,1,g,1)
                    EXTR_CHKF(ah,0x00FF0000,uid8,2,g,2) EXTR_CHKF(ah,0xFF000000,uid8,3,g,3)
                }
            }
        }
        for (; g < C; ++g){ UID7=UID6x^sval[g]; UID7x=UID7*65599ULL;
            for (int h=0;h<C;++h){ UID8=UID7x^sval[h]; CHECK(UID8, syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]<<syms[f]<<syms[g]<<syms[h]) }
        }
    }}}}}}
    std::cout << "[Length 8] Finish\n";
}
#undef PREFIX
#undef LAST_CHAR

// ── generate_9+: non-erasing find (report all preimages) ─────────────────────
#undef CHECK
#define CHECK(UIDn, ...)                                                        \
    if (bloom_check(UIDn) && ht_find(UIDn)) {                                  \
        std::ostringstream _oss; _oss << __VA_ARGS__;                          \
        report_dehash((UIDn), _oss.str()); }

#undef EXTR_CHKF
#define EXTR_CHKF(hmask, bits, ureg, lane, penu_base, penu_off)                \
    if ((hmask) & (bits)) {                                                     \
        unsigned long long _u = (unsigned long long)_mm256_extract_epi64((ureg), (lane)); \
        if (ht_find_at(_u, (size_t)(_u & HT_MASK)))                            \
            PRINT_DEHASH(_u, PREFIX<<syms[(penu_base)+(penu_off)]<<syms[LAST_CHAR]); \
    }

#undef SCALAR_CHKF
#define SCALAR_CHKF(hmask, bits, prev_x, sym_i, sv_val)                        \
    if ((hmask) & (bits)) {                                                     \
        unsigned long long _u = ((prev_x) ^ sval[sym_i]) * 65599ULL ^ (sv_val); \
        if (ht_find_at(_u, (size_t)(_u & HT_MASK)))                            \
            PRINT_DEHASH(_u, PREFIX<<syms[sym_i]<<syms[LAST_CHAR]);             \
    }

// ── generate_9 helpers ────────────────────────────────────────────────────────
alignas(32) static unsigned long long g9_sval[256];

// generate_9_hi: h,i batch loops once we know UID7x and the current g-index.
// Called by generate_9_g for each g that passes rc2.
#define PREFIX    syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]<<syms[fi]<<syms[g]
#define LAST_CHAR i
__attribute__((noinline, optimize("O3"), target("avx2")))
static void generate_9_hi(unsigned long long UID7x,
                           int a, int b, int c, int d, int e, int fi, int g,
                           const char* syms, int C)
{
    const unsigned long long* sval = g9_sval;
    const __m256i MASK4095 = _mm256_set1_epi64x(4095);
    const __m256i MASK63   = _mm256_set1_epi64x(63);
    const __m256i ONE      = _mm256_set1_epi64x(1);
    unsigned long long UID8=0,UID8x=0,UID9=0;
    __m256i uid7x_v = _mm256_set1_epi64x((long long)UID7x);
    int h = 0;
    for (; h+11 < C; h += 12) {
        __m256i uid8ax = mul65599_v(_mm256_xor_si256(uid7x_v, _mm256_load_si256((const __m256i*)&sval[h])));
        __m256i uid8bx = mul65599_v(_mm256_xor_si256(uid7x_v, _mm256_load_si256((const __m256i*)&sval[h+4])));
        __m256i uid8cx = mul65599_v(_mm256_xor_si256(uid7x_v, _mm256_load_si256((const __m256i*)&sval[h+8])));
        H12_LOOP(uid8ax, uid8bx, uid8cx, h, UID7x)
    }
    for (; h+7 < C; h += 8) {
        __m256i uid8ax = mul65599_v(_mm256_xor_si256(uid7x_v, _mm256_load_si256((const __m256i*)&sval[h])));
        __m256i uid8bx = mul65599_v(_mm256_xor_si256(uid7x_v, _mm256_load_si256((const __m256i*)&sval[h+4])));
        H8_LOOP(uid8ax, uid8bx, h, UID7x)
    }
    for (; h+3 < C; h += 4) {
        __m256i uid8x = mul65599_v(_mm256_xor_si256(uid7x_v, _mm256_load_si256((const __m256i*)&sval[h])));
        for (int i = 0; i < C; ++i) {
            __m256i uid9 = _mm256_xor_si256(uid8x, _mm256_set1_epi64x((long long)sval[i]));
            __m256i hits; BLOOM4(uid9, hits);
            if (__builtin_expect(!_mm256_testz_si256(hits, hits), 0)) {
                int ah=_mm256_movemask_epi8(_mm256_cmpeq_epi64(hits,ONE));
                EXTR_CHKF(ah,0x000000FF,uid9,0,h,0) EXTR_CHKF(ah,0x0000FF00,uid9,1,h,1)
                EXTR_CHKF(ah,0x00FF0000,uid9,2,h,2) EXTR_CHKF(ah,0xFF000000,uid9,3,h,3)
            }
        }
    }
    for (; h < C; ++h){ UID8=UID7x^sval[h]; UID8x=UID8*65599ULL;
        for (int i=0;i<C;++i){ UID9=UID8x^sval[i]; CHECK(UID9, PREFIX<<syms[h]<<syms[i]) }
    }
}
#undef PREFIX
#undef LAST_CHAR

// generate_9_g: vectorized rc2 pre-filter over 4 g-values at once using
// precomp K2 table + AVX2 gather; calls generate_9_hi for each passing g.
__attribute__((noinline, optimize("O3"), target("avx2")))
static void generate_9_g(unsigned long long UID6x,
                          int a, int b, int c, int d, int e, int fi,
                          const char* syms, int C)
{
    const unsigned long long* sval = g9_sval;
    const __m256i ONE    = _mm256_set1_epi64x(1);
    const __m256i MASK63 = _mm256_set1_epi64x(63);
    const __m256i MASK16 = _mm256_set1_epi64x(0xFFFF);

    // Precomp: (UID6x ^ sval[g]) * K65599_2
    //        = (UID6x & ~0xFF)*K65599_2 + ((UID6x & 0xFF)^sval[g])*K65599_2
    //        = base_K2 + g_precomp_K2[(UID6x_low ^ sval[g])]
    unsigned long long UID6x_low = UID6x & 0xFFULL;
    unsigned long long base_K2   = (UID6x & ~0xFFULL) * K65599_2;
    __m256i base_K2_v   = _mm256_set1_epi64x((long long)base_K2);
    __m256i UID6x_low_v = _mm256_set1_epi64x((long long)UID6x_low);

    // Vectorized g-loop: 4 at a time
    int g_base = 0;
    for (; g_base+3 < C; g_base += 4) {
        // Compute pred2 = base_K2 + g_precomp_K2[(UID6x_low ^ sval[g+i])] for i=0..3
        __m256i sval4   = _mm256_load_si256((const __m256i*)&sval[g_base]);
        __m256i idx4    = _mm256_xor_si256(UID6x_low_v, sval4);
        __m256i pk2_4   = _mm256_i64gather_epi64((const long long*)g_precomp_K2, idx4, 8);
        __m256i pred2_4 = _mm256_add_epi64(base_K2_v, pk2_4);

        // Pre-filter: k16 = (pred2 >> 48) & 0xFFFF; check g_rc3_pre_bits[k16>>6] bit k16&63
        __m256i k16_4  = _mm256_and_si256(_mm256_srli_epi64(pred2_4, 48), MASK16);
        __m256i widx4  = _mm256_srli_epi64(k16_4, 6);
        __m256i words4 = _mm256_i64gather_epi64((const long long*)g_rc3_pre_bits, widx4, 8);
        __m256i bits4  = _mm256_and_si256(
                             _mm256_srlv_epi64(words4, _mm256_and_si256(k16_4, MASK63)), ONE);

        if (_mm256_testz_si256(bits4, bits4)) continue;  // all 4 rejected

        // At least one passed pre-filter; extract pred2 and process each lane
        alignas(32) unsigned long long pred2[4];
        _mm256_store_si256((__m256i*)pred2, pred2_4);
        unsigned hmask = (unsigned)_mm256_movemask_epi8(_mm256_cmpeq_epi64(bits4, ONE));

        for (int i = 0; i < 4; ++i) {
            if (!((hmask >> (i * 8)) & 0xFFu)) continue;
            // Exact scan
            unsigned long long p = pred2[i];
            bool ok = false;
            for (int j = 0; j < g_ntargets; ++j) {
                unsigned long long dd = p - g_targets[j];
                if (dd < RANGE2 || (0ULL - dd) < RANGE2) { ok = true; break; }
            }
            if (!ok) continue;
            int g = g_base + i;
            unsigned long long UID7  = UID6x ^ sval[g];
            unsigned long long UID7x = UID7 * 65599ULL;
            generate_9_hi(UID7x, a, b, c, d, e, fi, g, syms, C);
        }
    }
    // Scalar tail (at most 3 remaining g-values)
    for (int g = g_base; g < C; ++g) {
        unsigned long long pred2_s = base_K2 + g_precomp_K2[UID6x_low ^ sval[g]];
        unsigned k16 = (unsigned)(pred2_s >> 48) & 0xFFFFu;
        if (!((g_rc3_pre_bits[k16 >> 6] >> (k16 & 63)) & 1u)) continue;
        bool ok = false;
        for (int j = 0; j < g_ntargets; ++j) {
            unsigned long long dd = pred2_s - g_targets[j];
            if (dd < RANGE2 || (0ULL - dd) < RANGE2) { ok = true; break; }
        }
        if (!ok) continue;
        unsigned long long UID7  = UID6x ^ sval[g];
        unsigned long long UID7x = UID7 * 65599ULL;
        generate_9_hi(UID7x, a, b, c, d, e, fi, g, syms, C);
    }
}

// ── generate_9 ────────────────────────────────────────────────────────────────
// Precomp K4 at e-level: saves C-1 multiplies per d-iteration (C≈37 → 36 saves).
// Precomp K3 at f-level: saves C-1 multiplies per passing e-iteration.
__attribute__((optimize("O3"), target("avx2")))
static void generate_9()
{
    const int C = (int)g_symbols.size();
    const char* const syms = g_symbols.c_str();
    for (int i = 0; i < C; ++i) g9_sval[i] = (unsigned char)syms[i];
    const unsigned long long* sval = g9_sval;

    unsigned long long UID1=0,UID1x=0,UID2=0,UID2x=0,UID3=0,UID3x=0,
                       UID4=0,UID4x=0,UID5=0,UID5x=0,UID6=0,UID6x=0;
    std::cout << "[Length 9] Start\n";
    for (int a=0;a<C;++a){ UID1=sval[a]; UID1x=UID1*65599ULL;
    for (int b=0;b<C;++b){                 UID2=UID1x^sval[b]; UID2x=UID2*65599ULL;
    for (int c=0;c<C;++c){                 UID3=UID2x^sval[c]; UID3x=UID3*65599ULL;
    for (int d=0;d<C;++d){                 UID4=UID3x^sval[d]; UID4x=UID4*65599ULL;
        // Precomp base for rc4 at e-level:
        // (UID4x ^ sval[e]) * K65599_4 = (UID4x & ~0xFF)*K65599_4 + g_precomp_K4[(UID4x&0xFF)^sval[e]]
        unsigned long long UID4x_low = UID4x & 0xFFULL;
        unsigned long long base_K4   = (UID4x & ~0xFFULL) * K65599_4;
    for (int e=0;e<C;++e) {
        // rc4 without multiply
        unsigned long long pred4 = base_K4 + g_precomp_K4[UID4x_low ^ sval[e]];
        unsigned k9 = (unsigned)(pred4 >> 55) & 0x1FFu;
        if (!((g_rc4_bits[k9 >> 6] >> (k9 & 63)) & 1u)) continue;

        UID5  = UID4x ^ sval[e];
        UID5x = UID5 * 65599ULL;

        // Precomp base for rc3 at f-level:
        unsigned long long UID5x_low = UID5x & 0xFFULL;
        unsigned long long base_K3   = (UID5x & ~0xFFULL) * K65599_3;

        for (int f=0;f<C;++f) {
            // rc3 pre-filter without multiply
            unsigned long long pred3 = base_K3 + g_precomp_K3[UID5x_low ^ sval[f]];
            unsigned k16 = (unsigned)(pred3 >> 48) & 0xFFFFu;
            if (!((g_rc3_pre_bits[k16 >> 6] >> (k16 & 63)) & 1u)) continue;
            // Exact scan
            bool ok = false;
            for (int ti = 0; ti < g_ntargets; ++ti) {
                unsigned long long dd = pred3 - g_targets[ti];
                if (dd < RANGE3 || (0ULL - dd) < RANGE3) { ok = true; break; }
            }
            if (__builtin_expect(!ok, 1)) continue;

            UID6  = UID5x ^ sval[f];
            UID6x = UID6 * 65599ULL;
            generate_9_g(UID6x, a, b, c, d, e, f, syms, C);
        }
    }}}}}
    std::cout << "[Length 9] Finish\n";
}

// ── generate_10 ───────────────────────────────────────────────────────────────
#define PREFIX    syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]<<syms[f]<<syms[g]<<syms[h]
#define LAST_CHAR j
__attribute__((optimize("O3"), target("avx2")))
static void generate_10()
{
    const int C = (int)g_symbols.size();
    const char* const syms = g_symbols.c_str();
    alignas(32) unsigned long long sval[256];
    for (int i = 0; i < C; ++i) sval[i] = (unsigned char)syms[i];

    const __m256i MASK4095 = _mm256_set1_epi64x(4095);
    const __m256i MASK63   = _mm256_set1_epi64x(63);
    const __m256i ONE      = _mm256_set1_epi64x(1);

    unsigned long long UID1=0,UID1x=0,UID2=0,UID2x=0,UID3=0,UID3x=0,
                       UID4=0,UID4x=0,UID5=0,UID5x=0,UID6=0,UID6x=0,
                       UID7=0,UID7x=0,UID8=0,UID8x=0,UID9=0,UID9x=0,UID10=0;
    std::cout << "[Length 10] Start\n";
    for (int a=0;a<C;++a){ UID1=sval[a];  UID1x=UID1*65599ULL;
    for (int b=0;b<C;++b){                 UID2=UID1x^sval[b];  UID2x=UID2*65599ULL;
    for (int c=0;c<C;++c){                 UID3=UID2x^sval[c];  UID3x=UID3*65599ULL;
    for (int d=0;d<C;++d){                 UID4=UID3x^sval[d];  UID4x=UID4*65599ULL;
    for (int e=0;e<C;++e){                 UID5=UID4x^sval[e];  UID5x=UID5*65599ULL;
    for (int f=0;f<C;++f){                 UID6=UID5x^sval[f];
        if (__builtin_expect(!range_check_4(UID6), 0)) continue;
        UID6x=UID6*65599ULL;
    for (int g=0;g<C;++g){                 UID7=UID6x^sval[g];
        if (__builtin_expect(!range_check_3(UID7), 1)) continue;
        UID7x=UID7*65599ULL;
    for (int h=0;h<C;++h){ UID8=UID7x^sval[h]; UID8x=UID8*65599ULL;
        __m256i uid8x_v = _mm256_set1_epi64x((long long)UID8x);
        int ii = 0;
        for (; ii+11 < C; ii += 12) {
            __m256i uid9ax = mul65599_v(_mm256_xor_si256(uid8x_v, _mm256_load_si256((const __m256i*)&sval[ii])));
            __m256i uid9bx = mul65599_v(_mm256_xor_si256(uid8x_v, _mm256_load_si256((const __m256i*)&sval[ii+4])));
            __m256i uid9cx = mul65599_v(_mm256_xor_si256(uid8x_v, _mm256_load_si256((const __m256i*)&sval[ii+8])));
#undef LAST_CHAR
            H12_LOOP(uid9ax, uid9bx, uid9cx, ii, UID8x)
#define LAST_CHAR j
        }
        for (; ii+7 < C; ii += 8) {
            __m256i uid9ax = mul65599_v(_mm256_xor_si256(uid8x_v, _mm256_load_si256((const __m256i*)&sval[ii])));
            __m256i uid9bx = mul65599_v(_mm256_xor_si256(uid8x_v, _mm256_load_si256((const __m256i*)&sval[ii+4])));
#undef LAST_CHAR
            H8_LOOP(uid9ax, uid9bx, ii, UID8x)
#define LAST_CHAR j
        }
        for (; ii+3 < C; ii += 4) {
            __m256i uid9x = mul65599_v(_mm256_xor_si256(uid8x_v, _mm256_load_si256((const __m256i*)&sval[ii])));
            for (int j = 0; j < C; ++j) {
                __m256i uid10 = _mm256_xor_si256(uid9x, _mm256_set1_epi64x((long long)sval[j]));
                __m256i hits; BLOOM4(uid10, hits);
                if (__builtin_expect(!_mm256_testz_si256(hits, hits), 0)) {
                    int ah=_mm256_movemask_epi8(_mm256_cmpeq_epi64(hits,ONE));
                    EXTR_CHKF(ah,0x000000FF,uid10,0,ii,0) EXTR_CHKF(ah,0x0000FF00,uid10,1,ii,1)
                    EXTR_CHKF(ah,0x00FF0000,uid10,2,ii,2) EXTR_CHKF(ah,0xFF000000,uid10,3,ii,3)
                }
            }
        }
        for (; ii < C; ++ii){ UID9=UID8x^sval[ii]; UID9x=UID9*65599ULL;
            for (int j=0;j<C;++j){ UID10=UID9x^sval[j]; CHECK(UID10, PREFIX<<syms[ii]<<syms[j]) }
        }
    }}}}}}}}
    std::cout << "[Length 10] Finish\n";
}
#undef PREFIX
#undef LAST_CHAR

// ── generate_11 ───────────────────────────────────────────────────────────────
#define PREFIX    syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]<<syms[f]<<syms[g]<<syms[h]<<syms[ii]
#define LAST_CHAR k
__attribute__((optimize("O3"), target("avx2")))
static void generate_11()
{
    const int C = (int)g_symbols.size();
    const char* const syms = g_symbols.c_str();
    alignas(32) unsigned long long sval[256];
    for (int i = 0; i < C; ++i) sval[i] = (unsigned char)syms[i];

    const __m256i MASK4095 = _mm256_set1_epi64x(4095);
    const __m256i MASK63   = _mm256_set1_epi64x(63);
    const __m256i ONE      = _mm256_set1_epi64x(1);

    unsigned long long UID1=0,UID1x=0,UID2=0,UID2x=0,UID3=0,UID3x=0,
                       UID4=0,UID4x=0,UID5=0,UID5x=0,UID6=0,UID6x=0,
                       UID7=0,UID7x=0,UID8=0,UID8x=0,UID9=0,UID9x=0,
                       UID10=0,UID10x=0,UID11=0;
    std::cout << "[Length 11] Start\n";
    for (int a=0;a<C;++a){ UID1=sval[a];   UID1x=UID1*65599ULL;
    for (int b=0;b<C;++b){                 UID2=UID1x^sval[b];  UID2x=UID2*65599ULL;
    for (int c=0;c<C;++c){                 UID3=UID2x^sval[c];  UID3x=UID3*65599ULL;
    for (int d=0;d<C;++d){                 UID4=UID3x^sval[d];  UID4x=UID4*65599ULL;
    for (int e=0;e<C;++e){                 UID5=UID4x^sval[e];  UID5x=UID5*65599ULL;
    for (int f=0;f<C;++f){                 UID6=UID5x^sval[f];  UID6x=UID6*65599ULL;
    for (int g=0;g<C;++g){                 UID7=UID6x^sval[g];
        if (!range_check_4(UID7)) continue;
        UID7x=UID7*65599ULL;
    for (int h=0;h<C;++h){                 UID8=UID7x^sval[h];
        if (!range_check_3(UID8)) continue;
        UID8x=UID8*65599ULL;
    for (int ii=0;ii<C;++ii){ UID9=UID8x^sval[ii]; UID9x=UID9*65599ULL;
        __m256i uid9x_v = _mm256_set1_epi64x((long long)UID9x);
        int jj = 0;
        for (; jj+11 < C; jj += 12) {
            __m256i uid10ax = mul65599_v(_mm256_xor_si256(uid9x_v, _mm256_load_si256((const __m256i*)&sval[jj])));
            __m256i uid10bx = mul65599_v(_mm256_xor_si256(uid9x_v, _mm256_load_si256((const __m256i*)&sval[jj+4])));
            __m256i uid10cx = mul65599_v(_mm256_xor_si256(uid9x_v, _mm256_load_si256((const __m256i*)&sval[jj+8])));
#undef LAST_CHAR
            H12_LOOP(uid10ax, uid10bx, uid10cx, jj, UID9x)
#define LAST_CHAR k
        }
        for (; jj+7 < C; jj += 8) {
            __m256i uid10ax = mul65599_v(_mm256_xor_si256(uid9x_v, _mm256_load_si256((const __m256i*)&sval[jj])));
            __m256i uid10bx = mul65599_v(_mm256_xor_si256(uid9x_v, _mm256_load_si256((const __m256i*)&sval[jj+4])));
#undef LAST_CHAR
            H8_LOOP(uid10ax, uid10bx, jj, UID9x)
#define LAST_CHAR k
        }
        for (; jj+3 < C; jj += 4) {
            __m256i uid10x = mul65599_v(_mm256_xor_si256(uid9x_v, _mm256_load_si256((const __m256i*)&sval[jj])));
            for (int k = 0; k < C; ++k) {
                __m256i uid11 = _mm256_xor_si256(uid10x, _mm256_set1_epi64x((long long)sval[k]));
                __m256i hits; BLOOM4(uid11, hits);
                if (__builtin_expect(!_mm256_testz_si256(hits, hits), 0)) {
                    int ah=_mm256_movemask_epi8(_mm256_cmpeq_epi64(hits,ONE));
                    EXTR_CHKF(ah,0x000000FF,uid11,0,jj,0) EXTR_CHKF(ah,0x0000FF00,uid11,1,jj,1)
                    EXTR_CHKF(ah,0x00FF0000,uid11,2,jj,2) EXTR_CHKF(ah,0xFF000000,uid11,3,jj,3)
                }
            }
        }
        for (; jj < C; ++jj){ UID10=UID9x^sval[jj]; UID10x=UID10*65599ULL;
            for (int k=0;k<C;++k){ UID11=UID10x^sval[k]; CHECK(UID11, PREFIX<<syms[jj]<<syms[k]) }
        }
    }}}}}}}}}
    std::cout << "[Length 11] Finish\n";
}
#undef PREFIX
#undef LAST_CHAR

// ── generate_12 ───────────────────────────────────────────────────────────────
#define PREFIX    syms[a]<<syms[b]<<syms[c]<<syms[d]<<syms[e]<<syms[f]<<syms[g]<<syms[h]<<syms[ii]<<syms[jj]
#define LAST_CHAR l
__attribute__((optimize("O3"), target("avx2")))
static void generate_12()
{
    const int C = (int)g_symbols.size();
    const char* const syms = g_symbols.c_str();
    alignas(32) unsigned long long sval[256];
    for (int i = 0; i < C; ++i) sval[i] = (unsigned char)syms[i];

    const __m256i MASK4095 = _mm256_set1_epi64x(4095);
    const __m256i MASK63   = _mm256_set1_epi64x(63);
    const __m256i ONE      = _mm256_set1_epi64x(1);

    unsigned long long UID1=0,UID1x=0,UID2=0,UID2x=0,UID3=0,UID3x=0,
                       UID4=0,UID4x=0,UID5=0,UID5x=0,UID6=0,UID6x=0,
                       UID7=0,UID7x=0,UID8=0,UID8x=0,UID9=0,UID9x=0,
                       UID10=0,UID10x=0,UID11=0,UID11x=0,UID12=0;
    std::cout << "[Length 12] Start\n";
    for (int a=0;a<C;++a){  UID1=sval[a];   UID1x=UID1*65599ULL;
    for (int b=0;b<C;++b){                   UID2=UID1x^sval[b];  UID2x=UID2*65599ULL;
    for (int c=0;c<C;++c){                   UID3=UID2x^sval[c];  UID3x=UID3*65599ULL;
    for (int d=0;d<C;++d){                   UID4=UID3x^sval[d];  UID4x=UID4*65599ULL;
    for (int e=0;e<C;++e){                   UID5=UID4x^sval[e];  UID5x=UID5*65599ULL;
    for (int f=0;f<C;++f){                   UID6=UID5x^sval[f];  UID6x=UID6*65599ULL;
    for (int g=0;g<C;++g){                   UID7=UID6x^sval[g];  UID7x=UID7*65599ULL;
    for (int h=0;h<C;++h){                   UID8=UID7x^sval[h];
        if (!range_check_4(UID8)) continue;
        UID8x=UID8*65599ULL;
    for (int ii=0;ii<C;++ii){                UID9=UID8x^sval[ii];
        if (!range_check_3(UID9)) continue;
        UID9x=UID9*65599ULL;
    for (int jj=0;jj<C;++jj){ UID10=UID9x^sval[jj]; UID10x=UID10*65599ULL;
        __m256i uid10x_v = _mm256_set1_epi64x((long long)UID10x);
        int kk = 0;
        for (; kk+11 < C; kk += 12) {
            __m256i uid11ax = mul65599_v(_mm256_xor_si256(uid10x_v, _mm256_load_si256((const __m256i*)&sval[kk])));
            __m256i uid11bx = mul65599_v(_mm256_xor_si256(uid10x_v, _mm256_load_si256((const __m256i*)&sval[kk+4])));
            __m256i uid11cx = mul65599_v(_mm256_xor_si256(uid10x_v, _mm256_load_si256((const __m256i*)&sval[kk+8])));
#undef LAST_CHAR
            H12_LOOP(uid11ax, uid11bx, uid11cx, kk, UID10x)
#define LAST_CHAR l
        }
        for (; kk+7 < C; kk += 8) {
            __m256i uid11ax = mul65599_v(_mm256_xor_si256(uid10x_v, _mm256_load_si256((const __m256i*)&sval[kk])));
            __m256i uid11bx = mul65599_v(_mm256_xor_si256(uid10x_v, _mm256_load_si256((const __m256i*)&sval[kk+4])));
#undef LAST_CHAR
            H8_LOOP(uid11ax, uid11bx, kk, UID10x)
#define LAST_CHAR l
        }
        for (; kk+3 < C; kk += 4) {
            __m256i uid11x = mul65599_v(_mm256_xor_si256(uid10x_v, _mm256_load_si256((const __m256i*)&sval[kk])));
            for (int l = 0; l < C; ++l) {
                __m256i uid12 = _mm256_xor_si256(uid11x, _mm256_set1_epi64x((long long)sval[l]));
                __m256i hits; BLOOM4(uid12, hits);
                if (__builtin_expect(!_mm256_testz_si256(hits, hits), 0)) {
                    int ah=_mm256_movemask_epi8(_mm256_cmpeq_epi64(hits,ONE));
                    EXTR_CHKF(ah,0x000000FF,uid12,0,kk,0) EXTR_CHKF(ah,0x0000FF00,uid12,1,kk,1)
                    EXTR_CHKF(ah,0x00FF0000,uid12,2,kk,2) EXTR_CHKF(ah,0xFF000000,uid12,3,kk,3)
                }
            }
        }
        for (; kk < C; ++kk){ UID11=UID10x^sval[kk]; UID11x=UID11*65599ULL;
            for (int l=0;l<C;++l){ UID12=UID11x^sval[l]; CHECK(UID12, PREFIX<<syms[kk]<<syms[l]) }
        }
    }}}}}}}}}}
    std::cout << "[Length 12] Finish\n";
}
#undef PREFIX
#undef LAST_CHAR

// ── Dictionary method ─────────────────────────────────────────────────────────
// Same idea as Dumb_Dictionary_method in the old UID_Dehasher: hash every word
// in dictionary.txt with MakeUID and check it against the loaded UIDs. Runs
// before brute force so any word already in the corpus is caught instantly.
static inline unsigned long long make_uid(const char* s)
{
    unsigned long long h = 0;
    for (; *s; ++s) h = h * 65599ULL ^ (unsigned char)*s;   // MakeUID recurrence
    return h;
}

static void generate_dictionary(const char* path)
{
    std::ifstream f(path);
    if (!f) { std::cout << "Cannot open " << path << " — skipping dictionary.\n\n"; return; }

    std::cout << "[Dictionary] Start\n";
    std::string word;
    size_t lines = 0;
    while (std::getline(f, word)) {
        if (!word.empty() && word.back() == '\r') word.pop_back();
        ++lines;
        if (word.empty()) continue;
        unsigned long long uid = make_uid(word.c_str());
        if (bloom_check(uid) && ht_find_erase(uid)) report_dehash(uid, word);
        if (g_ht_count == 0) break;
    }
    std::cout << "[Dictionary] Finish — " << lines << " words scanned, "
              << g_ht_count << " UIDs remaining\n\n";
}

int main()
{
    if (!read_settings("settings.txt"))
    { std::cerr << "Error: settings.txt missing or invalid.\n"; return 1; }

    load_uids("uids.txt");
    precompute_range_bitmaps();

    std::cout << "Symbols    : " << g_symbols << "\n";
    std::cout << "Max length : " << g_max_length << "\n";
    std::cout << "UIDs loaded: " << g_ht_count << "\n\n";
    if (g_ht_count == 0) { std::cout << "No UIDs to dehash.\n"; return 0; }

    generate_dictionary("dictionary.txt");
    if (g_ht_count == 0) { std::cout << "All UIDs dehashed by dictionary.\n"; return 0; }

    if (g_max_length >= 4)  generate_4();
    if (g_max_length >= 5)  generate_5();
    if (g_max_length >= 6)  generate_6();
    if (g_max_length >= 7)  generate_7();
    if (g_max_length >= 8)  generate_8();
    if (g_max_length >= 9)  generate_9();
    if (g_max_length >= 10) generate_10();
    if (g_max_length >= 11) generate_11();
    if (g_max_length >= 12) generate_12();
    return 0;
}


 
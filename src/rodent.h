// REGEX to count all the lines under MSVC 13: ^(?([^\r\n])\s)*[^\s+?/]+[^\n]*$

// VS RODENT IV:
// 45,1% - baseline
// 46,9% - no continuation
// 46,8 - FAIL hist inc = (depth-1)*(depth-1)
// 48,8% out of 1000 games
// 49,2% out of 2200 games (v1.101, passer eval)
// 50,1% out of 1000 games (v1.108, no futility pruning)
// 52,4% out of 1600 games (v1.112, masive tuning, mainly pawn params) + 16 Elo vs Rodent IV
// 53,0% out of 1200 games (v1.113, king's indian pawn center) + 22 Elo vs Rodent IV
// 54,7% out of 1800 games (v1.114, better time control) +32 Elo vs Rodent IV
// 52,9% out of 800 games  (v1.114, again but Rodent IV got futility pruning removed)
// 54,5% out of 900 games  (v1.115, pawn patterns)
// 54,8% out of 900 games  (v1.116, 2nd layer od checks in qs) +34 Elo vs Rodent IV
// 54,9% out of 700 games  (v1.117, more tactically oriented search) +34 Elo vs Rodent IV
// 55,2% out of 1000 games (v1.118, pawn eval speedup and weights at 100 
// 56,0% out of 1000 games (v1.119, pawn x pawn table) +42 Elo vs Rodent IV

// info depth 20 time 7828 nodes 11063324 nps 1413301 score cp 27 pv g1f3 d7d5 d2d4 e7e6 c2c4 c7c5 c4d5 e6d5 b1c3 g8f6 c1g5 f8e7 d4c5 e8g8 e2e3 b8c6 f1e2 h7h6 g5f6 e7f6 c3d5 f6b2  thread 1// 
// missing
// - own king proximity increases passers value
// - history not updated at depth 1
// - pst rebalancing algorithm
// - recapture extension
// - escapes from captures refuting a null move are sorted higher
// - iid / iir
// - bootstrapping history score at root with pst values scaled according to game phase
// - incrementally updated mateiral key (for each side)
// - history bootstrap discourages moves on squares controlled by enemy pawns
// - extend if null move search returns mate score

//#define USE_TUNING
// 62.349386
// 62.342892
// 62.340426 replacing phalanx
// 62.337884 replacing defended

// TACTICAL TESTS
//
// r2q1r2/1b2bpkp/p3p1p1/2ppP1P1/7R/1PN1BQR1/1PP2P1P/4K3 w - - 0 1 (Pietrzak)
// intermediate goal: 0:26 to Rxh7 returning mate in 8, depth 28
// would get d27 and 0:25 removing lmr of bad captures
// removed futility pruning 0:02
// final goal:
// removed futility pruning and null move: plus score on Qf6!! at depth 23, 8:23, default doesn't get it
//
// 1r3rk1/3bbppp/1qn2P2/p2pP1P1/3P4/2PB1N2/6K1/qNBQ1R2 w - - bm Bxh7+;
//
// 8/8/4kpp1/3p1b2/p6P/2B5/6P1/6K1 b - - 0 1 bm Bh3 (Shirov)

static const int nodeStepPerLevel = 128;
static const int numberOfLevels = 1024;
static const int blurStepPerLevel = 1;

enum eColor{White, Black, NoColor};
enum ePieceType{Pawn, Knight, Bishop, Rook, Queen, King, NO_TP};
enum ePiece{WP, BP, WN, BN, WB, BB, WR, BR, WQ, BQ, WK, BK, NO_PC};
enum eFile {fileA, fileB, fileC, fileD, fileE, fileF, fileG, fileH};
enum eRank {rank1, rank2, rank3, rank4, rank5, rank6, rank7, rank8};
enum eMoveType {NORMAL, CASTLE, EP_CAP, EP_SET, N_PROM, B_PROM, R_PROM, Q_PROM};
enum eHashEntry{NONE, UPPER, LOWER, EXACT};
enum eMoveFlag {MV_NORMAL, MV_HASH, MV_CAPTURE, MV_KILLER, MV_BADCAPT};
enum eOption { O_MATERIAL, O_OWN_ATT, O_OPP_ATT, O_OWN_MOB, O_OPP_MOB, O_OWN_TROP, O_OPP_TROP, O_OWN_PRES, O_OPP_PRES, O_OWN_PAWN, O_OPP_PAWN, N_OF_OPTIONS};
enum eFactor   {F_MAT, F_PST, F_PAWNS, F_PASSERS, F_ATT, F_MOB, F_PRES, F_TROP, F_OUTPOST, F_LINES, F_SHIELD, F_OTHERS, N_OF_FACTORS};
enum eSquare{
  A1, B1, C1, D1, E1, F1, G1, H1,
  A2, B2, C2, D2, E2, F2, G2, H2,
  A3, B3, C3, D3, E3, F3, G3, H3,
  A4, B4, C4, D4, E4, F4, G4, H4,
  A5, B5, C5, D5, E5, F5, G5, H5,
  A6, B6, C6, D6, E6, F6, G6, H6,
  A7, B7, C7, D7, E7, F7, G7, H7,
  A8, B8, C8, D8, E8, F8, G8, H8,
  NoSquare
};

enum SpecialConsideration { UNDEFINED, LOW_KID, HIGH_KID, KS_CASTLE, QS_CASTLE };

typedef unsigned long long Bitboard;

#define MAX_PLY         64
#define MAX_MOVES       256
#define INF             32767
#define MATE            32000
#define MAX_EVAL        29999
#define MAX_INT    2147483646

#define RANK_1_BB       (Bitboard)0x00000000000000FF
#define RANK_2_BB       (Bitboard)0x000000000000FF00
#define RANK_3_BB       (Bitboard)0x0000000000FF0000
#define RANK_4_BB       (Bitboard)0x00000000FF000000
#define RANK_5_BB       (Bitboard)0x000000FF00000000
#define RANK_6_BB       (Bitboard)0x0000FF0000000000
#define RANK_7_BB       (Bitboard)0x00FF000000000000
#define RANK_8_BB       (Bitboard)0xFF00000000000000

static const Bitboard bbRelRank[2][8] = { { RANK_1_BB, RANK_2_BB, RANK_3_BB, RANK_4_BB, RANK_5_BB, RANK_6_BB, RANK_7_BB, RANK_8_BB },
                                          { RANK_8_BB, RANK_7_BB, RANK_6_BB, RANK_5_BB, RANK_4_BB, RANK_3_BB, RANK_2_BB, RANK_1_BB } };

#define FILE_A_BB       (Bitboard)0x0101010101010101
#define FILE_B_BB       (Bitboard)0x0202020202020202
#define FILE_C_BB       (Bitboard)0x0404040404040404
#define FILE_D_BB       (Bitboard)0x0808080808080808
#define FILE_E_BB       (Bitboard)0x1010101010101010
#define FILE_F_BB       (Bitboard)0x2020202020202020
#define FILE_G_BB       (Bitboard)0x4040404040404040
#define FILE_H_BB       (Bitboard)0x8080808080808080

#define DIAG_A1H8_BB    (Bitboard)0x8040201008040201
#define DIAG_A8H1_BB    (Bitboard)0x0102040810204080
#define DIAG_B8H2_BB    (Bitboard)0x0204081020408000

#define bbNotA          (Bitboard)0xfefefefefefefefe // ~FILE_A_BB
#define bbNotH          (Bitboard)0x7f7f7f7f7f7f7f7f // ~FILE_H_BB

#define ShiftNorth(x)   (x<<8)
#define ShiftSouth(x)   (x>>8)
#define ShiftWest(x)    ((x & bbNotA)>>1)
#define ShiftEast(x)    ((x & bbNotH)<<1)
#define ShiftNW(x)      ((x & bbNotA)<<7)
#define ShiftNE(x)      ((x & bbNotH)<<9)
#define ShiftSW(x)      ((x & bbNotA)>>9)
#define ShiftSE(x)      ((x & bbNotH)>>7)

#define MoreThanOne(bb) ( bb & (bb - 1) )

#define SIDE_RANDOM     (~((Bitboard)0))

#define START_POS       "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -"

#define SqBb(x)         ((Bitboard)1 << (x))

#define Cl(x)           ((x) & 1)
#define Tp(x)           ((x) >> 1)
#define Pc(x, y)        (((y) << 1) | (x))

#define File(x)         ((x) & 7)
#define Rank(x)         ((x) >> 3)
#define Sq(x, y)        (((y) << 3) | (x))

#define Abs(x)          ((x) > 0 ? (x) : -(x))
#define Max(x, y)       ((x) > (y) ? (x) : (y))
#define Min(x, y)       ((x) < (y) ? (x) : (y))
#define Map0x88(x)      (((x) & 7) | (((x) & ~7) << 1))
#define Unmap0x88(x)    (((x) & 7) | (((x) & ~7) >> 1))
#define Sq0x88Off(x)    ((unsigned)(x) & 0x88)

#define Fsq(x)          ((x) & 63)
#define Tsq(x)          (((x) >> 6) & 63)
#define MoveType(x)     ((x) >> 12)
#define IsProm(x)       ((x) & 0x4000)
#define PromType(x)     (((x) >> 12) - 3)

#define Opp(x)          ((x) ^ 1)

#define InCheck(p)      Attacked(p, KingSq(p, p->side), Opp(p->side))
#define Illegal(p)      Attacked(p, KingSq(p, Opp(p->side)), p->side)
#define MayNull(p)      (((p)->cl_bb[(p)->side] & ~((p)->tp_bb[Pawn] | (p)->tp_bb[King])) != 0)

#define TpOnSq(p, x)    (Tp((p)->pc[x]))
#define KingSq(p, x)    ((p)->king_sq[x])

#define RelSq(sq,cl)   ( sq ^ (cl * 56) )
#define RelSqBb(sq,cl)  ( SqBb(RelSq(sq,cl) ) )

#define EVAL_HASH_SIZE 512*512
#define PAWN_HASH_SIZE 256*256

extern int progSide;

typedef struct {
  int ttp;
  int castle_flags;
  int ep_sq;
  int rev_moves;
  Bitboard hash_key;
  Bitboard pawn_key;
} UNDO;

Bitboard Paint(int s);
Bitboard Paint(int s1, int s2);
Bitboard Paint(int s1, int s2, int s3);
Bitboard ShiftFwd(Bitboard b, int c);
Bitboard FwdOf(Bitboard bitboard, int color);

class Position{
public:
  Bitboard cl_bb[2];
  Bitboard tp_bb[6];
  int pc[64];
  int king_sq[2];
  int cnt[2][6];
  int phase;
  int side;
  int castle_flags;
  int ep_sq;
  int rev_moves;
  int head;
  Bitboard hash_key;
  Bitboard pawn_key;
  Bitboard rep_list[256];

  Bitboard GetPawns(int sd) { return (cl_bb[sd] & tp_bb[Pawn]); }
  Bitboard GetKnights(int sd) { return cl_bb[sd] & tp_bb[Knight]; }
  Bitboard GetBishops(int sd) { return cl_bb[sd] & tp_bb[Bishop]; }
  Bitboard GetRooks(int sd) { return cl_bb[sd] & tp_bb[Rook]; }
  Bitboard GetQueens(int sd) { return cl_bb[sd] & tp_bb[Queen]; }
  Bitboard GetKings(int sd) { return cl_bb[sd] & tp_bb[King]; }

  void DoMove(int move, UNDO * u);
  void DoNull(UNDO * u);
  void UndoMove(int move, UNDO * u);
  void UndoNull(UNDO * u);
  int NonPawnCnt(int side) { return MinorCnt(side) + MajorCnt(side);};
  int MinorCnt(int side) { return cnt[side][Knight] + cnt[side][Bishop]; };
  int MajorCnt(int side) { return cnt[side][Rook] + cnt[side][Queen]; };
  int AllPawnCnt() { return cnt[White][Pawn] + cnt[Black][Pawn]; };
  Bitboard Empty() { return ~Filled(); };
  Bitboard Filled() { return cl_bb[White] | cl_bb[Black]; };
  Bitboard Map(int side, int piece) { return cl_bb[side] & tp_bb[piece]; }
  Bitboard MapType(int t) { return tp_bb[t]; };
  Bitboard MapDiag() { return tp_bb[Bishop] | tp_bb[Queen]; }
  Bitboard MapStraight() { return tp_bb[Rook] | tp_bb[Queen]; }
  bool IsOnSq(int side, int pc, int sq) { return (Paint(sq) & (cl_bb[side] & tp_bb[pc])); }
  bool IsEmpty(int sq) { return (Filled() & Paint(sq) == 0); }
  bool PawnComplex(int c, int s1, int s2) { return (IsOnSq(c, Pawn, s1) && IsOnSq(c, Pawn, s2)); }
  bool PawnComplex(int c, int s1, int s2, int s3) { return (IsOnSq(c, Pawn, s1) && IsOnSq(c, Pawn, s2) && IsOnSq(c, Pawn, s3));}

  void Copy(Position* oldPos);

};

typedef struct {
    Position* p;
    int phase;
    int trans_move;
    int killer1;
    int killer2;
    int refutation;
    int* next;
    int* last;
    int move[MAX_MOVES];
    int value[MAX_MOVES];
    int* badp;
    int bad[MAX_MOVES];
} MOVES;

struct sEvalHashEntry {
    Bitboard key;
    int score;
};

struct sPawnHashEntry {
    Bitboard key;
    int mg_pawns[2];
    int eg_pawns[2];
    int shield[2];
};

#ifdef USE_TUNING

#include <cstdint>
#include <cinttypes>
#include <string>

class cTuner {
public:
    int adjust[64];
    int addition[2][64];
    int secretIngredient;
    int otherIngredient;
    int cnt10;
    int cnt01;
    int cnt05;
    std::string epd10[10000000];
    std::string epd01[10000000];
    std::string epd05[10000000];

    void Init();
    void FitRound();
    double TexelFit(Position* p, int* pv);
    double TexelSigmoid(int score, double k);
};

extern cTuner Tuner;

#endif

// bitgen

class cAttacks {
private:
    Bitboard pAtt[2][64];
    Bitboard nAtt[64];
    Bitboard kAtt[64];
    Bitboard between[64][64];
    Bitboard SetBetween(int s1, int s2);
public:
    void Init(void);
    Bitboard bAttOnEmpty[64];
    Bitboard rAttOnEmpty[64];
    Bitboard Pawn(int c, int s);
    Bitboard Knight(int s);
    Bitboard Bish(Bitboard o, int s);
    Bitboard Rook(Bitboard o, int s);
    Bitboard Queen(Bitboard o, int s);
    Bitboard King(int s);
    Bitboard GetBetween(int s1, int s2);
    bool SameRankOrFile(int s1, int s2);
    bool SameDiag(int s1, int s2);
};

extern cAttacks Att;

class EvalData {
public:
    bool isKID[2];
    //int consideration[2];
    Bitboard control[2][6];
    Bitboard bbPawnCanTake[2];
    Bitboard dbl_control[2];
    int mg[2][N_OF_FACTORS];
    int eg[2][N_OF_FACTORS];
    int att[2];
    Bitboard NonKingAtt(int c) { return control[c][Pawn] | control[c][Knight] | control[c][Bishop] | control[c][Rook] | control[c][Queen]; }
    Bitboard AllAtt(Position* p, int c) { return NonKingAtt(c) | Att.King(p->king_sq[c]); }
};

class Engine {
public:

    bool isMain;
    int depthReached;
    int cutoffHistory[12][64];
    int triesHistory[12][64];
    int killer[MAX_PLY][2];
    int refutation[64][64];
    sEvalHashEntry EvalTT[EVAL_HASH_SIZE];
    sPawnHashEntry PawnTT[PAWN_HASH_SIZE];
    int oldEval[MAX_PLY]; // static eval for ech ply
    int oldMove[MAX_PLY];

    void ClearEvalHash(void);
    void SetTimingData(Position* p, int move, int depth, int *pv);
    int Perft(Position* p, int ply, int depth);
    int Widen(Position* p, int depth, int* pv, int lastScore);
    int Search(Position* p, int ply, int alpha, int beta, int depth, bool isExcluded, int was_null, int* pv);
    int Quiesce(Position* p, int ply, int alpha, int beta, int* pv);
    int QuiesceFlee(Position* p, int ply, int alpha, int beta, int* pv);
    int QuiesceChecks(Position* p, int ply, int alpha, int beta, int* pv);
    int QuiesceChecks2(Position* p, int ply, int alpha, int beta, int* pv);
    int Evaluate(Position* p, EvalData* e, int use_hash); // uses thread-dependent eval hash
    void PawnKingEval(Position* p, EvalData* e); // uses thread-dependent pawn hash

    // movegen

    void ScoreQuiet(MOVES* m);
    void InitMoves(Position* p, MOVES* m, int trans_move, int refutation, int ply);
    int NextMove(MOVES* m, int* flag);
    int NextCapture(MOVES* m);
    int NextCaptureOrCheck(MOVES* m, int* flag);
    void InitCaptures(Position* p, MOVES* m);
    void ScoreCaptures(MOVES*);

    // history heuristics

    void ClearHist(void);
    void UpdateHistory(Position* p, int lastMove, int move, int depth, int ply);
    void UpdateTried(Position* p, int move, int depth);
    int HistInc(int depth);
    int GetHistScore(Position* p, int move);
    void Trim();
};

extern Engine mainEngine;
extern Engine helpEngine;

class cMask {
public:
    void Init();
    Bitboard f[8];
    Bitboard r[8];
    Bitboard rr[2][8];
    Bitboard home[2];
    Bitboard away[2];
    Bitboard outpost[2];
    Bitboard adjacent[8];
    Bitboard passed[2][64];
    Bitboard support[2][64];
    Bitboard space[2];
    Bitboard sqColor[2];
    Bitboard ksCastle[2];
    Bitboard qsCastle[2];
    Bitboard centralFile;
    Bitboard kingside;
    Bitboard queenside;
    Bitboard rim;
};

extern cMask Mask;

class cDistance {
public:
    int grid[64][64];
    int cheb[64][64];
    int bonus[64][64];
    int diagDist[64][64];
    int qTropismMg[64][64];
    int rTropismMg[64][64];
    int bTropismMg[64][64];
    int nTropismMg[64][64];
    void Init(void);
};

extern cDistance Dist;

class cPst {
public:
    int mgKs[2][6][64];
    int mgQs[2][6][64];
    int mgOne[2][6][64];
    int mgKidLow[2][6][64];
    int mgKidHigh[2][6][64];
    int egOne[2][6][64];
    int mgPasser[2][64];
    int egPasser[2][64];
    int mgBackward[2][64];
    int mgPhalanx[2][64];
    int egPhalanx[2][64];
    int mgDefended[2][64];
    int egDefended[2][64];
    int mgShieldedB[2][64];
    int mgShieldedN[2][64];
    int rConMg[2][64];
    int rConEg[2][64];
    int pawnRelationshipMg[2][64][64];
    int pawnRelationshipEg[2][64][64];
    void Init(void);
    void AddPawnRelation(int s1, int s2, int mgVal, int egVal);
};

extern cPst Pst;

class cDanger {
public:
    int tab[512];
    void Init(int attStep, int attCap);
};

extern cDanger Danger;

class cLMR {
public:
    double table[2][MAX_PLY][MAX_MOVES];
    void Init();
};

extern cLMR LMR;

typedef struct {
  Bitboard key;
  short date;
  short move;
  short score;
  unsigned char flags;
  unsigned char depth;
} ENTRY;

// bitboard

Bitboard Paint(int s);
Bitboard Paint(int s1, int s2);
Bitboard Paint(int s1, int s2, int s3);
Bitboard FrontSpan(Bitboard bitboard, int color);
Bitboard SidesOf(Bitboard bb);
Bitboard GetWPControl(Bitboard bb);
Bitboard GetBPControl(Bitboard bb);
Bitboard GetDoubleWPControl(Bitboard bb);
Bitboard GetDoubleBPControl(Bitboard bb);

// gen

int* GenerateChecks(Position* p, int* list);
int* GenerateCaptures(Position* p, int* list);
int* GenerateQuiet(Position* p, int* list);
bool CanDiscoverCheck(Position* p, Bitboard checkers, int  oppo, int fromSquare);
int* SerializeMoves(int* list, Bitboard moves, int from);
int CreateMove(int from, int to, int flag);
int CreateMove(int from, int to);

void Add(EvalData *e, int sd, int factor, int mg_bonus, int eg_bonus);
void AddMg(EvalData* e, int sd, int factor, int mg_bonus);
void AllocTrans(int mbsize);
int Attacked(Position *p, int sq, int side);
Bitboard AttacksFrom(Position *p, int sq);
Bitboard AttacksTo(Position *p, int sq);
bool IsBadCapture(Position *p, int move);
void Bench(int depth);
void BuildPv(int *dst, int *src, int move);
void CheckForTimeout(void);
void ClearTrans(void);
void DisplayPv(int score, int *pv, int t);
void EvaluateKing(Position *p, EvalData *e, int sd);
int EvalKingFile(Position * p, int sd, Bitboard bbFile);
int EvalFileShelter(Bitboard bbOwnPawns, int sd);
int EvalFileStorm(Bitboard bbOppPawns, int sd);
void EvaluatePieces(Position *p, EvalData *e, int sd);
void EvaluatePawns(Position * p, EvalData *e, int sd);
void EvaluatePassers(Position* p, EvalData *e, int sd);
Bitboard FillNorth(Bitboard bb);
Bitboard FillSouth(Bitboard bb);
int FirstOne(Bitboard b);
int GetMS(void);

int GetDrawFactor(Position *p, int sd);
bool HashAllowsNullMove(Bitboard hash, int alpha, int beta, int depth, int ply);

void Init(void);
void InitWeights(void);
void InitOptions(void);
int InputAvailable(void);
Bitboard InitHashKey(Position * p);
Bitboard InitPawnKey(Position * p);
bool KPKdraw(Position* p, int sd);
int Legal(Position *p, int move);
void MoveToStr(int move, char *move_str);
int MvvLva(Position *p, int move);
void ParseGo(Position *, char *);
void ParseMoves(Position *p, char *ptr);
void ParsePosition(Position *, char *);
void ParseSetoption(char *);
void PrintBoard(Position *p);
void PrintEval(Position *p);
char *ParseToken(char *, char *);
int PopCnt(Bitboard);
int PopFirstBit(Bitboard * bb);
void PvToStr(int *, char *);
Bitboard Random64(void);
void ReadLine(char *str, int n);
void ResetEngine(void);
bool IsDraw(Position * p);
int SelectBest(MOVES *m);
void SetPosition(Position *p, char *epd);
int StrToMove(Position *p, char *move_str);
int Swap(Position *p, int from, int to);
int Timeout(void);
int TransRetrieve(Bitboard key, int *move, int *score, int *flag, int alpha, int beta, int depth, int ply);
int TransRetrieveMove(Bitboard key, int* move);
void TransStore(Bitboard key, int move, int score, int flags, int depth, int ply);
void UciLoop(void);
void SetCaptureSquare(Position* p, int move, int ply);
int CheckmateHelper(Position* p);

extern int engineLevel;
extern int evalBlur;
extern int castle_mask[64];
extern const int bit_table[64];
extern const int passed_bonus[2][8];
extern const int tp_value[7];
extern const int phase_value[7];
extern int cutoffHistory[12][64];
extern int triesHistory[12][64];
extern int killer[MAX_PLY][2];
extern int refutation[64][64];
extern Bitboard pieceKey[12][64];
extern Bitboard castleKey[16];
extern Bitboard enPassantKey[8];
extern int pondering;
extern int root_depth;
extern Bitboard nodes;
extern int abortSearch;
extern int abortThread;
extern ENTRY *tt;
extern int tt_size;
extern int tt_mask;
extern int tt_date;
extern int options[N_OF_OPTIONS];
extern int weights[2][N_OF_FACTORS];
extern int lastTargetSquare;
extern int lastVictim;

void Think(Position* p, int* pv);
void SetStrength();
void Iterate(Position* p, int* pv);
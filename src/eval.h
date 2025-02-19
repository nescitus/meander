// 0.063087
// 0.062991 n run
// 0.062943 b mg run
// 0.062599 pawns + passers run (+30 Elo)
// 0.062500 phalanx/defended pawns
// 0.062468 mobility
// 0.062369 pawns pst split according to king's position (kingside, queenside, the rest)

const int mg_value[7] = {
   94, 370, 380, 545, 1160, 0, 0
};

const int eg_value[7] = {
  113, 330, 343, 640, 1190, 0, 0
};

const int bPairMg = 44;
const int bPairEg = 55;
const int exchange = 24;
const int minorUp = 38;
const int minors2 = 20;
const int pawns2 = 16;

const int nMobMg[9] =  { -25, -19,  -9,  -2,   6,  11,  13,  13, };
const int nMobEg[9] =  { -25, -20, -11,  -1,   4,   9,  11,  13, };
const int bMobMg[14] = { -24, -20, -14,  -4,   2,   7,  10,  15,  17,  19,  20,  21,  22,  17, };
const int bMobEg[14] = { -23, -19, -14,  -9,  -4,   1,   9,  12,  14,  15,  15,  15,  15,  15, };
const int rMobMg[15] = { -14, -12, -10,  -8,  -6,  -4,  -2,   0,   2,   4,   6,   8,  10,  12,  14 };
const int rMobEg[15] = { -28, -24, -20, -16, -12,  -8,  -4,   0,   4,   8,  12,  16,  20,  24,  28 };
const int qMobMg[28] = { -5,  -4,  -3,  -2,  -1,   +0,  +1,  +2,  +3,  +4,  +5,  +6,  +7,  +8,  +9, +10, +11, +12, +13, +14, +15, +16, +17, +18, +19, +20, +21, +22, };
const int qMobEg[28] = { -24, -17, -11,  -7,  -3,  +0,  +2,  +4,  +6,  +8, +10, +12, +14, +16, +18, +20, +22, +24, +26, +28, +30, +32, +34, +36, +38, +40, +42, +44, };

const int chainBase = 12;
const int chainSt0 = 6;
const int chainSt1 = 12;
const int chainSt2 = 32;
const int chainStBad = -32;

const int phalanxPasser = 6;
const int blockedPasser = -13;
const int stopSquareOwn = 32;
const int stopSquareOpp = -34;
const int defendedPasser = 2;

const int knightAttack = 7;
const int knightCheck = 14;
const int safeBishAttack = 8;
const int unsafeBishAttack = 4;
const int bishCheck = 20;
const int safeRookAttack = 12;
const int unsafeRookAttack = 4;
const int rookCheck = 18;
const int safeQueenAttack = 15;
const int unsafeQueenAttack = 5;
const int queenCheck = 12;
const int queenContactCheck = 32;
const int noLuftMg = -11;
const int noLuftEg = -15;

const int pawnOnBColor = 4;

const int hangingMg[7] = { 2, 21, 21, 25, 41, 0, 0 };
const int hangingEg[7] = { 4, 28, 28, 33, 49, 0, 0 };

const int looseMg[7] = { 0, 10, 10, 10, 10, 0, 0 };
const int looseEg[7] = { 0, 10, 10, 10, 10, 0, 0 };

int NattacksBMg = 28;
int NattacksBEg = 24;
int BattacksNMg = 20;
int BattacksNEg = 20;
int RattacksNMg = 9;
int RattacksNEg = 8;

int isolPawnMg = -11;
int isolPawnEg = -19;
int isolOpenMg = -10;

int bishPotentialMg = 4; // potential outposts
int bishPotentialEg = 0;
int bishRestrictedMg = -7;
int bishRestrictedEg = -5;
int bTrappedA2 = -99;
int bTrappedA3 = -25;
const int blockedFianchettoMg = -5;
const int blockedFianchettoEg = -5;

const Bitboard kMask[2] = { Paint(F1, G1), Paint(F8, G8) };
const Bitboard krMask[2] = { Paint(G1, H1, H2), Paint(G8, H8, H7) };
const Bitboard qMask[2] = { Paint(C1, B1), Paint(C8, B8) };
const Bitboard qrMask[2] = { Paint(B1, A1, A2), Paint(B8, A8, A7) };

const int trappedRookMg = -35;
const int trappedRookEg = -35;

static const int shield[64] = {

  0,    0,   0,   0,   0,   0,   0,   0,
  2,    2,   2,   2,   2,   2,   2,   2,
 -11, -11, -11, -11, -11, -11, -11, -11,
 -20, -20, -20, -20, -20, -20, -20, -20,
 -27, -27, -27, -27, -27, -27, -27, -27,
 -32, -32, -32, -32, -32, -32, -32, -32,
 -35, -35, -35, -35, -35, -35, -35, -35,
  0,    0,   0,   0,   0,   0,   0,   0
};

static const int pstKnightOutpost[64] =
{
  0,   0,   0,   0,   0,   0,   0,   0,
  0,   0,   0,   0,   0,   0,   0,   0,
  0,   0,   0,   0,   0,   0,   0,   0,
  0,   2,   3,   6,   6,   3,   2,   0,
  0,   2,   6,   9,   9,   6,   2,   0,
  0,   3,   9,  12,  12,   9,   3,   0,
  0,   0,   0,   0,   0,   0,   0,   0,
  0,   0,   0,   0,   0,   0,   0,   0
};

static const int pstBishopOutpost[64] =
{
  0,   0,   0,   0,   0,   0,   0,   0,
  0,   0,   0,   0,   0,   0,   0,   0,
  0,   0,   0,   0,   0,   0,   0,   0,
  0,   1,   2,   4,   4,   2,   1,   0,
  0,   1,   4,   6,   6,   4,   1,   0,
  0,   2,   6,   8,   8,   6,   2,   0,
  0,   0,   0,   0,   0,   0,   0,   0,
  0,   0,   0,   0,   0,   0,   0,   0
};

static const int hateKingside[64] = {
	  //A1                                H1
	   0,   0,   0,   0,   0,  -5, -12, -25,
	   0,   0,   0,   0,   0,  -5, -12, -25,
	   0,   0,   0,   0,   0,  -5, -12, -25,
	   0,   0,   0,   0,   0,  -5, -12, -25,
	   0,   0,   0,   0,   0,  -5, -12, -25,
	   0,   0,   0,   0,   0,  -5, -12, -25,
	   0,   0,   0,   0,   0,  -5, -12, -25,
	   0,   0,   0,   0,   0,  -5, -12, -25,
	   //A8                                H8
};

static const int hateQueenside[64] = {
	//A1                                H1
	 -25, -12,  -5,   0,   0,   0,   0,   0,
	 -25, -12,  -5,   0,   0,   0,   0,   0,
	 -25, -12,  -5,   0,   0,   0,   0,   0,
	 -25, -12,  -5,   0,   0,   0,   0,   0,
	 -25, -12,  -5,   0,   0,   0,   0,   0,
	 -25, -12,  -5,   0,   0,   0,   0,   0,
	 -25, -12,  -5,   0,   0,   0,   0,   0,
	 -25, -12,  -5,   0,   0,   0,   0,   0,
	 //A8                                H8
};

static const int mgp2 = 6;
static const int mgp3 = 6;
static const int mgp4 = 12;
static const int mgp5 = 30;
static const int mgp6 = 70;
static const int mgp7 = 120;

static const int egp2 = 7;
static const int egp3 = 7;
static const int egp4 = 30;
static const int egp5 = 66;
static const int egp6 = 152;
static const int egp7 = 250;


const int passed_bonus_mg[2][8] = {
  { 0, mgp2, mgp3, mgp4, mgp5, mgp6, mgp7, 0 },
  { 0, mgp7, mgp6, mgp5, mgp4, mgp3, mgp2, 0 }
};

const int passed_bonus_eg[2][8] = {
  { 0, egp2, egp3, egp4, egp5, egp6, egp7, 0 },
  { 0, egp7, egp6, egp5, egp4, egp3, egp2, 0 }
};

const int candidate_mg[2][8] = {
  {0,  2,  2,  5,  9, 16,  0, 0},
  {0,  0, 16,  9,  5,  2,  2, 0}
};

const int candidate_eg[2][8] = {
  {0,  4,  4, 10, 22, 32,  0, 0},
  {0,  0, 32, 22, 10,  4,  4, 0}
};

const int shieldBishBaseMg = 2;
const int shieldBishBaseEg = 2;
const int shieldBishOppoMg = 5;
const int shieldBishOppoEg = 8;
const int bPinMg = 20;
const int bPinEg = 5;
const int bPinBlunt = 10;
const int bBlockedMg = -50;
const int bBlockedEg = -50;


const int rookOpenMg = 16;
const int rookOpenEg = 12;
const int rookHalfMg = 9;
const int rookHalfEg = 6;
const int rookBadHalfMg = 3;
const int rookBadHalfEg = 5;
const int rookSeventhMg = 16;
const int rookSeventhEg = 32;
const int rookClosedMg = -6;
const int rookClosedEg = -1;

void EvaluatePressure(Position *p, EvalData *e, int sd);
void EvalBishopAtHome(Position *p, EvalData *e, int c, int bish, int pawn, int block, Bitboard king);
void EvalTrappedBishop(Position *p, EvalData *e, int c, int bish, int pawn, int sc);
void EvalUnstoppablePassers(Position* p, EvalData *e);
void EvalKingAttacks(Position *p, EvalData *e, int sd);
void EvalKing(Position *p, EvalData *e, int side);
void EvalPin(Position* p, EvalData* e, int c, int pinned0, int pinned1, int knight, int bish0, int bish1);

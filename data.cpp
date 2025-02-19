#include "rodent.h"

int castle_mask[64];
const int bit_table[64] = {
   0,  1,  2,  7,  3, 13,  8, 19,
   4, 25, 14, 28,  9, 34, 20, 40,
   5, 17, 26, 38, 15, 46, 29, 48,
  10, 31, 35, 54, 21, 50, 41, 57,
  63,  6, 12, 18, 24, 27, 33, 39,
  16, 37, 45, 47, 30, 53, 49, 56,
  62, 11, 23, 32, 36, 44, 52, 55,
  61, 22, 43, 51, 60, 42, 59, 58
};

// used in Swap() and quiescence search delta pruning,
// so that NxB, BxN and queen for 2 rooks are accepted

const int tp_value[7] = {
  100, 325, 325, 500, 1000, 0, 0
};

Bitboard pieceKey[12][64];
Bitboard castleKey[16];
Bitboard enPassantKey[8];
int pondering;
int root_depth;
Bitboard nodes;
int abortSearch;
int abortThread;
ENTRY *tt;
int tt_size;
int tt_mask;
int tt_date;
int options[N_OF_OPTIONS];
int weights [2][N_OF_FACTORS];
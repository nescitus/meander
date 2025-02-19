#include "rodent.h"
#include "endgame.h"

constexpr Bitboard bbWhiteSq = 0x55AA55AA55AA55AA;
constexpr Bitboard bbBlackSq = 0xAA55AA55AA55AA55;

static const int kingTable[64] = {
  -72, -48, -36, -24, -24, -36, -48, -72,
  -48, -24, -12,   0,   0, -12, -24, -48,
  -36, -12,   0,  12,  12,   0, -12, -36,
  -24,   0,  12,  24,  24,  12,   0, -24,
  -24,   0,  12,  24,  24,  12,   0, -24,
  -36, -12,   0,  12,  12,   0, -12, -36,
  -48, -24, -12,   0,   0, -12, -24, -48,
  -72, -48, -36, -24, -24, -36, -48, -72
};

static const int BN_wb[64] = {
    0,   0,  15,  30,  45,  60,  85, 100,
    0,  15,  30,  45,  60,  85, 100,  85,
   15,  30,  45,  60,  85, 100,  85,  60,
   30,  45,  60,  85, 100,  85,  60,  45,
   45,  60,  85, 100,  85,  60,  45,  30,
   60,  85, 100,  85,  60,  45,  30,  15,
   85, 100,  85,  60,  45,  30,  15,   0,
  100,  85,  60,  45,  30,  15,   0,   0
};

static const int BN_bb[64] = {
  100,  85,  60,  45,  30,  15,   0,   0,
   85, 100,  85,  60,  45,  30,  15,   0,
   60,  85, 100,  85,  60,  45,  30,  15,
   45,  60,  85, 100,  85,  60,  45,  30,
   30,  45,  60,  85, 100,  85,  60,  45,
   15,  30,  45,  60,  85, 100,  85,  60,
    0,  15,  30,  45,  60,  85, 100,  85,
    0,   0,  15,  30,  45,  60,  85, 100
};


int GetDrawFactor(Position* p, int sd) {

    int op = Opp(sd);

    if (p->cnt[sd][Pawn] == 0) {

        if (p->MajorCnt(sd) == 0) {

            // K(m) vs K(m) or Km vs Kp(p)
            if (p->cnt[sd][Bishop] + p->cnt[sd][Knight] < 2) return 0;

            if (p->MinorCnt(sd) == 2) {

                // KNN 
                if (p->cnt[sd] [Knight] == 2) {
                    if (p->cnt[op][Pawn] == 0)
                        return 0;
                    return 8;
                }

                //Kmm vs Km (p)
                if (JustBishop(p, op))
                    return 8;

                if (JustKnight(p, op)) {
                    if (p->cnt[sd][Bishop] < 2)
                        return 8;
                }

                //Kmm vs KR
                if (p->cnt[op][Rook] == 1)
                    return 8;
            }

        }

        // KR vs Km(p)
        if (p->cnt[sd][Queen] + p->MinorCnt(sd) == 0 && p->cnt[sd][Rook] == 1
            && p->cnt[op][Queen] + p->cnt[op][Rook] == 0 && p->MinorCnt(op) == 1) return 16; // 1/4

        // KRm vs KR(p)
        if (p->cnt[sd][Queen] == 0 && p->MinorCnt(sd) == 1 && p->cnt[sd][Rook] == 1
            && p->cnt[op][Queen] + p->MinorCnt(op) == 0 && p->cnt[op][Rook] == 1) return 16; // 1/4

        // KQm vs KQ(p)
        if (p->cnt[sd][Rook] == 0 && p->MinorCnt(sd) == 1 && p->cnt[sd][Queen] == 1
        && p->cnt[op][Rook] + p->MinorCnt(op) == 0 && p->cnt[op][Queen] == 1) return 32; // 1/2
    }

    // equal pawnless material (guarding against false advantages)
    
    if (p->AllPawnCnt() == 0) {

        if (JustRook(p, sd) && JustRook(p, op)) return 8;
        if (JustQueen(p, sd) && JustQueen(p, op)) return 8;
        if (JustTwoMinors(p, sd) && JustTwoMinors(p, op)) return 8;
        if (JustTwoMinors(p, sd) && JustRook(p, op)) return 8;
    }
    
    // KBP vs Km, blockade detection
 
    if (JustBishop(p, sd)
        && JustMinor(p, op)
        && p->cnt[sd] [Pawn] == 1
        && p->cnt[op] [Pawn] == 0
        && NotOnBishColor(p, sd, p->king_sq[op])) {
        Bitboard pawnSpan = FrontSpan(p->Map(sd, Pawn), sd);
        if (pawnSpan & p->Map(op, King)) return 16;
    }
 
    // bishops of opposite colors, single pawn advantage
    
    if (BishopEndgame(p)) {
        if (p->cnt[sd][Pawn] - p->cnt[op][Pawn] == 1) {
            if (DifferentBishops(p)) return 32;
        }
    }

    // KRPKR, defending king on pawn's way
 
    if (RookEndgame(p)) {
        if (p->cnt[sd][Pawn] == 1
        && p->cnt[op] [Pawn] == 0) {
            return ScaleKRPKR(p, sd, op);
        }
    }

    return 64; // default: no scaling
}

int ScaleKRPKR(Position* p, int sd, int op) {
    
    if ((RelSqBb(A7, sd) & p->GetPawns(sd))
    && (RelSqBb(A8, sd) & p->GetRooks(sd))
    && (FILE_A_BB & p->GetRooks(op))
    && ((RelSqBb(H7, sd) & p->GetKings(op)) || (RelSqBb(G7, sd) & p->GetKings(op)))
        ) return 0; // dead draw

    if ((RelSqBb(H7, sd) & p->GetPawns(sd))
    && (RelSqBb(H8, sd) & p->GetRooks(sd))
    && (FILE_H_BB & p->GetRooks(op))
    && ((RelSqBb(A7, sd) & p->GetKings(op)) || (RelSqBb(B7, sd) & p->GetKings(op)))
        ) return 0; // dead draw

    Bitboard pawnSpan = FrontSpan(p->Map(sd, Pawn), sd);
    if (pawnSpan & p->Map(op, King)) // king on pawn's path 
        return 32;

    return 64; // no scaling
}

// TODO: IsKingOnSinglePawnSpan

bool BishopEndgame(Position* p) {
    return (p->MajorCnt(White) == 0
        && p->MajorCnt(Black) == 0
        && p->cnt[White][Knight] == 0
        && p->cnt[Black][Knight] == 0
        && p->cnt[White][Bishop] == 1
        && p->cnt[Black][Bishop] == 1);
}

bool RookEndgame(Position* p) {
    return (JustRook(p, White) && JustRook(p, Black));
}

bool JustBishop(Position* p, int c) {
    return (p->MajorCnt(c) == 0
         && p->cnt[c] [Bishop] == 1
         && p->cnt[c] [Knight] == 0);
}

bool JustKnight(Position* p, int c) {
    return (p->MajorCnt(c) == 0
        && p->cnt[c][Bishop] == 0
        && p->cnt[c][Knight] == 1);
}

bool JustRook(Position* p, int c) {
    return (p->MinorCnt(c) == 0
        && p->cnt[c] [Queen] == 0
        && p->cnt[c] [Rook] == 1);
}

bool JustQueen(Position* p, int c) {
    return (p->MinorCnt(c) == 0
        && p->cnt[c][Queen] == 1
        && p->cnt[c][Rook] == 0);
}

bool JustMinor(Position* p, int c) {
    return (p->MinorCnt(c) == 1
        && p->MajorCnt(c) == 0);
}

bool JustTwoMinors(Position* p, int c) {
    return (p->MinorCnt(c) == 2
        && p->MajorCnt(c) == 0);
}

bool DifferentBishops(Position* p) {

    if ((Mask.sqColor[White] & p->Map(White, Bishop))
        && (Mask.sqColor[Black] & p->Map(Black, Bishop)))
        return true;

    if ((Mask.sqColor[Black] & p->Map(White, Bishop))
        && (Mask.sqColor[White] & p->Map(Black, Bishop)))
        return true;

    return false;
}

bool NotOnBishColor(Position* p, int bishSide, int s) {

    if (((Mask.sqColor[White] & p->Map(bishSide, Bishop)) == 0)
        && (Paint(s) & Mask.sqColor[White])) return true;

    if (((Mask.sqColor[Black] & p->Map(bishSide, Bishop)) == 0)
        && (Paint(s) & Mask.sqColor[Black])) return true;

    return false;
}

int CheckmateHelper(Position* p) {

    // TODO: make color-agnostic
    int result = 0;

    // KQ vs Kx: drive enemy king towards the edge

    if (p->cnt[White][Queen] > 0 && p->cnt[White][Pawn] == 0) {
        if (p->cnt[Black][Queen] == 0 && p->cnt[Black][Pawn] == 0 && p->cnt[Black][Rook] + p->cnt[Black][Bishop] + p->cnt[Black][Knight] <= 1) {

            result += 200;
            result += 10 * Dist.bonus[p->king_sq[White]][p->king_sq[Black]];
            result -= kingTable[p->king_sq[Black]];
            return result;
        }
    }

    if (p->cnt[Black][Queen] > 0 && p->cnt[Black][Pawn] == 0) {
        if (p->cnt[White][Queen] == 0 && p->cnt[White][Pawn] == 0 && p->cnt[White][Rook] + p->cnt[White][Bishop] + p->cnt[White][Knight] <= 1) {

            result -= 200;
            result -= 10 * Dist.bonus[p->king_sq[White]][p->king_sq[Black]];
            result += kingTable[p->king_sq[Black]];
            return result;
        }
    }

    // Weaker side has bare king (KQK, KRK, KBBK + bigger advantage

    if (p->cnt[Black][Pawn] + p->cnt[Black][Knight] + p->cnt[Black][Bishop] + p->cnt[Black][Rook] + p->cnt[Black][Queen] == 0) {
        if ((p->cnt[White][Queen] + p->cnt[White][Rook] > 0) || p->cnt[White][Bishop] > 1) {
            result += 200;
            result += 10 * Dist.bonus[p->king_sq[White]][p->king_sq[Black]];
            result -= kingTable[p->king_sq[Black]];
        }
    }

    if (p->cnt[White][Pawn] + p->cnt[White][Knight] + p->cnt[White][Bishop] + p->cnt[White][Rook] + p->cnt[White][Queen] == 0) {
        if ((p->cnt[Black][Queen] + p->cnt[Black][Rook] > 0) || p->cnt[Black][Bishop] > 1) {
            result -= 200;
            result -= 10 * Dist.bonus[p->king_sq[White]][p->king_sq[Black]];
            result += kingTable[p->king_sq[Black]];
        }
    }

    // KBN vs K specialized code

    if (p->cnt[White][Pawn] == 0
        && p->cnt[Black][Pawn] == 0
        && p->phase == 2) {

        if (p->cnt[White][Bishop] == 1 && p->cnt[White][Knight] == 1) {  // mate with black bishop and knight
            if (p->GetBishops(White) & bbWhiteSq) result -= 2 * BN_bb[p->king_sq[Black]];
            if (p->GetBishops(White) & bbBlackSq) result -= 2 * BN_wb[p->king_sq[Black]];
        }

        if (p->cnt[Black][Bishop] == 1 && p->cnt[Black][Knight] == 1) {  // mate with white bishop and knight
            if (p->GetBishops(Black) & bbWhiteSq) result += 2 * BN_bb[p->king_sq[White]];
            if (p->GetBishops(Black) & bbBlackSq) result += 2 * BN_wb[p->king_sq[White]];
        }
    }

    return result;
}

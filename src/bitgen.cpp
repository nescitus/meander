#include "rodent.h"
#include "stdio.h"

#define USE_MAGIC

#ifdef USE_MAGIC
#include "magicmoves.h"
#endif

static const int diag[64] = {
       0,   1,   2,   3,   4,   5,   6,   7,
       1,   2,   3,   4,   5,   6,   7,   8,
       2,   3,   4,   5,   6,   7,   8,   9,
       3,   4,   5,   6,   7,   8,   9,  10,
       4,   5,   6,   7,   8,   9,  10,  11,
       5,   6,   7,   8,   9,  10,  11,  12,
       6,   7,   8,   9,  10,  11,  12,  13,
       7,   8,   9,  10,  11,  12,  13,  14
};

static const int adiag[64] = {
       7,   8,   9,  10,  11,  12,  13,  14,
       6,   7,   8,   9,  10,  11,  12,  13,
       5,   6,   7,   8,   9,  10,  11,  12,
       4,   5,   6,   7,   8,   9,  10,  11,
       3,   4,   5,   6,   7,   8,   9,  10,
       2,   3,   4,   5,   6,   7,   8,   9,
       1,   2,   3,   4,   5,   6,   7,   8,
       0,   1,   2,   3,   4,   5,   6,   7
};

void cAttacks::Init(void) {

    // pawn

    for (int s = A1; s < NoSquare; ++s) {
        pAtt[White][s] = GetWPControl(Paint(s));
        pAtt[Black][s] = GetBPControl(Paint(s));
    }

    // knight
    
    for (int s = A1; s < NoSquare; ++s) {
        Bitboard bitboard = Paint(s);

        nAtt[s] = 0;
        nAtt[s] |= ShiftEast(ShiftNorth(ShiftNorth(bitboard)));
        nAtt[s] |= ShiftWest(ShiftNorth(ShiftNorth(bitboard)));
        nAtt[s] |= ShiftEast(ShiftSouth(ShiftSouth(bitboard)));
        nAtt[s] |= ShiftWest(ShiftSouth(ShiftSouth(bitboard)));
        nAtt[s] |= ShiftNorth(ShiftWest(ShiftWest(bitboard)));
        nAtt[s] |= ShiftSouth(ShiftWest(ShiftWest(bitboard)));
        nAtt[s] |= ShiftNorth(ShiftEast(ShiftEast(bitboard)));
        nAtt[s] |= ShiftSouth(ShiftEast(ShiftEast(bitboard)));
    }    

    // king

    for (int s = A1; s < NoSquare; ++s) {
        kAtt[s] = Paint(s);
        kAtt[s] |= SidesOf(kAtt[s]);
        kAtt[s] |= (ShiftNorth(kAtt[s]) | ShiftSouth(kAtt[s]));
        kAtt[s] ^= Paint(s); // this is for king safety eval, important as long as eval can be run while in check
    }
    

    // magic bitboard initialization routine

#ifdef USE_MAGIC
    initmagicmoves();
#endif

    // rays between squares 
	// (this requires bishop and rook attack getters,
	// so initmagicmoves must go first)

    for (int s1 = A1; s1 < NoSquare; ++s1)
        for (int s2 = A1; s2 < NoSquare; ++s2) {
            between[s1][s2] = SetBetween(s1, s2);
        }

    // ints attacked orthogonnally/ diagonally
    // from a given int on an empty board

    for (int s = A1; s < NoSquare; ++s) {
        bAttOnEmpty[s] = Bish(0ULL, s);
        rAttOnEmpty[s] = Rook(0ULL, s);
    }
}

Bitboard cAttacks::SetBetween(int s1, int s2) {

    Bitboard result = 0;

    if (SameRankOrFile(s1, s2)) {
        Bitboard fakeRook1 = Rook(Paint(s1), s2);
        Bitboard fakeRook2 = Rook(Paint(s2), s1);
        result |= (fakeRook1 & fakeRook2);
    }

    if (SameDiag(s1, s2)) {
        Bitboard fakeBish1 = Bish(Paint(s1), s2);
        Bitboard fakeBish2 = Bish(Paint(s2), s1);
        result |= (fakeBish1 & fakeBish2);
    }

    return result;
}

bool cAttacks::SameRankOrFile(int s1, int s2) {
    if (Rank(s1) == Rank(s2)) return true;
    if (File(s1) == File(s2)) return true;
    return false;
}

bool cAttacks::SameDiag(int s1, int s2) {
    if (diag[s1] == diag[s2]) return true;
    if (adiag[s1] == adiag[s2]) return true;
    return false;
}

Bitboard cAttacks::Pawn(int c, int s) { 
    return pAtt[c][s]; 
};

Bitboard cAttacks::Knight(int s) { 
    return nAtt[s]; 
};

Bitboard cAttacks::Bish(Bitboard o, int s) {

#ifdef USE_MAGIC
    return Bmagic(s, o);
#else
    Bitboard b = Paint(s);
    return NEOf(FillOcclNE(b, ~o))
         | NWOf(FillOcclNW(b, ~o))
         | SEOf(FillOcclSE(b, ~o))
         | SWOf(FillOcclSW(b, ~o));
#endif
}

Bitboard cAttacks::Rook(Bitboard o, int s) {

#ifdef USE_MAGIC
    return Rmagic(s, o);
#else
    Bitboard b = Paint(s);
    return NorthOf(FillOcclNorth(b, ~o))
         | SouthOf(FillOcclSouth(b, ~o))
         | EastOf(FillOcclEast(b, ~o))
         | WestOf(FillOcclWest(b, ~o));
#endif
}

Bitboard cAttacks::Queen(Bitboard o, int s) {
    return Rook(o, s) | Bish(o, s);
}


Bitboard cAttacks::King(int s) { 
    return kAtt[s]; 
};


Bitboard cAttacks::GetBetween(int s1, int s2) {
    return between[s1][s2];
}
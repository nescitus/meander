#include "meander.h"

static const int diagToUpperLeft[64] = {
     0,  1,  2,  3,  4,  5,  6,  7,
     1,  2,  3,  4,  5,  6,  7,  8,
     2,  3,  4,  5,  6,  7,  8,  9,
     3,  4,  5,  6,  7,  8,  9, 10,
     4,  5,  6,  7,  8,  9, 10, 11,
     5,  6,  7,  8,  9, 10, 11, 12,
     6,  7,  8,  9, 10, 11, 12, 13,
     7,  8,  9, 10, 11, 12, 13, 14
};

static const int diagToUpperRight[64] = {
     7,  6,  5,  4,  3,  2,  1,  0,
     8,  7,  6,  5,  4,  3,  2,  1,
     9,  8,  7,  6,  5,  4,  3,  2,
    10,  9,  8,  7,  6,  5,  4,  3,
    11, 10,  9,  8,  7,  6,  5,  4,
    12, 11, 10,  9,  8,  7,  6,  5,
    13, 12, 11, 10,  9,  8,  7,  6,
    14, 13, 12, 11, 10,  9,  8,  7
};

int nBonusMg[15] = { 14, 22, 29, 28, 19, -1, -6, -10, -11, -12, -13, -14, -15, -16, -17 };
int bBonusMg[15] = { 6, -12, 4, -16, -11, -17, -6, -14, -9, -17, -1, -17, -4, 3, 7 };
int rBonusMg[15] = { 7, 22, 23, 22, 22, 16, -2, -5, -14, -10, -8, -15, -16, -17, -17 };
int qBonusMg[15] = { 35, 49, 47, 44, 40, 14, 3, 0, -2, 1, 4, -3, -5, -6, -9 };

void cDistance::Init() {

    // Init distance tables

    for (int s1 = A1; s1 < NoSquare; ++s1) {
        for (int s2 = A1; s2 < NoSquare; ++s2) {
            int deltaR = Abs(Rank(s1) - Rank(s2));
            int deltaF = Abs(File(s1) - File(s2));
            grid[s1][s2] = deltaR + deltaF;
            cheb[s1][s2] = Max(deltaR, deltaF);  // for unstoppable passer evaluation
        }
    }

    // Init per-piece distance bonuses

    for (int s1 = A1; s1 < NoSquare; ++s1) {
        for (int s2 = A1; s2 < NoSquare; ++s2) {

            int rankDelta = Abs(Rank(s1) - Rank(s2));
            int fileDelta = Abs(File(s1) - File(s2));

            qTropismMg[s1][s2] = qBonusMg[grid[s1][s2]];
            rTropismMg[s1][s2] = rBonusMg[grid[s1][s2]];
            nTropismMg[s1][s2] = nBonusMg[grid[s1][s2]];
            bTropismMg[s1][s2] = bBonusMg[Abs(diagToUpperRight[s1] - diagToUpperRight[s2])];
            bTropismMg[s1][s2] += bBonusMg[Abs(diagToUpperLeft[s1] - diagToUpperLeft[s2])];
            bonus[s1][s2] = 14 - (rankDelta + fileDelta);  // for Fruit-like king tropism evaluation
        }
    }
}
#include "meander.h"

void cMask::Init() {
    f[fileA] = 0x0101010101010101ULL;
    f[fileB] = 0x0202020202020202ULL;
    f[fileC] = 0x0404040404040404ULL;
    f[fileD] = 0x0808080808080808ULL;
    f[fileE] = 0x1010101010101010ULL;
    f[fileF] = 0x2020202020202020ULL;
    f[fileG] = 0x4040404040404040ULL;
    f[fileH] = 0x8080808080808080ULL;

    // ranks

    r[rank1] = 0x00000000000000FFULL;
    r[rank2] = 0x000000000000FF00ULL;
    r[rank3] = 0x0000000000FF0000ULL;
    r[rank4] = 0x00000000FF000000ULL;
    r[rank5] = 0x000000FF00000000ULL;
    r[rank6] = 0x0000FF0000000000ULL;
    r[rank7] = 0x00FF000000000000ULL;
    r[rank8] = 0xFF00000000000000ULL;

    rim = r[rank1] | r[rank8] | f[fileA] | f[fileH];

    // relative ranks

    for (int i = 0; i < 8; i++) {
        rr[White][i] = r[i];
        rr[Black][i] = r[7 - i];
    }

    // outpost masks

    outpost[White] = (rr[White][rank4] | rr[White][rank5] | rr[White][rank6]) & ~f[fileA] & ~f[fileH];
    outpost[Black] = (rr[Black][rank4] | rr[Black][rank5] | rr[Black][rank6]) & ~f[fileA] & ~f[fileH];

    for (int i = 0; i < 64; i++) {
        passed[White][i] = 0;
        for (int j = File(i) - 1; j <= File(i) + 1; j++) {
            if ((File(i) == fileA && j == -1) ||
                (File(i) == fileH && j == 8))
                continue;
            for (int k = Rank(i) + 1; k <= rank8; k++)
                passed[White][i] |= Paint(Sq(j, k));
        }
    }
    for (int i = 0; i < 64; i++) {
        passed[Black][i] = 0;
        for (int j = File(i) - 1; j <= File(i) + 1; j++) {
            if ((File(i) == fileA && j == -1) ||
                (File(i) == fileH && j == 8))
                continue;
            for (int k = Rank(i) - 1; k >= rank1; k--)
                passed[Black][i] |= Paint(Sq(j, k));
        }
    }

    // support mask (for detecting weak pawns)

    for (int sq = A1; sq < 64; ++sq) {
        support[White][sq] = SidesOf(Paint(sq));
        support[White][sq] |= FillSouth(support[White][sq]);

        support[Black][sq] = SidesOf(Paint(sq));
        support[Black][sq] |= FillNorth(support[Black][sq]);
    }

    for (int i = 0; i < 8; i++) {
        adjacent[i] = 0;
        if (i > 0)
            adjacent[i] |= FILE_A_BB << (i - 1);
        if (i < 7)
            adjacent[i] |= FILE_A_BB << (i + 1);
    }

    home[White] = r[rank1] | r[rank2] | r[rank3] | r[rank4];
    home[Black] = r[rank8] | r[rank7] | r[rank6] | r[rank5];
    away[Black] = r[rank1] | r[rank2] | r[rank3] | r[rank4];
    away[White] = r[rank8] | r[rank7] | r[rank6] | r[rank5];
    space[White] |= Mask.r[rank2] | Mask.r[rank3] | Mask.r[rank4] | Mask.r[rank5];
    space[Black] |= Mask.r[rank7] | Mask.r[rank6] | Mask.r[rank5] | Mask.r[rank4];

    // castled king masks

    ksCastle[White] = Paint(F1, G1, H1) | Paint(F2, G2, H2);
    ksCastle[Black] = Paint(F8, G8, H8) | Paint(F7, G7, H7);
    qsCastle[White] = Paint(A1, B1, C1) | Paint(A2, B2, C2);
    qsCastle[Black] = Paint(A8, B8, C8) | Paint(A7, B7, C7);

    centralFile = f[fileC] | f[fileD] | f[fileE] | f[fileF];

    // square color masks

    sqColor[White] = 0x55AA55AA55AA55AA;
    sqColor[Black] = 0xAA55AA55AA55AA55;


    // wings

    kingside = f[fileF] | f[fileG] | f[fileH];
    queenside = f[fileA] | f[fileB] | f[fileC];
}
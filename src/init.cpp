#include "rodent.h"

void Init(void) {

    int i,j;

    for (i = 0; i < 64; i++)
        castle_mask[i] = 15;

    castle_mask[A1] = 13;
    castle_mask[E1] = 12;
    castle_mask[H1] = 14;
    castle_mask[A8] = 7;
    castle_mask[E8] = 3;
    castle_mask[H8] = 11;

    for (i = 0; i < 12; i++)
        for (j = 0; j < 64; j++)
            pieceKey[i][j] = Random64();

    for (i = 0; i < 16; i++)
        castleKey[i] = Random64();

    for (i = 0; i < 8; i++)
        enPassantKey[i] = Random64();
}

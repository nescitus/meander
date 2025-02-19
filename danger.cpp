#include "rodent.h"

void cDanger::Init(int attStep, int attCap) {

    for (int t = 0, i = 1; i < 511; ++i) {
        t = (int)Min(1280.0, Min((((double)(attStep) * 0.001) * i * i), t + double((attCap))));
        tab[i] = (t * 100) / 256; // rescale to centipawns
    }
}
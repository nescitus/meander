#include "rodent.h"
#include "math.h"
#include <stdio.h>

void cLMR::Init() {

    // Set depth of late move reduction

    for (int depth = 0; depth < MAX_PLY; depth++)
        for (int moves = 0; moves < MAX_MOVES; moves++) {

            int r = log(depth) * log(moves) / 2;
            if (depth == 0 || moves == 0) r = 0;
            //if (r > 8) r = 8;

            table[0][depth][moves] = r + 1; // zero window node
            table[1][depth][moves] = r;     // principal variation node

            for (int node = 0; node <= 1; node++) {
                if (table[node][depth][moves] > depth - 1) // reduction cannot exceed actual depth
                    table[node][depth][moves] = depth - 1;
                if (table[node][depth][moves] < 0)
                    table[node][depth][moves] = 0;
            }

            // uncomment code below to visualise lmr table

/**
if (depth < 24 && moves < 56) printf("%d ", (int)table[0][depth][moves]);
if (depth < 24 && moves == 56) printf("\n");
/**/
        }

}
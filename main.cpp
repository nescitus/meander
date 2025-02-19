#include "rodent.h"
#include "timer.h"
#include "stdio.h"

sTimer Timer; // class for setting and observing time limits
cAttacks Att;
cMask Mask;
cDistance Dist;
cPst Pst;
cDanger Danger;
cLMR LMR;
Engine mainEngine;
Engine helpEngine;
#ifdef USE_TUNING
cTuner Tuner;
#endif

int main() {

	Mask.Init();
	Att.Init();
	Pst.Init();
	Dist.Init();
	Danger.Init(27, 8);
    LMR.Init();
	Init();
	InitOptions();
    InitWeights();
	UciLoop();
	return 0;
}

void Position::Copy(Position* oldPos)
{
    for (int side = 0; side < 2; side++) {
        cl_bb[side] = oldPos->cl_bb[side];
        king_sq[side] = oldPos->king_sq[side];
    }

    for (int type = 0; type < 6; type++) {
        tp_bb[type] = oldPos->tp_bb[type];
        cnt[White][type] = oldPos->cnt[White][type];
        cnt[Black][type] = oldPos->cnt[Black][type];
    }

    for (int square = 0; square < 64; square++) 
    {
        pc[square] = oldPos->pc[square];
    }

    for (int i = 0; i < 256; i++) 
    {
        rep_list[i] = oldPos->rep_list[i];
    }

    side = oldPos->side;
    castle_flags = oldPos->castle_flags;
    ep_sq = oldPos->ep_sq;
    rev_moves = oldPos->rev_moves;
    head = oldPos->head;
    hash_key = oldPos->hash_key;
    pawn_key = oldPos->pawn_key;
    phase = oldPos->phase;
}
#include "rodent.h"

static const int ph[7] = { 0, 1, 1, 2, 4, 0, 0 };
static const int ph_max = 24;

int GetNewEval(Position* p) 
{
	int mg = 0;
	int eg = 0;
	int ph = 0;
	int score;
	
	int mg_phase = Min(ph_max, p->phase);
	int eg_phase = ph_max - mg_phase;

	score = (((mg * mg_phase) + (eg * eg_phase)) / ph_max);
	return score;
}
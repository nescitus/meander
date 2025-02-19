#include "rodent.h"

int Engine::QuiesceChecks(Position* p, int ply, int alpha, int beta, int* pv) 
{
    int best, score, move, moveType, hashFlag, new_pv[MAX_PLY];
    bool isPv = (alpha != beta - 1);
    MOVES m[1];
    UNDO u[1];
    EvalData e;

    if (InCheck(p)) {
        return QuiesceFlee(p, ply, alpha, beta, pv);
    }

    // Early exit and node initialization

    nodes++;
#ifndef USE_TUNING
    CheckForTimeout();


    if (abortSearch || abortThread) {
        return 0;
    }
#endif

    *pv = 0;

    if (IsDraw(p)) {
        return 0;
    }

    move = 0;

    // Read transposition table

    if (TransRetrieve(p->hash_key, &move, &score, &hashFlag, alpha, beta, 0, ply)) {

        if (!isPv || (score > alpha && score < beta))
            return score;
    }

    // Determine floor value

    best = Evaluate(p, &e, true);

    if (best >= beta) {
        return best;
    }

    if (best > alpha) {
        alpha = best;
    }

    // Safeguard against reaching MAX_PLY limit

    if (ply >= MAX_PLY - 1)
    {
        return Evaluate(p, &e, true);
    }

    // Prepare for search

    InitMoves(p, m, move, -1, ply);

    // Main loop

    while ((move = NextCaptureOrCheck(m, &moveType))) {

        // Make move

        p->DoMove(move, u);
        if (Illegal(p)) {
            p->UndoMove(move, u);
            continue;
        }

        score = -QuiesceChecks2(p, ply + 1, -beta, -alpha, new_pv);

        // Undo move

        p->UndoMove(move, u);
        if (abortSearch || abortThread) {
            return 0;
        }

        // Beta cutoff

        if (score >= beta) {
            TransStore(p->hash_key, move, score, LOWER, 0, ply);
            return score;
        }

        // New best move

        if (score > best) {
            best = score;
            if (score > alpha) {
                alpha = score;
                BuildPv(pv, new_pv, move);
            }
        }

    } // end of main loop

    // Return correct checkmate/stalemate score

    if (best == -INF) {
        return InCheck(p) ? -MATE + ply : 0;
    }

    // Save result in transposition table

    if (*pv)
        TransStore(p->hash_key, *pv, best, EXACT, 0, ply);
    else
        TransStore(p->hash_key, 0, best, UPPER, 0, ply);

    return best;
}

int Engine::QuiesceChecks2(Position* p, int ply, int alpha, int beta, int* pv)
{
    int best, score, move, moveType, hashFlag, new_pv[MAX_PLY];
    bool isPv = (alpha != beta - 1);
    MOVES m[1];
    UNDO u[1];
    EvalData e;

    if (InCheck(p)) {
        return QuiesceFlee(p, ply, alpha, beta, pv);
    }

    // Early exit and node initialization

    nodes++;
#ifndef USE_TUNING
    CheckForTimeout();


    if (abortSearch || abortThread) {
        return 0;
    }
#endif

    * pv = 0;

    if (IsDraw(p)) {
        return 0;
    }

    move = 0;

    // Read transposition table

    if (TransRetrieve(p->hash_key, &move, &score, &hashFlag, alpha, beta, 0, ply)) {

        if (!isPv || (score > alpha && score < beta))
            return score;
    }

    // Determine floor value

    best = Evaluate(p, &e, true);

    if (best >= beta) {
        return best;
    }

    if (best > alpha) {
        alpha = best;
    }

    // Safeguard against reaching MAX_PLY limit

    if (ply >= MAX_PLY - 1)
    {
        return Evaluate(p, &e, true);
    }

    // Prepare for search

    InitMoves(p, m, move, -1, ply);

    // Main loop

    while ((move = NextCaptureOrCheck(m, &moveType))) {

        // Make move

        p->DoMove(move, u);
        if (Illegal(p)) {
            p->UndoMove(move, u);
            continue;
        }

        score = -Quiesce(p, ply + 1, -beta, -alpha, new_pv);

        // Undo move

        p->UndoMove(move, u);
        if (abortSearch || abortThread) {
            return 0;
        }

        // Beta cutoff

        if (score >= beta) {
            TransStore(p->hash_key, move, score, LOWER, 0, ply);
            return score;
        }

        // New best move

        if (score > best) {
            best = score;
            if (score > alpha) {
                alpha = score;
                BuildPv(pv, new_pv, move);
            }
        }

    } // end of main loop

    // Return correct checkmate/stalemate score

    if (best == -INF) {
        return InCheck(p) ? -MATE + ply : 0;
    }

    // Save result in transposition table

    if (*pv)
        TransStore(p->hash_key, *pv, best, EXACT, 0, ply);
    else
        TransStore(p->hash_key, 0, best, UPPER, 0, ply);

    return best;
}


int Engine::Quiesce(Position *p, int ply, int alpha, int beta, int *pv) {

  int best, score, move, new_pv[MAX_PLY];
  MOVES m[1];
  UNDO u[1];
  EvalData e;

#ifndef USE_TUNING
  if (InCheck(p))
  {
      return QuiesceFlee(p, ply, alpha, beta, pv);
  }
#endif

  // Statistics and attempt at quick exit

  nodes++;
#ifndef USE_TUNING
  CheckForTimeout();
  if (abortSearch || abortThread)
      return 0;
#endif
  *pv = 0;
  
  if (IsDraw(p)) 
      return 0;

  if (ply >= MAX_PLY - 1) 
      return Evaluate(p, &e, 1);

  // Get a stand-pat score and adjust bounds
  // (exiting if eval exceeds beta)

  best = Evaluate(p, &e, 1);
  if (best >= beta) return best;
  if (best > alpha) alpha = best;
  int alphaFloor = alpha;

  // Transposition table read

  InitCaptures(p, m);

  // Main loop

  while ((move = NextCapture(m))) {

  // Delta pruning

  if (best + tp_value[TpOnSq(p, Tsq(move))] + 300 < alphaFloor) // TODO: array of margins
      continue;

  // Pruning of bad captures

  if (IsBadCapture(p, move)) 
      continue;

    p->DoMove(move, u);
    if (Illegal(p)) { p->UndoMove(move, u); continue; }
    score = -Quiesce(p, ply + 1, -beta, -alpha, new_pv);
    p->UndoMove(move, u);
    if (abortSearch || abortThread)
        return 0;

  // Beta cutoff

	if (score >= beta) {
		return score;
	}

  // Adjust alpha and score

    if (score > best) {
      best = score;
      if (score > alpha) {
        alpha = score;
        BuildPv(pv, new_pv, move);
      }
    }
  }

  return best;
}

int Engine::QuiesceFlee(Position* p, int ply, int alpha, int beta, int* pv) {

    int best, score, move, moveType, hashFlag, new_pv[MAX_PLY];
    bool isPv = (alpha != beta - 1);
    MOVES m[1];
    UNDO u[1];
    EvalData e;

    // Early exit and node initialization

    nodes++;
#ifndef USE_TUNING
    CheckForTimeout();

    if (abortSearch || abortThread)
    {
        return 0;
    }
#endif

    *pv = 0;

    if (IsDraw(p))
    {
        return 0;
    }

    move = 0;

    // Read transposition table

    if (TransRetrieve(p->hash_key, &move, &score, &hashFlag, alpha, beta, 0, ply)) {

        if (!isPv || (score > alpha && score < beta))
        {
            return score;
        }
    }

    // Safeguard against reaching MAX_PLY limit

    if (ply >= MAX_PLY - 1) {
        return Evaluate(p, &e, true);
    }

    // Prepare for main search

    best = -INF;
    InitMoves(p, m, move, -1, ply);

    // Main loop

    while ((move = NextMove(m, &moveType))) {

        // Make move

        p->DoMove(move, u);
        if (Illegal(p)) {
            p->UndoMove(move, u);
            continue;
        }

        score = -Quiesce(p, ply + 1, -beta, -alpha, new_pv);

        // Undo move

        p->UndoMove(move, u);
        if (abortSearch || abortThread)
        {
            return 0;
        }

        // Beta cutoff

        if (score >= beta) {
            TransStore(p->hash_key, move, score, LOWER, 0, ply);
            return score;
        }

        // New best move

        if (score > best) {
            best = score;
            if (score > alpha) {
                alpha = score;
                BuildPv(pv, new_pv, move);
            }
        }

    } // end of main loop

    // Return correct checkmate/stalemate score

    if (best == -INF)
        return InCheck(p) ? -MATE + ply : 0;

    // Save result in transposition table

    if (*pv)
        TransStore(p->hash_key, *pv, best, EXACT, 0, ply);
    else
        TransStore(p->hash_key, 0, best, UPPER, 0, ply);

    return best;
}

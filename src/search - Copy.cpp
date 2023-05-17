#include <stdio.h>
#include <string.h>
#include "math.h"
#include "rodent.h"
#include "timer.h"

int progSide;
int captureSquare[MAX_PLY];
int lastVictim, lastTargetSquare;

const int lmpTable[][10 + 1] = {
    { 0, 3, 4, 6, 10, 15, 21, 28, 36, 45, 55 },
    { 0, 5, 6, 9, 15, 23, 32, 42, 54, 68, 83 }
};

int seeDepth = 4;
int seeCaptStep = -120;
int histLimit = 800; // was 800

void Engine::SetTimingData(Position* p, int move, int depth, int *pv)
{
    /*
    if (Swap(p, Fsq(move), Tsq(move)) < 0)
        Timer.isSacrifice = true;
    else
        Timer.isSacrifice = false;
        */

    if (depth > 4)
    {
        Timer.isRecapture = true;
        if ((Tsq(move) != lastTargetSquare)
        || (tp_value[lastVictim] != tp_value[TpOnSq(p, Tsq(move))]))
            Timer.isRecapture = false;

        if (pv[0] != move) Timer.OnNewRootMove();
        else               Timer.OnOldRootMove();
    }
}

int Engine::Search(Position* p, int ply, int alpha, int beta, int depth, int was_null, int* pv) {

    int best, score, move, moveType, newDepth, reduction, hashFlag, hashScore, new_pv[MAX_PLY];
    bool isInCheck, isPrunableNode, isPrunableMove, isPv = (beta > alpha + 1);
    int movesTried = 0, quietTried = 0;
    bool isTTread = false;
    bool canSing = false;
    int singScore = 0;
    int singMove = 0;
    int hashMove = 0;
    int moveList[256];
    int histScore;
    int moveSEEscore = 0;

    MOVES m[1];
    UNDO u[1];
    EvalData e;

    // Quiescence search entry point

    if (depth <= 0)
        return QuiesceChecks(p, ply, alpha, beta, pv);

    // Periodically check for timeout, ponderhit or stop command

    nodes++;
    CheckForTimeout();

    // Quick exit on a timeout or on a statically detected draw

    if (abortSearch || abortThread)
        return 0;

    if (ply) 
        *pv = 0;
    
    if (IsDraw(p) && ply)
        return 0;

    // Mate distance pruning (except at root)

    if (ply) 
    {
        alpha = Max(alpha, -MATE + ply);
        beta = Min(beta, MATE - ply + 1);
        if (alpha > beta) {
            return alpha;
        }
    }

    // Retrieving data from transposition table. We hope for a cutoff
    // or at least for a move to improve move ordering.

    move = 0;
    if (TransRetrieve(p->hash_key, &move, &score, &hashFlag, alpha, beta, depth, ply))
    {
        isTTread = true;
        hashScore = score;
        hashMove = move;

        // For move ordering purposes, a cutoff from hash is treated
        // exactly like a cutoff from search

        if (score >= beta)
        {
            triesHistory[p->pc[Fsq(move)]][Tsq(move)] += HistInc(depth);
            UpdateHistory(p, oldMove[ply - 1], oldMove[ply - 2], move, depth, ply);
        }

        // In pv nodes only exact scores are returned. This is done because
        // there is much more pruning and reductions in zero-window nodes,
        // so retrieving such scores in pv nodes works like retrieving scores
        // from slightly lower depth.

        if (!isPv || (score > alpha && score < beta))
            return score;
    }

    // Will we use singular extension?

    canSing = false;

    if (isPv && depth > 8)
    {
        if (TransRetrieve(p->hash_key, &singMove, &singScore, &hashFlag, alpha, beta, depth - 4, ply)) 
        {
            if (hashFlag & LOWER)
                canSing = true;
        }
    }

    // Safeguard against exceeding ply limit

    if (ply >= MAX_PLY - 1) 
    {
        return Evaluate(p, &e, 1);
    }

    // Are we in check? Knowing that is useful when it comes 
    // to pruning/reduction decisions

    isInCheck = InCheck(p);
    isPrunableNode = !isInCheck && !isPv && ply > 1;

    // Internal iterative deepening

    /**
    if (isPv
        && !fl_check
        && !move
        && depth > 8) {
        Search(p, ply, alpha, beta, depth - 2, was_null, lastMove, pv);
        TransRetrieveMove(p->hash_key, &move);
    }
    /**/

    // Prepare static evaluation of a node

    int eval;

    if (isInCheck)
        eval = -INF;
    else
        eval = Evaluate(p, &e, true);

    oldEval[ply] = eval;

    // Adjust node eval by using transposition table score

    if (isTTread) 
    {
        if (hashFlag & (hashScore > eval ? LOWER : UPPER))
            eval = hashScore;
    }

    bool improving = true;

    if (ply > 2) { // >= 2 is no better
        if (eval < oldEval[ply - 2])
            improving = false;
    }

    // Null move (and static null move)

    if (isPrunableNode
    && !was_null
    && MayNull(p)) {

        if (depth <= 3
        && abs(beta - 1) > -INF + 100) // TODO: does it work?
        {
            int evalMargin = 120 * depth; // 90 worse, 135 - 30 * improving worse
            if (eval - evalMargin >= beta)
                return eval;
        }

        if (depth > 1 && eval > beta) {

            reduction = ((13 + depth) >> 2) + Min(3, (eval - beta) / 185);

            if (HashAllowsNullMove(p->hash_key, alpha, beta, depth - reduction, ply)) 
            {
                oldMove[ply] = 0;
                p->DoNull(u);
                score = -Search(p, ply + 1, -beta, -beta + 1, depth - reduction, 1, new_pv);
                p->UndoNull(u);

                // if (score > MAX_EVAL) score = beta;

                if (abortSearch || abortThread)
                    return 0;

                // null move verification
                if (depth - reduction > 5 && score >= beta)
                    score = Search(p, ply, alpha, beta, depth - reduction - 4, 1, pv);

                if (abortSearch || abortThread)
                    return 0;

                if (score >= beta)
                    return score;
            }
        }
    }

    // end of null move code

    // Razoring based on Toga II 3.0

    if (isPrunableNode
    && !move
    && !was_null
    && !(p->Map(p->side, Pawn) & bbRelRank[p->side][rank7]) // no pawns to promote in one move
    && depth <= 4) {
        int threshold = beta - 200 - (depth - 1) * 60 - 200 * (depth > 3) + 200 * (depth > 4);

        if (eval < threshold) {
            score = QuiesceChecks(p, ply, alpha, beta, pv);
            if (score < threshold) 
                return score;
        }
    }   // end of razoring code

    // Init moves and variables before entering main loop

    best = -INF;
    int ref = -1;
    int cont = -1;
    if (ply) {
        ref = refutation[Fsq(oldMove[ply - 1])][Tsq(oldMove[ply - 1])];
    }
#ifdef USE_CONTINUATION
    if (ply > 1)
        cont = continuation[Fsq(oldMove[ply - 2])][Tsq(oldMove[ply - 2])];
#endif
    InitMoves(p, m, move, ref, cont, ply);

    // Main loop

    while ((move = NextMove(m, &moveType))) 
    {
        histScore = GetHistScore(p, move);
        SetCaptureSquare(p, move, ply);

        if (moveType == MV_BADCAPT && depth <= seeDepth) 
        {
            moveSEEscore = Swap(p, Fsq(move), Tsq(move));
        }

        p->DoMove(move, u);
        if (Illegal(p)) { p->UndoMove(move, u); continue; }
        oldMove[ply] = move;

        // Update move statistics (needed for reduction/pruning decisions)

        moveList[movesTried] = move;
        movesTried++;
        if (moveType == MV_NORMAL)
            quietTried++;

        // Display info currmove in UCI mode

        if (!ply /* && State.isUci*/ && depth > 15) 
        {
                char moveString[6];
                MoveToStr(move, moveString);
                printf("info currmove %s currmovenumber %d\n", moveString, movesTried);            
        }

        // Can we prune current move?

        isPrunableMove = !InCheck(p) && (moveType == MV_NORMAL);

        // Set new search depth

        newDepth = depth - 1;

        // TODO: if (ply) for all extenstions

        if (InCheck(p) && (isPv || depth < 9))
            newDepth++; // check extension

        else if ((depth < 9 && isPv) && Tsq(move) == captureSquare[ply - 1])
            newDepth++; // recapture extension

        //else if (depth >= 7 && move == hashMove && histScore > 800)
        //    newDepth++; // history extension

        // TODO
          // history extension - if the tt move has a really good history score, extend.
    // thank you to Connor, author of Seer for this idea
    //    else if (ply && depth >= 7 && tt && move == hashMove && history >= 98304)
    //        newDepth++;

        else if (depth > 8 // singular extension
            && move == singMove
            && canSing) {
            int newAlpha = -singScore - 50;
            int mockPv;
            int sc = Search(p, ply + 1, newAlpha, newAlpha + 1, depth - 4, false, &mockPv);
            if (sc <= newAlpha) {
                newDepth += 1;
            }
        }

        // SEE pruning of bad captures

        if (!isInCheck
        && !InCheck(p)
        && moveType == MV_BADCAPT
        && depth <= seeDepth
        && !isPv) 
        {
            if (moveSEEscore > seeCaptStep * depth) { // yes, sign is correct
                p->UndoMove(move, u);
                /*char move_str[6];
                MoveToStr(move, move_str);
                p->PrintBoard();
                printf("%s", move_str);*/
                continue;
            }
        }

        bool isPawnPush = (p->tp_bb[Pawn] & Paint(Tsq(move)))
                        && (Paint(Tsq(move)) & (RANK_2_BB | RANK_7_BB));

        // Late move pruning

        if (isPrunableNode
        && depth < 10
        && quietTried > lmpTable[improving][depth]
        && isPrunableMove
        && histScore < histLimit
        && !isPawnPush
        && MoveType(move) != CASTLE) 
        {
            p->UndoMove(move, u);
            continue;
        }

        // Pawn threat pruning at depth 1
        // (depth 2, don't blunder major piece - inconclusive)

        if (!isInCheck
        && !InCheck(p)
        && moveType == MV_NORMAL
        && depth == 1
        && !isPv)
        {
            if (!(p->IsOnSq(p->side ^ 1, Pawn, Tsq(move))))
            {
                Bitboard threats = (Att.Pawn(p->side ^ 1, Tsq(move)));

                if (threats & (p->Map(p->side, Pawn)))
                {
                    p->UndoMove(move, u);
                    continue;
                }
            }
        }

        // Late move reduction

        reduction = 0;

        if (depth >= 2
        && movesTried > 3
        && !isInCheck
        && histScore < histLimit
        && (moveType == MV_NORMAL)
        && LMR.table[isPv][depth][movesTried] > 0
        && !isPawnPush
        && MoveType(move) != CASTLE) 
        {
            reduction = LMR.table[isPv][depth][movesTried];

            reduction += (histScore < 200);

            reduction += (!isPv && !improving);

            // Checks are reduced half of the usual amount

            if (InCheck(p) && reduction > 1)
                reduction /= 2;

            // Cap on reduction

            if (reduction >= newDepth)
                reduction = newDepth - 1;

            // Pawn moves are reduced a bit less

            if (p->tp_bb[Tsq(move)] == Pawn && reduction > 1 && isPv)
                reduction--;

            newDepth -= reduction;
        }
        
        if (!InCheck(p)
        && moveType == MV_BADCAPT
        && depth < 8
        && !isPv
        && depth >= 2
        && movesTried > 3
        && !isInCheck)
        {
            reduction = 1;
            newDepth -= reduction;
        }
        

    re_search:

        // PVS

        if (best == -INF)
            score = -Search(p, ply + 1, -beta, -alpha, newDepth, 0, new_pv);
        else {
            score = -Search(p, ply + 1, -alpha - 1, -alpha, newDepth, 0, new_pv);
            if (!abortSearch && !abortThread && score > alpha && score < beta)
                score = -Search(p, ply + 1, -beta, -alpha, newDepth, 0, new_pv);
        }

        // Reduced move scored above alpha - we need to re-search it

        if (reduction && score > alpha) {
            newDepth += reduction;
            reduction = 0;
            goto re_search;
        }

        p->UndoMove(move, u);
        if (abortSearch || abortThread)
            return 0;

        // Beta cutoff

        if (score >= beta) {

            if (ply == 0) {
                SetTimingData(p, move, depth, pv);
            }

            UpdateHistory(p, oldMove[ply - 1], oldMove[ply - 1], move, depth, ply);
            for (int i = 0; i < movesTried; i++) {
                UpdateTried(p, moveList[i], depth);
            }
            TransStore(p->hash_key, move, score, LOWER, depth, ply);

            // If beta cutoff occurs at the root, change the best move

            if (!ply) {
                BuildPv(pv, new_pv, move);
                DisplayPv(score, pv, isMain);
            }

            return score;
        }

        // Updating score and alpha

        if (score > best) {
            best = score;
            if (score > alpha) {

                if (ply == 0) {
                    SetTimingData(p, move, depth, pv);
                }

                alpha = score;
                BuildPv(pv, new_pv, move);
                if (!ply)
                    DisplayPv(score, pv, isMain);
            }
        }

    } // end of the main loop

    // Return correct checkmate/stalemate score

    if (best == -INF) {
        if (Timeout())
            abortSearch = true;
        return InCheck(p) ? -MATE + ply : 0;
    }

    // Save score in the transposition table

    if (*pv)
        TransStore(p->hash_key, *pv, best, EXACT, depth, ply);
    else
        TransStore(p->hash_key, 0, best, UPPER, depth, ply);

    return best;
}

bool IsDraw(Position* p) {

    // Draw by 50 move rule

    if (p->rev_moves > 100) {
        if (Timeout())
            abortSearch = true;
        return true;
    }

    // Draw by repetition

    for (int i = 4; i <= p->rev_moves; i += 2)
        if (p->hash_key == p->rep_list[p->head - i]) {
            if (Timeout())
                abortSearch = true;
            return true;
        }

    // Draw by insufficient material (bare kings or Km vs K)

    if (!Illegal(p)) {
        if (p->cnt[White][Pawn] + p->cnt[Black][Pawn] + p->MajorCnt(White) + p->MajorCnt(Black) == 0) {

            // K(m)K
            if (p->MinorCnt(White) + p->MinorCnt(Black) <= 1) {
                if (Timeout())
                    abortSearch = true;
                return true;
            }

            // KmKm but no kings on the rim
            if (p->MinorCnt(White) == 1 && p->MinorCnt(Black) == 1) {
                if ((p->tp_bb[King] & Mask.rim) == 0) {
                    if (Timeout())
                        abortSearch = true;
                    return true;
                }
            }
        }
    }

    // KPK draw

    if (p->AllPawnCnt() == 1 && p->MajorCnt(White) + p->MajorCnt(Black) + p->MinorCnt(White) + p->MinorCnt(Black) == 0) {
        // TODO: is this loss of time reason?
        if (p->cnt[White][Pawn] == 1) return KPKdraw(p, White);  // exactly one white pawn
        if (p->cnt[Black][Pawn] == 1) return KPKdraw(p, Black);  // exactly one black pawn
    }

    return false; // default: no draw
}

bool KPKdraw(Position* p, int sd)
{
    int op = sd ^ 1;
    Bitboard bbPawn = p->Map(sd, Pawn);
    Bitboard bbStrongKing = p->Map(sd, King);
    Bitboard bbWeakKing = p->Map(op, King);

    // opposition through a pawn

    if (p->side == sd
        && (bbWeakKing & FwdOf(bbPawn, sd))
        && (bbStrongKing & FwdOf(bbPawn, op))) {
        return true;
    }

    // weaker side can create opposition through a pawn in one move

    if (p->side == op
        && (Att.King(p->king_sq[op]) & FwdOf(bbPawn, sd))
        && (bbStrongKing & FwdOf(bbPawn, op))) {
        if (!Illegal(p)) return true;
    }

    // opposition next to a pawn

    if (p->side == sd
        && (bbStrongKing & SidesOf(bbPawn))
        && (bbWeakKing & FwdOf(FwdOf(bbStrongKing, sd), sd))) {
        return true;
    }

    // TODO: pawn checks king

    return false;
}

void DisplayPv(int score, int* pv, int t) {

    char* type, pv_str[512];
    Bitboard nps = 0;
    int elapsed = Timer.GetElapsedTime();
    if (elapsed) nps = nodes * 1000 / elapsed;

    type = "mate";
    if (score < -MAX_EVAL)
        score = (-MATE - score) / 2;
    else if (score > MAX_EVAL)
        score = (MATE - score + 1) / 2;
    else
        type = "cp";

    PvToStr(pv, pv_str);
    printf("info depth %d time %d nodes %I64d nps %I64d score %s %d pv %s thread %d\n",
        root_depth, elapsed, nodes, nps, type, score, pv_str, t);
}

void CheckForTimeout(void) {

    char command[80];

    if (nodes & 4095 || root_depth == 1)
        return;

    if (InputAvailable()) {
        ReadLine(command, sizeof(command));

        if (strcmp(command, "stop") == 0)
            abortSearch = 1;
        else if (strcmp(command, "ponderhit") == 0)
            pondering = 0;
    }

    if (Timeout())
        abortSearch = 1;
}

int Timeout() {

#ifdef USE_TUNING
    return false;
#endif

    if (engineLevel < numberOfLevels) {
        if (nodes > nodeStepPerLevel * (engineLevel + 1) && root_depth > 1)
            return true;
    }

    return (!pondering && !Timer.IsInfiniteMode() && Timer.TimeHasElapsed());
}

// check whether our king has at least one legal move

bool IsKingMobile(Position* p) {

    bool isKingMobile = false;
    int side = p->side;
    int oppo = ~side;
    int ksq = p->king_sq[side];
    int target;
    Bitboard moves = Att.King(ksq) & p->Empty(); // try !own color

    while (moves) {
        target = PopFirstBit(&moves);
        if (!Attacked(p, target, oppo))
            return true;
    }

    return false;
}

void SetCaptureSquare(Position* p, int move, int ply)
{
    if (!p->IsEmpty(Tsq(move)))
        captureSquare[ply] = Tsq(move);
    else
        captureSquare[ply] = -1;
}

bool HashAllowsNullMove(Bitboard hash, int alpha, int beta, int depth, int ply) {

    int move, score, flag;

    if (TransRetrieve(hash, &move, &score, &flag, alpha, beta, depth, ply)) {
        if (score < beta)
            return false;
    }

    return true;
}

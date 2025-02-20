#include <stdio.h>
#include <string.h>
#include "math.h"
#include "rodent.h"
#include "timer.h"

const int dummyMove = CreateMove(A1, H7);
const int singularDepth = 7;
int excludedMove = dummyMove;

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

int Engine::Search(Position* p, int ply, int alpha, int beta, int depth, bool isExcluded, int was_null, int* pv) {

    int best, score, move, moveType, newDepth, reduction, hashFlag, hashScore, new_pv[MAX_PLY];
    bool isInCheck, isPrunableNode, isPrunableMove, isPv = (beta > alpha + 1);
    int movesTried = 0, quietTried = 0;
    bool isTTread = false;
    int hashMove = 0;
    int moveList[256];
    int histScore;
    int moveSEEscore = 0;
    int singularMove, singularScore;
    bool singularExtension, hasTTmove;

    MOVES m[1];
    UNDO u[1];
    EvalData e;

    // Init

    singularScore = -INF;
    singularMove = 0;
    singularExtension = false;
    hasTTmove = false;

    // Quiescence search entry point

    if (depth <= 0)
        return QuiesceChecks(p, ply, alpha, beta, pv);

    // Periodically check for timeout, ponderhit or stop command

    nodes++;
    CheckForTimeout();

    // Quick exit on a timeout or on a statically detected draw

    if (abortSearch || abortThread)
        return 0;

    if (ply) {
        *pv = 0;

        if (IsDraw(p))
            return 0;

        // Mate distance pruning (except at root)

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
            UpdateHistory(p, oldMove[ply - 1], move, depth, ply);
        }

        if (move) hasTTmove = true;

        // In pv nodes only exact scores are returned. This is done because
        // there is much more pruning and reductions in zero-window nodes,
        // so retrieving such scores in pv nodes works like retrieving scores
        // from slightly lower depth.

        if (!isPv || (score > alpha && score < beta))
            return score;
    }

    // Safeguard against exceeding ply limit

    if (ply >= MAX_PLY - 1)
    {
        return Evaluate(p, &e, 1);
    }

    // Prepare for singular extension

    if (ply && depth > singularDepth && excludedMove == dummyMove) {
        if (TransRetrieve(p->hash_key, &singularMove, &singularScore, &hashFlag, alpha, beta, depth - 4, ply)) {

            if ((hashFlag & LOWER) && singularScore < MAX_EVAL)
            {
                singularExtension = true;
            }
        }
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

    oldEval[ply] = eval; // TODO : illogical, 
    // either both old and new should be adjusted or both should not

    // Adjust node eval by using transposition table score

    //if (isTTread)
    //{
    //    if (hashFlag & (hashScore > eval ? LOWER : UPPER))
    //        eval = hashScore;
   // }

    bool improving = true;

    if (ply > 1) {
        if (eval < oldEval[ply - 2])
            improving = false;
    }

    // Null move (and static null move)

    if (isPrunableNode
        && !was_null
        && !isExcluded
        && MayNull(p)) {

        if (depth <= 3
            && abs(beta - 1) > -INF + 100) // TODO: does it work?
        {
            int evalMargin = 120 * depth; // 90 worse, 135 - 30 * improving worse
            if (eval - evalMargin >= beta)
                return eval;
        }

        if (depth > 1 && eval > beta) {

            reduction = 3 + depth / 6;
            reduction = ((13 + depth) >> 2) + Min(3, (eval - beta) / 185);

            if (HashAllowsNullMove(p->hash_key, alpha, beta, depth - reduction, ply))
            {
                oldMove[ply] = 0;
                p->DoNull(u);
                score = -Search(p, ply + 1, -beta, -beta + 1, depth - reduction, 1, false, new_pv);
                p->UndoNull(u);

                // if (score > MAX_EVAL) score = beta;

                if (abortSearch || abortThread)
                    return 0;

                // null move verification

                if (depth - reduction > 5 && score >= beta)
                    score = Search(p, ply, alpha, beta, depth - reduction - 4, false, 1, pv);

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
        && !isExcluded
        && !move
        && !was_null
        && !(p->Map(p->side, Pawn) & bbRelRank[p->side][rank7]) // no pawns to promote in one move
        && depth <= 3) {
        int threshold = beta - 200 - (depth - 1) * 60;

        if (eval < threshold) {
            score = QuiesceChecks(p, ply, alpha, beta, pv);
            if (score < threshold)
                return score;
        }
    }   // end of razoring code

    // Init moves and variables before entering main loop

    best = -INF;
    int ref = -1;
    if (ply) {
        ref = refutation[Fsq(oldMove[ply - 1])][Tsq(oldMove[ply - 1])];
    }

    InitMoves(p, m, move, ref, ply);

    // Main loop

    while ((move = NextMove(m, &moveType)))
    {
        histScore = GetHistScore(p, move);
        SetCaptureSquare(p, move, ply);

        if (moveType == MV_BADCAPT && depth <= seeDepth)
        {
            moveSEEscore = Swap(p, Fsq(move), Tsq(move));
        }

        // Singular extension

        bool extend = false;

        if (depth > singularDepth &&
            singularMove &&
            move == singularMove &&
            singularExtension &&
            excludedMove == dummyMove) {

            int mockPv[MAX_PLY];
            int newAlpha = -singularScore - 50;
            excludedMove = move;
            int sc = Search(p, ply + 1, newAlpha, newAlpha + 1, (depth - 1) / 2, false, true, mockPv);
            excludedMove = dummyMove;

            if (abortSearch)
                return alpha;

            if (sc <= newAlpha) {
                extend = true;
            }
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

        if (extend)
            newDepth++; // singular extension
        else if (InCheck(p) && (isPv || depth < 9))
            newDepth++; // check extension
        else if ((depth < 9 && isPv) && Tsq(move) == captureSquare[ply - 1]) // TODO: test || isPv
            newDepth++; // recapture extension

        //else if (depth >= 7 && move == hashMove && histScore > 800)
        //    newDepth++; // history extension

        // SEE pruning of bad captures

        if (!isInCheck
            && !InCheck(p)
            && moveType == MV_BADCAPT
            && depth <= seeDepth
            && !isPv)
        {
            if (moveSEEscore > seeCaptStep * depth) { // yes, sign is correct
                p->UndoMove(move, u);
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
            // Basic reduction

            reduction = LMR.table[isPv][depth][movesTried];

            // Increase on bad history

            reduction += (histScore < 200);

            // Increase non-improving non-pv reduction

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

        // Late move reduction of bad captures

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
            score = -Search(p, ply + 1, -beta, -alpha, newDepth, false, 0, new_pv);
        else {
            score = -Search(p, ply + 1, -alpha - 1, -alpha, newDepth, false, 0, new_pv);
            if (!abortSearch && !abortThread && score > alpha /* && score < beta*/)
                score = -Search(p, ply + 1, -beta, -alpha, newDepth, false, 0, new_pv);
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

            // Butterfly history update

            UpdateHistory(p, oldMove[ply - 1], move, depth, ply);
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

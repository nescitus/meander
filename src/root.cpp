#include "rodent.h"
#include "timer.h"
#include <thread>

void Think(Position* p, int* pv) {

    SetStrength();
    progSide = p->side;
    InitWeights();
    mainEngine.ClearHist();
    helpEngine.ClearHist();
    tt_date = (tt_date + 1) & 255;
    nodes = 0;
    abortSearch = 0;
    abortThread = 0;
    Timer.SetStartTime();
    Iterate(p, pv);
}

void SetStrength()
{
    evalBlur = 0;
    if (engineLevel == 0)
    {
        Timer.SetData(MAX_NODES, 0); // no node limit
    }
    else
    {
        const int eloFloor = engineLevel - 25;
        const int eloCeiling = engineLevel + 25;
        int actualRating = rand() % (eloCeiling - eloFloor + 1) + eloFloor;
        int nodesToSearch = (int)(pow(1.0069555500567, (((actualRating) / 1000) - 1) + (actualRating - 1000)) * 128);
        Timer.SetData(MAX_NODES, nodesToSearch);

        if (engineLevel < 1500)
            evalBlur = (1500 - engineLevel) / 3;
    }
}

void task1(Position* p, int depth, int* pv, int lastScore, int* cur_val)
{
    abortThread = 0;
    *cur_val = mainEngine.Widen(p, root_depth, pv, lastScore);
    abortThread = 1;
}

void task2(Position* p, int depth, int* pv, int lastScore)
{
    helpEngine.Widen(p, root_depth, pv, lastScore);
}

void Iterate(Position* p, int* pv) {

    int pv2[MAX_PLY];
    Position p2;
    p2.Copy(p);

    int val = 0, cur_val = 0;
    Bitboard nps = 0;
    Timer.SetIterationTiming();

    root_depth = 1;
    cur_val = mainEngine.Widen(p, root_depth, pv, cur_val);

    // TODO: use Perft() to reduce max depth if only one move is available

    for (root_depth = 2; root_depth <= Timer.GetData(MAX_DEPTH); root_depth++) {
        int elapsed = Timer.GetElapsedTime();
        if (elapsed) nps = nodes * 1000 / elapsed;
        printf("info depth %d time %d nodes %I64d nps %I64d\n", root_depth, elapsed, nodes, nps);
        abortThread = 0;
        std::thread t1(task1, p, root_depth, pv, cur_val, &cur_val);
        // std::thread t2(task2, &p2, root_depth, pv2, cur_val);
        t1.join();
        //t2.join();
        mainEngine.depthReached = root_depth;
        if (abortSearch || Timer.FinishIteration())
            break;
        val = cur_val;
    }

}

// @Widen() performs aspiration search, progressively widening the window.
// Code structere modelled after Senpai 1.0.

int Engine::Widen(Position* p, int depth, int* pv, int lastScore)
{
    int currentValue = lastScore, alpha, beta;
    if (depth > 6 && lastScore < MAX_EVAL) {
        for (int margin = 12; margin < 500; margin *= 2)
        {
            alpha = lastScore - margin;
            beta = lastScore + margin;
            currentValue = Search(p, 0, alpha, beta, depth, false, 0, pv);

            if (abortSearch || abortThread)
                break;

            if (currentValue < alpha) {
                Timer.OnFailLow();
            }

            if (currentValue > alpha && currentValue < beta)
                return currentValue;            // we have finished within the window

            if (currentValue > MAX_EVAL) break; // verify mate searching with infinite bounds
        }
    }

    currentValue = Search(p, 0, -INF, INF, root_depth, false, 0, pv);      // full window search
    return currentValue;
}


#include "meander.h"
#include <assert.h>

void Engine::ClearHist(void) {

  for (int i = 0; i < 12; i++)
      for (int j = 0; j < 64; j++) {
          triesHistory[i][j] = 0;
          cutoffHistory[i][j] = 0;
      }

  for (int i = 0; i < MAX_PLY; i++) {
    killer[i][0] = 0;
    killer[i][1] = 0;
  }

  for (int i = 0; i < 64; i++)
      for (int j = 0; j < 64; j++)
          refutation[i][j] = 0;
}

void Engine::UpdateTried(Position* p, int move, int depth)
{
    // Don't update stuff used for move ordering if a move changes material balance

    if (p->pc[Tsq(move)] != NO_PC || IsProm(move) || MoveType(move) == EP_CAP)
        return;

    int fromSquare = Fsq(move);
    int toSquare = Tsq(move);

    triesHistory[p->pc[fromSquare]][toSquare] += HistInc(depth);

    if (triesHistory[p->pc[fromSquare]][toSquare] > 16384)
        Trim();
}

void Engine::UpdateHistory(Position *p, int lastMove, int move, int depth, int ply) {

  // Don't update stuff used for move ordering if a move changes material balance

  if (p->pc[Tsq(move)] != NO_PC || IsProm(move) || MoveType(move) == EP_CAP)
    return;

  // Increment history counter

  cutoffHistory[p->pc[Fsq(move)]][Tsq(move)] += HistInc(depth);

  // Prevent history counters from growing too high

  if (cutoffHistory[p->pc[Fsq(move)]][Tsq(move)] > (1 << 15))
      Trim();

  // Update killer moves, taking care that they are different

  if (move != killer[ply][0]) {
    killer[ply][1] = killer[ply][0];
    killer[ply][0] = move;
  }

  // Update refutation move

  if (lastMove != -1)
      refutation[Fsq(lastMove)][Tsq(lastMove)] = move;
}

void Engine::Trim() {
    {
        for (int i = 0; i < 12; i++)
            for (int j = 0; j < 64; j++) {
                cutoffHistory[i][j] /= 2;
                triesHistory[i][j] /= 2;
            }
    }
}

int Engine::HistInc(int depth) {
    return (depth-1) * (depth-1);
}

int Engine::GetHistScore(Position* p, int move)
{
    int tries = triesHistory[p->pc[Fsq(move)]][Tsq(move)];

    if (tries == 0)
        return 0;

    int cutoffs = cutoffHistory[p->pc[Fsq(move)]][Tsq(move)];

    return (1000 * cutoffs) / tries;
}
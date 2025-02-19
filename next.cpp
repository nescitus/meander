#include "rodent.h"
#include <assert.h>

void Engine::InitMoves(Position *p, MOVES *m, int trans_move, int refutation, int ply) {

  m->p = p;
  m->phase = 0;
  m->trans_move = trans_move;
  m->killer1 = killer[ply][0];
  m->killer2 = killer[ply][1];
  m->refutation = refutation;
}

int Engine::NextMove(MOVES *m, int *flag) {

  int move;

  switch (m->phase) {
  case 0: // return transposition table move, if legal
    move = m->trans_move;
    if (move && Legal(m->p, move)) {
      m->phase = 1;
      *flag = MV_HASH;
      return move;
    }

  case 1: // helper phase: generate captures
    m->last = GenerateCaptures(m->p, m->move);
    ScoreCaptures(m);
    m->next = m->move;
    m->badp = m->bad;
    m->phase = 2;

  case 2: // return good captures, save bad ones on the separate list
    while (m->next < m->last) {
      move = SelectBest(m);

      if (move == m->trans_move)
        continue;

      if (IsBadCapture(m->p, move)) {
        *m->badp++ = move;
        continue;
      }
      *flag = MV_CAPTURE;
      return move;
    }

  case 3:  // first killer move
    move = m->killer1;
    if (move && move != m->trans_move &&
      m->p->pc[Tsq(move)] == NO_PC && Legal(m->p, move)) {
      m->phase = 4;
      *flag = MV_KILLER;
      return move;
    }

  case 4:  // second killer move
    move = m->killer2;
    if (move && move != m->trans_move &&
      m->p->pc[Tsq(move)] == NO_PC && Legal(m->p, move)) {
      m->phase = 5;
      *flag = MV_KILLER;
      return move;
    }

  case 5:  // refutation move
      move = m->refutation;
      if (move && move != m->trans_move && move != m->killer1 && move != m->killer2 && move != 0 &&
          m->p->pc[Tsq(move)] == NO_PC && Legal(m->p, move)) {
          m->phase = 6;
          *flag = MV_NORMAL;
          return move;
      }

  case 6:  // helper phase: generate quiet moves
    m->last = GenerateQuiet(m->p, m->move);
    ScoreQuiet(m);
    m->next = m->move;
    m->phase = 7;

  case 7:  // return quiet moves
    while (m->next < m->last) {
      move = SelectBest(m);
      if (move == m->trans_move ||
        move == m->killer1 ||
        move == m->killer2 ||
        move == m->refutation
          )
        continue;
      *flag = MV_NORMAL;
      return move;
    }

    m->next = m->bad;
    m->phase = 8;

  case 8: // return bad captures
    if (m->next < m->badp) {
      *flag = MV_BADCAPT;
      return *m->next++;
    }
  }
  return 0;
}

int Engine::NextCaptureOrCheck(MOVES* m, int* flag)
{
    int move;

    switch (m->phase) {
    case 0: // return transposition table move, if legal
        move = m->trans_move;
        if (move && Legal(m->p, move)) {
            m->phase = 1;
            *flag = MV_HASH;
            return move;
        }
        // fallthrough

    case 1: // helper phase: generate captures
        m->last = GenerateCaptures(m->p, m->move);
        ScoreCaptures(m);
        m->next = m->move;
        m->badp = m->bad;
        m->phase = 2;
        // fallthrough

    case 2: // return good captures, prune bad ones
        while (m->next < m->last) {
            move = SelectBest(m);
            if (move == m->trans_move)
                continue;
            if (IsBadCapture(m->p, move)) {
                continue;
            }
            *flag = MV_CAPTURE;
            return move;
        }
        // fallthrough

    case 3: // first killer move
        move = m->killer1;
        if (move && move != m->trans_move
            && m->p->pc[Tsq(move)] == NO_PC
            && Legal(m->p, move)) {
            m->phase = 4;
            *flag = MV_KILLER;
            return move;
        }
        // fallthrough

    case 4: // second killer move
        move = m->killer2;
        if (move && move != m->trans_move
            && m->p->pc[Tsq(move)] == NO_PC && Legal(m->p, move)) {
            m->phase = 5;
            *flag = MV_KILLER;
            return move;
        }
        // fallthrough

    case 5: // helper phase: generate checking moves
        m->last = GenerateChecks(m->p, m->move);
        ScoreQuiet(m);
        m->next = m->move;
        m->phase = 6;
        // fallthrough

    case 6: // return checking moves
        while (m->next < m->last) {
            move = SelectBest(m);
            if (move == m->trans_move
                || move == m->killer1
                || move == m->killer2)
                continue;
            *flag = MV_NORMAL;
            return move;
        }
    }
    return 0;
}

void Engine::InitCaptures(Position *p, MOVES *m) {

  m->p = p;
  m->last = GenerateCaptures(m->p, m->move);
  ScoreCaptures(m);
  m->next = m->move;
}

int Engine::NextCapture(MOVES *m) {

  int move;

  while (m->next < m->last) {
    move = SelectBest(m);
    return move;
  }
  return 0;
}

void Engine::ScoreCaptures(MOVES *m) {

  int *movep, *valuep;

  valuep = m->value;
  for (movep = m->move; movep < m->last; movep++)
    *valuep++ = MvvLva(m->p, *movep);
}

void Engine::ScoreQuiet(MOVES *m) {

  int *movep, *valuep;

  valuep = m->value;
  for (movep = m->move; movep < m->last; movep++)
    *valuep++ = GetHistScore(m->p, *movep);
}

int SelectBest(MOVES *m) {

  int *movep, *valuep, aux;

  valuep = m->value + (m->last - m->move) - 1;
  for (movep = m->last - 1; movep > m->next; movep--) {
    if (*valuep > *(valuep - 1)) {
      aux = *valuep;
      *valuep = *(valuep - 1);
      *(valuep - 1) = aux;
      aux = *movep;
      *movep = *(movep - 1);
      *(movep - 1) = aux;
    }
    valuep--;
  }
  return *m->next++;
}

bool IsBadCapture(Position *p, int move) {

  int fsq = Fsq(move);
  int tsq = Tsq(move);

  // Captures that gain material or capture equal piece are good by definition
  // (includes BxN and NxB)

  if (tp_value[TpOnSq(p, tsq)] >= tp_value[TpOnSq(p, fsq)])
    return false;

  // En passant captures are good by definition

  if (MoveType(move) == EP_CAP)
    return false;

  // We have to evaluate this capture using expensive Static Exchange Evaluation

  return Swap(p, fsq, tsq) < 0;
}

int MvvLva(Position *p, int move) {

  // Captures

  if (p->pc[Tsq(move)] != NO_PC)
    return TpOnSq(p, Tsq(move)) * 6 + 5 - TpOnSq(p, Fsq(move));

  // Non-capturing promotions
  
  if (IsProm(move)) return PromType(move) - 5;

  return 5;
}
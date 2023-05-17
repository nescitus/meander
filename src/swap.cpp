#include "meander.h"

int Swap(Position *p, int from, int to) {

  int side, ply, type, score[32];
  Bitboard bbAttackers, bbOcc, bbType;

  bbAttackers = AttacksTo(p, to);
  bbOcc = p->Filled();
  score[0] = tp_value[TpOnSq(p, to)];
  type = TpOnSq(p, from);
  bbOcc ^= SqBb(from);
  bbAttackers |= (Att.Bish(bbOcc, to) & p->MapDiag() ) |
                 (Att.Rook(bbOcc, to) & p->MapStraight());
  bbAttackers &= bbOcc;
  side = Opp(p->side);
  ply = 1;
  while (bbAttackers & p->cl_bb[side]) {
    if (type == King) {
      score[ply++] = INF;
      break;
    }
    score[ply] = -score[ply - 1] + tp_value[type];
    for (type = Pawn; type <= King; type++)
      if ((bbType = p->Map(side, type) & bbAttackers))
        break;
    bbOcc ^= bbType & -bbType;
    bbAttackers |= (Att.Bish(bbOcc, to) & (p->MapDiag())) |
                   (Att.Rook(bbOcc, to) & (p->MapStraight()));
    bbAttackers &= bbOcc;
    side ^= 1;
    ply++;
  }
  while (--ply)
    score[ply - 1] = -Max(-score[ply - 1], score[ply]);
  return score[0];
}

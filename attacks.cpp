#include "rodent.h"

Bitboard AttacksFrom(Position *p, int sq) {

  switch (TpOnSq(p, sq)) {
  case Pawn:
    return Att.Pawn(Cl(p->pc[sq]), sq);
  case Knight:
    return Att.Knight(sq);
  case Bishop:
    return Att.Bish(p->Filled(), sq);
  case Rook:
    return Att.Rook(p->Filled(), sq);
  case Queen:
    return Att.Queen(p->Filled(), sq);
  case King:
    return Att.King(sq);
  }
  return 0;
}

Bitboard AttacksTo(Position *p, int sq) {

  return (p->Map(White, Pawn) & Att.Pawn(Black, sq)) |
         (p->Map(Black, Pawn) & Att.Pawn(White, sq)) |
         (p->tp_bb[Knight] & Att.Knight(sq)) |
         ((p->tp_bb[Bishop] | p->tp_bb[Queen]) & Att.Bish(p->Filled(), sq)) |
         ((p->tp_bb[Rook] | p->tp_bb[Queen]) & Att.Rook(p->Filled(), sq)) |
         (p->tp_bb[King] & Att.King(sq));
}

int Attacked(Position *p, int sq, int side) {

  return (p->Map(side, Pawn) & Att.Pawn(Opp(side),sq)) ||
         (p->Map(side, Knight) &Att.Knight(sq)) ||
         ((p->Map(side, Bishop) | p->Map(side, Queen)) & Att.Bish(p->Filled(), sq)) ||
         ((p->Map(side, Rook) | p->Map(side, Queen)) & Att.Rook(p->Filled(), sq)) ||
         (p->Map(side, King) & Att.King(sq));
}

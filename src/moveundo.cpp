//  Rodent, a UCI chess playing engine derived from Sungorus 1.4
//  Copyright (C) 2009-2011 Pablo Vazquez (Sungorus author)
//  Copyright (C) 2011-2015 Pawel Koziol
//
//  Rodent is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published
//  by the Free Software Foundation, either version 3 of the License,
//  or (at your option) any later version.
//
//  Rodent is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty
//  of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
//  See the GNU General Public License for more details.
//
//  You should have received a copy of the GNU General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "rodent.h"

void Position::UndoMove(int move, UNDO *u) {

  int sd  = Opp(side);
  int op  = side;
  int fsq = Fsq(move);
  int tsq = Tsq(move);
  int ftp = Tp(pc[tsq]);    // moving piece
  int ttp = u->ttp;

  castle_flags = u->castle_flags;
  ep_sq = u->ep_sq;
  rev_moves = u->rev_moves;
  pawn_key = u->pawn_key;
  hash_key = u->hash_key;
  head--;
  pc[fsq] = Pc(sd, ftp);
  pc[tsq] = NO_PC;
  cl_bb[sd] ^= SqBb(fsq) | SqBb(tsq);
  tp_bb[ftp] ^= SqBb(fsq) | SqBb(tsq);

  // Update king location

  if (ftp == King) king_sq[sd] = fsq;

  // Undo capture

  if (ttp != NO_TP) {
    pc[tsq] = Pc(op, ttp);
    cl_bb[op] ^= SqBb(tsq);
    tp_bb[ttp] ^= SqBb(tsq);
    phase += phase_value[ttp];
    cnt[op][ttp]++;
  }

  switch (MoveType(move)) {

  case NORMAL:
    break;

  case CASTLE:

    // define complementary rook move

    switch (tsq) {
      case C1: { fsq = A1; tsq = D1; break; }
      case G1: { fsq = H1; tsq = F1; break; }
      case C8: { fsq = A8; tsq = D8; break; }
      case G8: { fsq = H8; tsq = F8; break; }
    }

    pc[tsq] = NO_PC;
    pc[fsq] = Pc(sd, Rook);
    cl_bb[sd] ^= SqBb(fsq) | SqBb(tsq);
    tp_bb[Rook] ^= SqBb(fsq) | SqBb(tsq);
    break;

  case EP_CAP:
    tsq ^= 8;
    pc[tsq] = Pc(op, Pawn);
    cl_bb[op] ^= SqBb(tsq);
    tp_bb[Pawn] ^= SqBb(tsq);
    phase += phase_value[Pawn];
    cnt[op][Pawn]++;
    break;

  case EP_SET:
    break;

  case N_PROM: case B_PROM: case R_PROM: case Q_PROM:
    pc[fsq] = Pc(sd, Pawn);
    tp_bb[Pawn] ^= SqBb(fsq);
    tp_bb[ftp] ^= SqBb(fsq);
    phase += phase_value[Pawn] - phase_value[ftp];
    cnt[sd][Pawn]++;
    cnt[sd][ftp]--;
    break;
  }
  side ^= 1;
}

void Position::UndoNull(UNDO *u) {

  ep_sq = u->ep_sq;
  hash_key = u->hash_key;
  head--;
  rev_moves--;
  side ^= 1;
}

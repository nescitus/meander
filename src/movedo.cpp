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

void Position::DoMove(int move, UNDO *u) {

  int sd = side;          // moving side
  int op = Opp(sd);       // side not to move
  int fsq = Fsq(move);    // start square
  int tsq = Tsq(move);    // target square
  int ftp = Tp(pc[fsq]);  // moving piece
  int ttp = Tp(pc[tsq]);  // captured piece

  // Save data for undoing a move

  u->ttp = ttp;
  u->castle_flags = castle_flags;
  u->ep_sq = ep_sq;
  u->rev_moves = rev_moves;
  u->hash_key = hash_key;
  u->pawn_key = pawn_key;
  rep_list[head++] = hash_key;

  // Update reversible moves counter

  if (ftp == Pawn || ttp != NO_TP) rev_moves = 0;
  else                          rev_moves++;

  // Update pawn hash

  if (ftp == Pawn || ftp == King)
    pawn_key ^= pieceKey[Pc(sd, ftp)][fsq] ^ pieceKey[Pc(sd, ftp)][tsq];

  // Update castling rights

  hash_key ^= castleKey[castle_flags];
  castle_flags &= castle_mask[fsq] & castle_mask[tsq];
  hash_key ^= castleKey[castle_flags];

  // Clear en passant square

  if (ep_sq != NoSquare) {
    hash_key ^= enPassantKey[File(ep_sq)];
    ep_sq = NoSquare;
  }

  pc[fsq] = NO_PC;
  pc[tsq] = Pc(sd, ftp);
  hash_key ^= pieceKey[Pc(sd, ftp)][fsq] ^ pieceKey[Pc(sd, ftp)][tsq];
  cl_bb[sd] ^= Paint(fsq) | Paint(tsq);
  tp_bb[ftp] ^= Paint(fsq) | Paint(tsq);

  // Update king location

  if (ftp == King)
    king_sq[sd] = tsq;

  // Capture enemy piece

  if (ttp != NO_TP) {
    hash_key ^= pieceKey[Pc(op, ttp)][tsq];

  if (ttp == Pawn)
    pawn_key ^= pieceKey[Pc(op, ttp)][tsq];

    cl_bb[op] ^= Paint(tsq);
    tp_bb[ttp] ^= Paint(tsq);
    phase -= phase_value[ttp];
    cnt[op][ttp]--;
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
  
    pc[fsq] = NO_PC;
    pc[tsq] = Pc(sd, Rook);
    hash_key ^= pieceKey[Pc(sd, Rook)][fsq] ^ pieceKey[Pc(sd, Rook)][tsq];
    cl_bb[sd] ^= Paint(fsq) | Paint(tsq);
    tp_bb[Rook]  ^= Paint(fsq) | Paint(tsq);
    break;

  case EP_CAP:
    tsq ^= 8;
    pc[tsq] = NO_PC;
    hash_key ^= pieceKey[Pc(op, Pawn)][tsq];
    pawn_key ^= pieceKey[Pc(op, Pawn)][tsq];
    cl_bb[op] ^= Paint(tsq);
    tp_bb[Pawn] ^= Paint(tsq);
    phase -= phase_value[Pawn];
    cnt[op][Pawn]--;
    break;

  case EP_SET:
    tsq ^= 8;
  if (Att.Pawn(sd,tsq) & (cl_bb[op] & tp_bb[Pawn]) ) {
      ep_sq = tsq;
      hash_key ^= enPassantKey[File(tsq)];
    }
    break;

  case N_PROM: case B_PROM: case R_PROM: case Q_PROM:
    ftp = PromType(move);
    pc[tsq] = Pc(sd, ftp);
    hash_key ^= pieceKey[Pc(sd, Pawn)][tsq] ^ pieceKey[Pc(sd, ftp)][tsq];
    pawn_key ^= pieceKey[Pc(sd, Pawn)][tsq];
    tp_bb[Pawn] ^= SqBb(tsq);
    tp_bb[ftp] ^= SqBb(tsq);
    phase += phase_value[ftp] - phase_value[Pawn];
    cnt[sd][Pawn]--;
    cnt[sd][ftp]++;
    break;
  }

  // Invert side to move

  side ^= 1;
  hash_key ^= SIDE_RANDOM;
}

void Position::DoNull(UNDO *u) {

  u->ep_sq = ep_sq;
  u->hash_key = hash_key;

  // Update repetition list

  rep_list[head++] = hash_key;
  rev_moves++;
  
  // Clear en passant square

  if (ep_sq != NoSquare) {
    hash_key ^= enPassantKey[File(ep_sq)];
    ep_sq = NoSquare;
  }

  // Invert side to move

  side ^= 1;
  hash_key ^= SIDE_RANDOM;
}

#include "meander.h"
#include "stdio.h"

int *GenerateCaptures(Position *p, int *list) {

  Bitboard bbPieces, bbMoves, bbEnemy;
  int from, to;
  int side = p->side;

  bbEnemy = p->cl_bb[Opp(side)];

  if (side == White) {

    // White pawn promotions with capture

    bbMoves = ((p->Map(White, Pawn) & ~FILE_A_BB & RANK_7_BB) << 7) & p->cl_bb[Black];
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (Q_PROM << 12) | (to << 6) | (to - 7);
      *list++ = (R_PROM << 12) | (to << 6) | (to - 7);
      *list++ = (B_PROM << 12) | (to << 6) | (to - 7);
      *list++ = (N_PROM << 12) | (to << 6) | (to - 7);
    }

  // White pawn promotions with capture

    bbMoves = ((p->Map(White, Pawn) & ~FILE_H_BB & RANK_7_BB) << 9) & p->cl_bb[Black];
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (Q_PROM << 12) | (to << 6) | (to - 9);
      *list++ = (R_PROM << 12) | (to << 6) | (to - 9);
      *list++ = (B_PROM << 12) | (to << 6) | (to - 9);
      *list++ = (N_PROM << 12) | (to << 6) | (to - 9);
    }

  // White pawn promotions without capture

    bbMoves = ((p->Map(White, Pawn) & RANK_7_BB) << 8) & p->Empty();
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (Q_PROM << 12) | (to << 6) | (to - 8);
      *list++ = (R_PROM << 12) | (to << 6) | (to - 8);
      *list++ = (B_PROM << 12) | (to << 6) | (to - 8);
      *list++ = (N_PROM << 12) | (to << 6) | (to - 8);
    }

  // White pawn captures

    bbMoves = ((p->Map(White, Pawn) & ~FILE_A_BB & ~RANK_7_BB) << 7) & p->cl_bb[Black];
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (to << 6) | (to - 7);
    }

  // White pawn captures

    bbMoves = ((p->Map(White, Pawn) & ~FILE_H_BB & ~RANK_7_BB) << 9) & p->cl_bb[Black];
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (to << 6) | (to - 9);
    }

  // White en passant capture

    if ((to = p->ep_sq) != NoSquare) {
      if (((p->Map(White, Pawn) & ~FILE_A_BB) << 7) & Paint(to))
        *list++ = (EP_CAP << 12) | (to << 6) | (to - 7);
      if (((p->Map(White, Pawn) & ~FILE_H_BB) << 9) & Paint(to))
        *list++ = (EP_CAP << 12) | (to << 6) | (to - 9);
    }
  } else {

    // Black pawn promotions with capture

    bbMoves = ((p->Map(Black, Pawn) & ~FILE_A_BB & RANK_2_BB) >> 9) & p->cl_bb[White];
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (Q_PROM << 12) | (to << 6) | (to + 9);
      *list++ = (R_PROM << 12) | (to << 6) | (to + 9);
      *list++ = (B_PROM << 12) | (to << 6) | (to + 9);
      *list++ = (N_PROM << 12) | (to << 6) | (to + 9);
    }

  // Black pawn promotions with capture

    bbMoves = ((p->Map(Black, Pawn) & ~FILE_H_BB & RANK_2_BB) >> 7) & p->cl_bb[White];
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (Q_PROM << 12) | (to << 6) | (to + 7);
      *list++ = (R_PROM << 12) | (to << 6) | (to + 7);
      *list++ = (B_PROM << 12) | (to << 6) | (to + 7);
      *list++ = (N_PROM << 12) | (to << 6) | (to + 7);
    }

  // Black pawn promotions

    bbMoves = ((p->Map(Black, Pawn) & RANK_2_BB) >> 8) & p->Empty();
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (Q_PROM << 12) | (to << 6) | (to + 8);
      *list++ = (R_PROM << 12) | (to << 6) | (to + 8);
      *list++ = (B_PROM << 12) | (to << 6) | (to + 8);
      *list++ = (N_PROM << 12) | (to << 6) | (to + 8);
    }

  // Black pawn captures, excluding promotions

    bbMoves = ((p->Map(Black, Pawn) & ~FILE_A_BB & ~RANK_2_BB) >> 9) & bbEnemy;
    while (bbMoves) { 
      to = PopFirstBit(&bbMoves);
      *list++ = (to << 6) | (to + 9);
    }

  // Black pawn captures, excluding promotions

    bbMoves = ((p->Map(Black, Pawn) & ~FILE_H_BB & ~RANK_2_BB) >> 7) & bbEnemy;
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (to << 6) | (to + 7);
    }

  // Black en passant capture

    if ((to = p->ep_sq) != NoSquare) {
      if (((p->Map(Black, Pawn) & ~FILE_A_BB) >> 9) & Paint(to))
        *list++ = (EP_CAP << 12) | (to << 6) | (to + 9);
      if (((p->Map(Black, Pawn) & ~FILE_H_BB) >> 7) & Paint(to))
        *list++ = (EP_CAP << 12) | (to << 6) | (to + 7);
    }
  }

  // Captures by knight

  bbPieces = p->Map(side, Knight);
  while (bbPieces) {
    from = PopFirstBit(&bbPieces);
    bbMoves = Att.Knight(from) & bbEnemy;
    list = SerializeMoves(list, bbMoves, from);
  }

  // Captures by bishop

  bbPieces = p->Map(side, Bishop);
  while (bbPieces) {
    from = PopFirstBit(&bbPieces);
    bbMoves = Att.Bish(p->Filled(), from) & bbEnemy;
    list = SerializeMoves(list, bbMoves, from);
  }

  // Captures by rook

  bbPieces = p->Map(side, Rook);
  while (bbPieces) {
    from = PopFirstBit(&bbPieces);
    bbMoves = Att.Rook(p->Filled(), from) & bbEnemy;
    list = SerializeMoves(list, bbMoves, from);
  }

  // Captures by queen

  bbPieces = p->Map(side, Queen);
  while (bbPieces) {
    from = PopFirstBit(&bbPieces);
    bbMoves = Att.Queen(p->Filled(), from) & bbEnemy;
    list = SerializeMoves(list, bbMoves, from);
  }

  // Captures by king

  bbMoves = Att.King(KingSq(p, side)) & bbEnemy;
  list = SerializeMoves(list, bbMoves, KingSq(p, side));

  return list;
}

int *GenerateQuiet(Position *p, int *list) {

  Bitboard bbPieces, bbMoves;
  int from, to;
  int side = p->side;

  if (side == White) {

    // White short castle

    if ((p->castle_flags & 1) && !(p->Filled() & (Bitboard)0x0000000000000060))
      if (!Attacked(p, E1, Black) && !Attacked(p, F1, Black))
        *list++ = (CASTLE << 12) | (G1 << 6) | E1;

  // White long castle

    if ((p->castle_flags & 2) && !(p->Filled() & (Bitboard)0x000000000000000E))
      if (!Attacked(p, E1, Black) && !Attacked(p, D1, Black))
        *list++ = (CASTLE << 12) | (C1 << 6) | E1;

  // White double pawn moves

    bbMoves = ((((p->Map(White, Pawn) & RANK_2_BB) << 8) & p->Empty()) << 8) & p->Empty();
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (EP_SET << 12) | (to << 6) | (to - 16);
    }

  // White normal pawn moves

    bbMoves = ((p->Map(White, Pawn) & ~RANK_7_BB) << 8) & p->Empty();
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (to << 6) | (to - 8);
    }
  } else {

    // Black short castle

    if ((p->castle_flags & 4) && !(p->Filled() & (Bitboard)0x6000000000000000))
      if (!Attacked(p, E8, White) && !Attacked(p, F8, White))
        *list++ = (CASTLE << 12) | (G8 << 6) | E8;

  // Black long castle

    if ((p->castle_flags & 8) && !(p->Filled() & (Bitboard)0x0E00000000000000))
      if (!Attacked(p, E8, White) && !Attacked(p, D8, White))
        *list++ = (CASTLE << 12) | (C8 << 6) | E8;

  // Black double pawn moves

    bbMoves = ((((p->Map(Black, Pawn) & RANK_7_BB) >> 8) & p->Empty()) >> 8) & p->Empty();
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (EP_SET << 12) | (to << 6) | (to + 16);
    }

  // Black single pawn moves

    bbMoves = ((p->Map(Black, Pawn) & ~RANK_2_BB) >> 8) & p->Empty();
    while (bbMoves) {
      to = PopFirstBit(&bbMoves);
      *list++ = (to << 6) | (to + 8);
    }
  }

  // Knight moves

  bbPieces = p->Map(side, Knight);
  while (bbPieces) {
    from = PopFirstBit(&bbPieces);
    bbMoves = Att.Knight(from) & p->Empty();
    list = SerializeMoves(list, bbMoves, from);
  }

  // Bishop moves

  bbPieces = p->Map(side, Bishop);
  while (bbPieces) {
    from = PopFirstBit(&bbPieces);
    bbMoves = Att.Bish(p->Filled(), from) & p->Empty();
    list = SerializeMoves(list, bbMoves, from);
  }

  // Rook moves

  bbPieces = p->Map(side, Rook);
  while (bbPieces) {
    from = PopFirstBit(&bbPieces);
    bbMoves = Att.Rook(p->Filled(), from) & p->Empty();
    list = SerializeMoves(list, bbMoves, from);
  }

  // Queen moves

  bbPieces = p->Map(side, Queen);
  while (bbPieces) {
    from = PopFirstBit(&bbPieces);
    bbMoves = Att.Queen(p->Filled(), from) & p->Empty();
    list = SerializeMoves(list, bbMoves, from);
  }

  // King moves

  bbMoves = Att.King(KingSq(p, side)) & p->Empty();
  list = SerializeMoves(list, bbMoves, KingSq(p, side));

  return list;
}

int* GenerateChecks(Position* p, int* list)
{
    Bitboard pieces, moves;
    int side, from, to;

    side = p->side;
    int ksq = p->king_sq[side ^ 1];
    Bitboard pawnChecks = FwdOf(SidesOf(Paint(ksq)), side ^ 1);
    Bitboard nCheck = Att.Knight(ksq);
    Bitboard bCheck = Att.Bish(p->Filled(), ksq);
    Bitboard rCheck = Att.Rook(p->Filled(), ksq);
    Bitboard qCheck = bCheck | rCheck;

    if (side == White) {

        // White double pawn moves

        moves = ((ShiftNorth(p->Map(White, Pawn) & Mask.r[rank2]) & p->Empty()) << 8) & p->Empty(); // TODO: reorganize
        moves &= pawnChecks;
        while (moves) {
            to = PopFirstBit(&moves);
            *list++ = (EP_SET << 12) | (to << 6) | (to - 16);
        }

        // White normal pawn moves

        moves = ShiftNorth(p->Map(White, Pawn) & ~Mask.r[rank7]) & p->Empty();
        moves &= pawnChecks;
        while (moves) {
            to = PopFirstBit(&moves);
            *list++ = (to << 6) | (to - 8);
        }
    }
    else {

        // Black double pawn moves

        moves = ((ShiftSouth(p->Map(Black, Pawn) & Mask.r[rank7]) & p->Empty()) >> 8) & p->Empty(); // TODO: reorganize
        moves &= pawnChecks;
        while (moves) {
            to = PopFirstBit(&moves);
            *list++ = (EP_SET << 12) | (to << 6) | (to + 16);
        }

        // Black single pawn moves

        moves = ShiftSouth(p->Map(Black, Pawn) & ~Mask.r[rank2]) & p->Empty();
        moves &= pawnChecks;
        while (moves) {
            to = PopFirstBit(&moves);
            *list++ = (to << 6) | (to + 8);
        }
    }

    // knight checks

    Bitboard checkers = p->Map(side, Queen) | p->Map(side, Rook) | p->Map(side, Bishop);
    checkers &= (Att.rAttOnEmpty[ksq] | Att.bAttOnEmpty[ksq]);

    pieces = p->Map(side, Knight);
    while (pieces) {
        from = PopFirstBit(&pieces);
        bool canDiscoverCheck = CanDiscoverCheck(p, checkers, side ^ 1, from);
        moves = Att.Knight(from) & p->Empty();
        if (!canDiscoverCheck) moves &= nCheck;
        list = SerializeMoves(list, moves, from);
    }

    // Bishop checks

    checkers = p->Map(side, Queen) | p->Map(side, Rook);
    checkers &= Att.rAttOnEmpty[ksq];

    pieces = p->Map(side, Bishop);
    while (pieces) {
        from = PopFirstBit(&pieces);
        bool canDiscoverCheck = CanDiscoverCheck(p, checkers, side ^ 1, from);
        moves = Att.Bish(p->Filled(), from) & p->Empty();
        if (!canDiscoverCheck) moves &= bCheck;
        list = SerializeMoves(list, moves, from);
    }

    // Rook checks

    checkers = p->Map(side, Queen) | p->Map(side, Bishop);
    checkers &= Att.bAttOnEmpty[ksq];

    pieces = p->Map(side, Rook);
    while (pieces) {
        from = PopFirstBit(&pieces);
        bool canDiscoverCheck = CanDiscoverCheck(p, checkers, side ^ 1, from);
        moves = Att.Rook(p->Filled(), from) & p->Empty();
        if (!canDiscoverCheck) moves &= rCheck;
        list = SerializeMoves(list, moves, from);
    }

    // Queen checks

    pieces = p->Map(side, Queen);
    while (pieces) {
        from = PopFirstBit(&pieces);
        moves = Att.Queen(p->Filled(), from) & p->Empty();
        moves &= qCheck;
        list = SerializeMoves(list, moves, from);
    }

    return list;
}

bool CanDiscoverCheck(Position* p, Bitboard checkers, int  oppo, int fromSquare)
{

    while (checkers) {

        int threatSquare = PopFirstBit(&checkers);
        Bitboard ray = Att.GetBetween(threatSquare, p->king_sq[oppo]);

        if (Paint(fromSquare) & ray) {
            if (PopCnt(ray & p->Filled()) == 1) {
                return true;
            }
        }
    }

    return false;
}

int* SerializeMoves(int* list, Bitboard moves, int from)
{
    while (moves) {
        int to = PopFirstBit(&moves);
        *list++ = CreateMove(from, to);
    }

    return list;
}

int CreateMove(int from, int to, int flag)
{
    return (flag << 12) | (to << 6) | from;
}

int CreateMove(int from, int to)
{
    return (to << 6) | from;
}

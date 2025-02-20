#include "rodent.h"

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
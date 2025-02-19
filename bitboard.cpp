#include "rodent.h"

#define FAST_POPCNT
#ifdef FAST_POPCNT 

#include <nmmintrin.h>
#include <intrin.h>

int FirstOne(Bitboard b) {
    unsigned long index;
    _BitScanForward64(&index, b);
    return index;
}

int PopCnt(Bitboard b) {
    return (int)_mm_popcnt_u64(b);
}

#else

const int bit_table[64] = {
   0,  1,  2,  7,  3, 13,  8, 19,
   4, 25, 14, 28,  9, 34, 20, 40,
   5, 17, 26, 38, 15, 46, 29, 48,
  10, 31, 35, 54, 21, 50, 41, 57,
  63,  6, 12, 18, 24, 27, 33, 39,
  16, 37, 45, 47, 30, 53, 49, 56,
  62, 11, 23, 32, 36, 44, 52, 55,
  61, 22, 43, 51, 60, 42, 59, 58
};

int FirstOne(Bitboard b) {
    return bit_table[(((b) & (~(b)+1)) * (Bitboard)0x0218A392CD3D5DBF) >> 58];
}

int PopCnt(Bitboard b) {

    Bitboard k1 = (Bitboard)0x5555555555555555;
    Bitboard k2 = (Bitboard)0x3333333333333333;
    Bitboard k3 = (Bitboard)0x0F0F0F0F0F0F0F0F;
    Bitboard k4 = (Bitboard)0x0101010101010101;

    b -= (b >> 1) & k1;
    b = (b & k2) + ((b >> 2) & k2);
    b = (b + (b >> 4)) & k3;
    return (b * k4) >> 56;
}
#endif

int PopFirstBit(Bitboard * bb) {

  Bitboard bbLocal = *bb;
  *bb &= (*bb - 1);
  return FirstOne(bbLocal);
}

Bitboard Paint(int s) {
    return ((Bitboard)1 << (s));
}

Bitboard Paint(int s1, int s2) {
    return (Paint(s1) | Paint(s2));
}

Bitboard Paint(int s1, int s2, int s3) {
    return (Paint(s1, s2) | Paint(s3));
}

Bitboard FrontSpan(Bitboard bitboard, int color)
{
    if (color == White) return FillNorth(ShiftNorth(bitboard));
    else                return FillSouth(ShiftSouth(bitboard));
}

Bitboard FwdOf(Bitboard bitboard, int color)
{
    if (color == White) return ShiftNorth(bitboard);
    else                return ShiftSouth(bitboard);
}

Bitboard ShiftFwd(Bitboard b, int c) {
    if (c == White) return ShiftNorth(b);
    else return ShiftSouth(b);
}

Bitboard FillNorth(Bitboard bb) {
  bb |= bb << 8;
  bb |= bb << 16;
  bb |= bb << 32;
  return bb;
}

Bitboard FillSouth(Bitboard bb) {
  bb |= bb >> 8;
  bb |= bb >> 16;
  bb |= bb >> 32;
  return bb;
}

Bitboard SidesOf(Bitboard bb) {
    return (ShiftWest(bb) | ShiftEast(bb));
}

Bitboard GetWPControl(Bitboard bb) {
  return (ShiftNE(bb) | ShiftNW(bb));
}

Bitboard GetBPControl(Bitboard bb) {
  return (ShiftSE(bb) | ShiftSW(bb));
}

Bitboard GetDoubleWPControl(Bitboard bb) {
    return (ShiftNE(bb) & ShiftNW(bb));
}

Bitboard GetDoubleBPControl(Bitboard bb) {
    return (ShiftSE(bb) & ShiftSW(bb));
}
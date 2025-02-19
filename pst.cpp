#include "rodent.h"
#include <stdio.h>
#include "pst.h"

void cPst::Init() 
{
    for (int sq = 0; sq < 64; sq++) {
        for (int sd = 0; sd < 2; sd++) {

            mgOne[sd][Pawn][RelSq(sq, sd)] = p_mg[sq];
            egOne[sd][Pawn][RelSq(sq, sd)] = p_eg[sq];
            mgOne[sd][Knight][RelSq(sq, sd)] = n_mg[sq];
            egOne[sd][Knight][RelSq(sq, sd)] = n_eg[sq];
            mgOne[sd][Bishop][RelSq(sq, sd)] = b_mg[sq];
            egOne[sd][Bishop][RelSq(sq, sd)] = b_eg[sq];
            mgOne[sd][Rook][RelSq(sq, sd)] = r_mg[sq];
            egOne[sd][Rook][RelSq(sq, sd)] = r_eg[sq];
            mgOne[sd][Queen][RelSq(sq, sd)] = q_mg[sq];
            egOne[sd][Queen][RelSq(sq, sd)] = q_eg[sq];
            mgOne[sd][King][RelSq(sq, sd)] = k_mg[sq];
            egOne[sd][King][RelSq(sq, sd)] = k_eg[sq];

            mgKidLow[sd][Pawn][RelSq(sq, sd)] = p_kid_low[sq];
            mgKidHigh[sd][Pawn][RelSq(sq, sd)] = p_kid_high[sq];

            mgKs[sd][Pawn][RelSq(sq, sd)] = p_ks[sq];
            mgQs[sd][Pawn][RelSq(sq, sd)] = p_qs[sq];
            mgKs[sd][Knight][RelSq(sq, sd)] = n_ks[sq];
            mgBackward[sd][RelSq(sq, sd)] = pstBackwardMg[sq];
            mgPhalanx[sd][RelSq(sq, sd)] = pstPhalanxPawnMg[sq];
            egPhalanx[sd][RelSq(sq, sd)] = pstPhalanxPawnEg[sq];
            mgDefended[sd][RelSq(sq, sd)] = pstDefendedPawnMg[sq];
            egDefended[sd][RelSq(sq, sd)] = pstDefendedPawnEg[sq];
            mgShieldedB[sd][RelSq(sq, sd)] = b_shld_mg[sq];
            mgShieldedN[sd][RelSq(sq, sd)] = n_shld_mg[sq];
            rConMg[sd][RelSq(sq, sd)] = r_con_mg[sq];
            rConEg[sd][RelSq(sq, sd)] = r_con_eg[sq];
        }

        for (int sd = 0; sd < 2; sd++) {
            for (int s1 = 0; s1 < 64; s1++)
                for (int s2 = 0; s2 < 64; s2++) {
                    pawnRelationshipMg[sd][RelSq(s1, sd)][RelSq(s2, sd)] = 0;
                    pawnRelationshipEg[sd][RelSq(s1, sd)][RelSq(s2, sd)] = 0;

                }
        }

        AddPawnRelation(A2, A3, -16, -20);
        AddPawnRelation(B2, B3, -13, -19);
        AddPawnRelation(C2, C3, -11, -19);
        AddPawnRelation(D2, D3, -14, -19);
        AddPawnRelation(E2, E3, -14, -19);
        AddPawnRelation(F2, F3, -13, -19);
        AddPawnRelation(G2, G3, -13, -19);
        AddPawnRelation(H2, H3, -16, -20);

        AddPawnRelation(A2, A4, -13, -19);
        AddPawnRelation(B2, B4, -13, -19);
        AddPawnRelation(C2, C4, -12, -19);
        AddPawnRelation(D2, D4, -13, -19);
        AddPawnRelation(E2, E4, -13, -19);
        AddPawnRelation(F2, F4, -12, -19);
        AddPawnRelation(G2, G4, -13, -19);
        AddPawnRelation(H2, H4, -13, -19);

        AddPawnRelation(A2, A5, -13, -19);
        AddPawnRelation(B2, B5, -13, -19);
        AddPawnRelation(C2, C5, -13, -19);
        AddPawnRelation(D2, D5, -13, -19);
        AddPawnRelation(E2, E5, -13, -19);
        AddPawnRelation(F2, F5, -13, -19);
        AddPawnRelation(G2, G5, -13, -19);
        AddPawnRelation(H2, H5, -13, -19);

        AddPawnRelation(A2, A6, -13, -19);
        AddPawnRelation(B2, B6, -13, -19);
        AddPawnRelation(C2, C6, -13, -19);
        AddPawnRelation(D2, D6, -13, -19);
        AddPawnRelation(E2, E6, -13, -19);
        AddPawnRelation(F2, F6, -13, -19);
        AddPawnRelation(G2, G6, -13, -19);
        AddPawnRelation(H2, H6, -13, -19);

        AddPawnRelation(A2, A7, -13, -19);
        AddPawnRelation(B2, B7, -13, -19);
        AddPawnRelation(C2, C7, -13, -19);
        AddPawnRelation(D2, D7, -13, -19);
        AddPawnRelation(E2, E7, -13, -19);
        AddPawnRelation(F2, F7, -13, -19);
        AddPawnRelation(G2, G7, -13, -19);
        AddPawnRelation(H2, H7, -13, -19);

        AddPawnRelation(A3, A4, -13, -19);
        AddPawnRelation(B3, B4, -13, -19);
        AddPawnRelation(C3, C4, -14, -19);
        AddPawnRelation(D3, D4, -13, -19);
        AddPawnRelation(E3, E4, -13, -19);
        AddPawnRelation(F3, F4, -13, -19);
        AddPawnRelation(G3, G4, -13, -19);
        AddPawnRelation(H3, H4, -13, -19);

        AddPawnRelation(A3, A5, -13, -19);
        AddPawnRelation(B3, B5, -13, -19);
        AddPawnRelation(C3, C5, -13, -19);
        AddPawnRelation(D3, D5, -13, -19);
        AddPawnRelation(E3, E5, -13, -19);
        AddPawnRelation(F3, F5, -13, -19);
        AddPawnRelation(G3, G5, -13, -19);
        AddPawnRelation(H3, H5, -13, -19);

        AddPawnRelation(A3, A6, -13, -19);
        AddPawnRelation(B3, B6, -13, -19);
        AddPawnRelation(C3, C6, -13, -19);
        AddPawnRelation(D3, D6, -13, -19);
        AddPawnRelation(E3, E6, -13, -19);
        AddPawnRelation(F3, F6, -13, -19);
        AddPawnRelation(G3, G6, -13, -19);
        AddPawnRelation(H3, H6, -13, -19);

        AddPawnRelation(A3, A7, -13, -19);
        AddPawnRelation(B3, B7, -13, -19);
        AddPawnRelation(C3, C7, -13, -19);
        AddPawnRelation(D3, D7, -13, -19);
        AddPawnRelation(E3, E7, -13, -19);
        AddPawnRelation(F3, F7, -13, -19);
        AddPawnRelation(G3, G7, -13, -19);
        AddPawnRelation(H3, H7, -13, -19);

        AddPawnRelation(A4, A5, -13, -19);
        AddPawnRelation(B4, B5, -13, -19);
        AddPawnRelation(C4, C5, -13, -19);
        AddPawnRelation(D4, D5, -13, -19);
        AddPawnRelation(E4, E5, -13, -19);
        AddPawnRelation(F4, F5, -13, -19);
        AddPawnRelation(G4, G5, -13, -19);
        AddPawnRelation(H4, H5, -13, -19);

        AddPawnRelation(A4, A6, -13, -19);
        AddPawnRelation(B4, B6, -13, -19);
        AddPawnRelation(C4, C6, -13, -19);
        AddPawnRelation(D4, D6, -13, -19);
        AddPawnRelation(E4, E6, -13, -19);
        AddPawnRelation(F4, F6, -13, -19);
        AddPawnRelation(G4, G6, -13, -19);
        AddPawnRelation(H4, H6, -13, -19);

        AddPawnRelation(A4, A7, -13, -19);
        AddPawnRelation(B4, B7, -13, -19);
        AddPawnRelation(C4, C7, -13, -19);
        AddPawnRelation(D4, D7, -13, -19);
        AddPawnRelation(E4, E7, -13, -19);
        AddPawnRelation(F4, F7, -13, -19);
        AddPawnRelation(G4, G7, -13, -19);
        AddPawnRelation(H4, H7, -13, -19);

        AddPawnRelation(A5, A6, -13, -19);
        AddPawnRelation(B5, B6, -13, -19);
        AddPawnRelation(C5, C6, -13, -19);
        AddPawnRelation(D5, D6, -13, -19);
        AddPawnRelation(E5, E6, -13, -19);
        AddPawnRelation(F5, F6, -13, -19);
        AddPawnRelation(G5, G6, -13, -19);
        AddPawnRelation(H5, H6, -13, -19);

        AddPawnRelation(A5, A7, -13, -19);
        AddPawnRelation(B5, B7, -13, -19);
        AddPawnRelation(C5, C7, -13, -19);
        AddPawnRelation(D5, D7, -13, -19);
        AddPawnRelation(E5, E7, -13, -19);
        AddPawnRelation(F5, F7, -13, -19);
        AddPawnRelation(G5, G7, -13, -19);
        AddPawnRelation(H5, H7, -13, -19);

        AddPawnRelation(A6, A7, -13, -19);
        AddPawnRelation(B6, B7, -13, -19);
        AddPawnRelation(C6, C7, -13, -19);
        AddPawnRelation(D6, D7, -13, -19);
        AddPawnRelation(E6, E7, -13, -19);
        AddPawnRelation(F6, F7, -13, -19);
        AddPawnRelation(G6, G7, -13, -19);
        AddPawnRelation(H6, H7, -13, -19);

        AddPawnRelation(A2, B2, -1, -6); // fm
        AddPawnRelation(B2, C2,  0, -6); // fm
        AddPawnRelation(C2, D2, -6, -6); // fm
        AddPawnRelation(D2, E2, 15, -6); // fm
        AddPawnRelation(E2, F2,  3, -6); // fm
        AddPawnRelation(F2, G2,  0, -6); // fm
        AddPawnRelation(G2, H2,  3, -6); // fm

        AddPawnRelation(A3, B3,-12, -4);
        AddPawnRelation(B3, C3, -1, -4); // fm
        AddPawnRelation(C3, D3, 14, -4); // fm
        AddPawnRelation(D3, E3, 14, -4); // fm
        AddPawnRelation(E3, F3,  4, -4); // fm
        AddPawnRelation(F3, G3,  7, -4);
        AddPawnRelation(G3, H3,-18, -4); // fm

        AddPawnRelation(A4, B4,  5, 5);
        AddPawnRelation(B4, C4, 10, 5);
        AddPawnRelation(C4, D4, 20, 5);
        AddPawnRelation(D4, E4, 25, 5);  // fm
        AddPawnRelation(E4, F4, 13, 5);
        AddPawnRelation(F4, G4, 10, 5);
        AddPawnRelation(G4, H4,  5, 5);

        AddPawnRelation(A5, B5,  7, 15);
        AddPawnRelation(B5, C5, 12, 15);
        AddPawnRelation(C5, D5, 12, 15);
        AddPawnRelation(D5, E5, 16, 15);
        AddPawnRelation(E5, F5, 17, 15);
        AddPawnRelation(F5, G5, 20, 15);
        AddPawnRelation(G5, H5,  7, 15);

        AddPawnRelation(A6, B6, 15, 25);
        AddPawnRelation(B6, C6, 15, 25);
        AddPawnRelation(C6, D6, 15, 25);
        AddPawnRelation(D6, E6, 15, 25);
        AddPawnRelation(E6, F6, 15, 25);
        AddPawnRelation(F6, G6, 15, 25);
        AddPawnRelation(G6, H6, 15, 25);

        AddPawnRelation(A7, B7, 25, 45);
        AddPawnRelation(B7, C7, 25, 45);
        AddPawnRelation(C7, D7, 25, 45);
        AddPawnRelation(D7, E7, 25, 45);
        AddPawnRelation(E7, F7, 25, 45);
        AddPawnRelation(F7, G7, 25, 45);
        AddPawnRelation(G7, H7, 25, 45);

        AddPawnRelation(B2, A3, 4, 2);  // fm

        AddPawnRelation(A2, B3, 9,  2);
        AddPawnRelation(C2, B3, 4,  2);
        AddPawnRelation(A2, C2, 2,  0);

        AddPawnRelation(B2, C3, 10, 2); // fm
        AddPawnRelation(D2, C3, 2, 2);  // fm
        AddPawnRelation(B2, D2,-4, 0);  // fm

        AddPawnRelation(C2, D3, 3, 2);
        AddPawnRelation(E2, D3, 3, 2);
        AddPawnRelation(C2, E2,-2, 0); // fm

        AddPawnRelation(D2, E3,  6, 2);
        AddPawnRelation(F2, E3, 10, 2); // fm
        AddPawnRelation(F2, D2,  0, 0); // fm

        AddPawnRelation(E2, F3, 1, 2);
        AddPawnRelation(G2, F3, 4, 2);
        AddPawnRelation(E2, G2, -2, 0);

        AddPawnRelation(F2, G3, 8, 2); // fm
        AddPawnRelation(H2, G3, 5, 2); // fm
        AddPawnRelation(F2, H2, -3, 0);// fm

        AddPawnRelation(G2, H3, 6, 2);

        AddPawnRelation(B3, A4, 0, 2); // fm

        AddPawnRelation(A3, B4, 12, 2);
        AddPawnRelation(C3, B4, 4, 2);
        AddPawnRelation(A3, C3, -2, 0); // fm

        AddPawnRelation(B3, C4, 6, 2);
        AddPawnRelation(D3, C4, 4, 2);
        AddPawnRelation(B3, D3, -5, 0);

        AddPawnRelation(C3, D4, 13, 2); // fm
        AddPawnRelation(E3, D4, 8, 2);  // fm
        AddPawnRelation(C3, E3, -14, 0);// fm

        AddPawnRelation(D3, E4, 11, 2); // fm
        AddPawnRelation(F3, E4, 15, 2);
        AddPawnRelation(F3, D3, -10, 0); //fm

        AddPawnRelation(E3, F4, 5, 2);
        AddPawnRelation(G3, F4, 7, 2);
        AddPawnRelation(E3, G3, -13, 0); // fm

        AddPawnRelation(F3, G4, 4, 2);
        AddPawnRelation(H3, G4, 12, 2);
        AddPawnRelation(F3, H3, -5, 0); //fm

        AddPawnRelation(G3, H4, 1, 2);  //fm

        AddPawnRelation(B4, A5, 1, 1);

        AddPawnRelation(A4, B5, 4, 2);
        AddPawnRelation(C4, B5, 3, 2);
        AddPawnRelation(A4, C4, -4, 0);

        AddPawnRelation(B4, C5, 5, 2);
        AddPawnRelation(D4, C5, 1, 2);
        AddPawnRelation(B4, D4, -2, 0);

        AddPawnRelation(C4, D5, 9, 2);
        AddPawnRelation(E4, D5, 9, 2);
        AddPawnRelation(C4, E4, 3, 0); // fm

        AddPawnRelation(D4, E5,12, 2); // fm
        AddPawnRelation(F4, E5,14, 2);
        AddPawnRelation(F4, D4, 5, 0);

        AddPawnRelation(E4, F5, 4, 2);
        AddPawnRelation(G4, F5, 2, 2);
        AddPawnRelation(E4, G4, -2, 0); // fm

        AddPawnRelation(F4, G5, 2, 2);
        AddPawnRelation(H4, G5, 3, 2);
        AddPawnRelation(F4, H4, -6, 0);

        AddPawnRelation(G4, H5, 0, 1);

        AddPawnRelation(B5, A6, 1, 1);

        AddPawnRelation(A5, B6, 2, 2);
        AddPawnRelation(C5, B6, 2, 2);
        AddPawnRelation(A5, C5, -2, 0); // fm

        AddPawnRelation(B5, C6, 2, 2);
        AddPawnRelation(D5, C6, 2, 2);
        AddPawnRelation(B5, D5, -2, 0); //fm

        AddPawnRelation(C5, D6, 2, 2);
        AddPawnRelation(E5, D6, 2, 2);
        AddPawnRelation(C5, E5, -1, 0);

        AddPawnRelation(D5, E6, 2, 2);
        AddPawnRelation(F5, E6, 2, 2);
        AddPawnRelation(F5, D5, -1, 0);

        AddPawnRelation(E5, F6, 2, 2);
        AddPawnRelation(G5, F6, 2, 2);
        AddPawnRelation(E5, G5, -1, 0);

        AddPawnRelation(F5, G6, 2, 2);
        AddPawnRelation(H5, G6, 2, 2);
        AddPawnRelation(F5, H5, -1, 0);

        AddPawnRelation(G5, H6, 1, 1);

        AddPawnRelation(B6, A7, 0, -5);

        AddPawnRelation(A6, B7, 1, 3);
        AddPawnRelation(C6, B7, 1, 3);
        AddPawnRelation(A6, C6, 0, 0);

        AddPawnRelation(B6, C7, 1, 2);
        AddPawnRelation(D6, C7, 1, 2);
        AddPawnRelation(B6, D6, 0, 0);

        AddPawnRelation(C6, D7, 1, 3);
        AddPawnRelation(E6, D7, 1, 2);
        AddPawnRelation(C6, E6, 0, 0);

        AddPawnRelation(D6, E7, 1, 2);
        AddPawnRelation(F6, E7, 1, 2);
        AddPawnRelation(F6, D6, 0, 0);

        AddPawnRelation(E6, F7, 1, 2);
        AddPawnRelation(G6, F7, 1, 2);
        AddPawnRelation(E6, G6, 0, 0);

        AddPawnRelation(F6, G7, 1, 2);
        AddPawnRelation(H6, G7, 1, 2);
        AddPawnRelation(F6, H6, 0, 0);

        AddPawnRelation(G6, H7,-4, -6);
        
        AddPawnRelation(A2, C4, -1, 0);
        AddPawnRelation(A3, C4,  1, 0);
        AddPawnRelation(C2, D4, -4, 0);
        AddPawnRelation(F3, D5,  3, 0);
        AddPawnRelation(C3, E5,  2, 0);
        AddPawnRelation(D3, G3,  2, 0);
        AddPawnRelation(E5, H4,  2, 0);
        AddPawnRelation(E5, H5,  6, 0);
    }

    /**
    printf("--------------------------------------------\n");
    for (int sq = 0; sq < 64; sq++) {
        int inv = sq ^ (Black * 56);
        int val = (8 * egOne[White][King][sq] + 2 * egCla[White][King][sq]) / 10;
        printf("%3d, ", val);
        if ((sq + 1) % 8 == 0) printf("\n");
    }
    /**/
}

void cPst::AddPawnRelation(int s1, int s2, int mgVal, int egVal) 
{
    pawnRelationshipMg[White][RelSq(s1, White)][RelSq(s2, White)] += mgVal;
    pawnRelationshipMg[Black][RelSq(s1, Black)][RelSq(s2, Black)] += mgVal;
    pawnRelationshipMg[White][RelSq(s2, White)][RelSq(s1, White)] += mgVal;
    pawnRelationshipMg[Black][RelSq(s2, Black)][RelSq(s1, Black)] += mgVal;
    pawnRelationshipEg[White][RelSq(s1, White)][RelSq(s2, White)] += egVal;
    pawnRelationshipEg[Black][RelSq(s1, Black)][RelSq(s2, Black)] += egVal;
    pawnRelationshipEg[White][RelSq(s2, White)][RelSq(s1, White)] += egVal;
    pawnRelationshipEg[Black][RelSq(s2, Black)][RelSq(s1, Black)] += egVal;
}
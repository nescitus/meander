#include <assert.h>
#include <stdio.h>
#include <math.h>
#include "meander.h"
#include "eval.h"

// TODO: 
// - bishop that can't go backwards is penalised
// - knight shielded by defended pawn
// - bishop shielded by opponent's defending pawn
// - 7th line passer blocked by a major piece
// - knight blocking c pawn
// - more extensive pawn mobility eval
// - bonus for pawns that can attack pieces
// - outpost unattackable by enemy minors
// - outpost eval taking into account distance to enemy king
// - rook outpost (defended by pawn only)
// - penalize king on pawnless wing
// - bigger shield value on actual king's file
// - attacked and undefended squares around the king
// - pawns' participation in king attack
// - knight pair
// - rook pair
// 
// - eval grain, equal to 2 or 4 FAIL
// - trapped knight FAIL


static const int max_phase = 24;
const int phase_value[7] = { 0, 1, 1, 2, 4, 0, 0 };

static const Bitboard bbQSCastle[2] = { Paint(A1,B1,C1) | Paint(A2,B2,C2),
                                        Paint(A8,B8,C8) | Paint(A7,B7,C7)
};
static const Bitboard bbKSCastle[2] = { Paint(F1,G1,H1) | Paint(F2,G2,H2),
                                        Paint(F8,G8,H8) | Paint(F7,G7,H7)
};

static const Bitboard bbCentralFile = FILE_C_BB | FILE_D_BB | FILE_E_BB | FILE_F_BB;

const int kingRoot[64] = {
    B2, B2, C2, D2, E2, F2, G2, G2,
    B2, B2, C2, D2, E2, F2, G2, G2,
    B3, B3, C3, D3, E3, F3, G3, G3,
    B4, B4, C4, D4, E4, F4, G4, G4,
    B5, B5, C5, D5, E5, F5, G5, G5,
    B6, B6, C6, D6, E6, F6, G6, G6,
    B7, B7, C7, D7, E7, F7, G7, G7,
    B7, B7, C7, D7, E7, F7, G7, G7
};

char* factor_name[] = { "Material  ", "Pst       ",  "Pawns     ", "Passers   ", "Attack    ", "Mobility  ", "Pressure  ", "Tropism   ", "Outposts  ", "Lines     ", "Shield    ", "Others    " };

int Engine::Evaluate(Position *p, EvalData *e, int use_hash) 
{

    // Try to retrieve score from eval hashtable

    int addr = p->hash_key % EVAL_HASH_SIZE;

#ifndef USE_TUNING
    if (EvalTT[addr].key == p->hash_key && use_hash) {
        int hashScore = EvalTT[addr].score;
        return p->side == White ? hashScore : -hashScore;
    }
#endif

    // Clear eval

    int score = 0;
    int mg_score = 0;
    int eg_score = 0;

    for (int sd = 0; sd < 2; sd++) {
        for (int fc = 0; fc < N_OF_FACTORS; fc++) {
            e->mg[sd][fc] = 0;
            e->eg[sd][fc] = 0;
        }
    }

    // Detect pawn structure

    e->isKID[White] = false;
    e->isKID[Black] = false;
    if (p->PawnComplex(White, E4, D5) && p->PawnComplex(Black, D6, E5)) e->isKID[Black] = true;
    if (p->PawnComplex(Black, E5, D4) && p->PawnComplex(White, D3, E4)) e->isKID[White] = true; 

    // Calculate variables used during evaluation

    e->control[White][Pawn] = GetWPControl(p->Map(White, Pawn));
    e->control[Black][Pawn] = GetBPControl(p->Map(Black, Pawn));
    e->control[White][Knight] = e->control[Black][Knight] = 0;
    e->control[White][Bishop] = e->control[Black][Bishop] = 0;
    e->control[White][Rook] = e->control[Black][Rook] = 0;
    e->control[White][Queen] = e->control[Black][Queen] = 0;
    e->bbPawnCanTake[White] = FillNorth(e->control[White][Pawn]);
    e->bbPawnCanTake[Black] = FillSouth(e->control[Black][Pawn]);
    e->dbl_control[White] = GetDoubleWPControl(p->Map(White, Pawn));
    e->dbl_control[Black] = GetDoubleBPControl(p->Map(Black, Pawn));

    // Tempo bonus

    e->mg[p->side][F_OTHERS] += 10;
    e->eg[p->side][F_OTHERS] += 5;

    // Bishop pair

    if (PopCnt(p->Map(White, Bishop)) > 1) Add(e, White, F_MAT, bPairMg, bPairEg);
    if (PopCnt(p->Map(Black, Bishop)) > 1) Add(e, Black, F_MAT, bPairMg, bPairEg);

    // Evaluate pieces and pawns

    EvaluatePieces(p, e, White);
    EvaluatePieces(p, e, Black);
    PawnKingEval(p, e);
    EvaluatePressure(p, e, White);
    EvaluatePressure(p, e, Black);
    EvaluatePassers(p, e, White);
    EvaluatePassers(p, e, Black);
    EvalKingAttacks(p, e, White);
    EvalKingAttacks(p, e, Black);
    EvalKing(p, e, White);
    EvalKing(p, e, Black);

    // Bishop at home

    EvalBishopAtHome(p, e, White, F1, E2, E3, Paint(G1, H1, H2));
    EvalBishopAtHome(p, e, White, C1, D2, D3, Paint(B1, A1, A2));
    EvalBishopAtHome(p, e, Black, F8, E7, E6, Paint(G8, H8, H7));
    EvalBishopAtHome(p, e, Black, C8, D7, D6, Paint(B8, A8, A7));

    // Bishop pins

    EvalPin(p, e, White, D8, E7, F6, G5, H4);
    EvalPin(p, e, White, E8, D7, C6, B5, A4);
    EvalPin(p, e, Black, D1, E2, F3, G4, H5);
    EvalPin(p, e, Black, E1, D2, C3, B4, A5);

    // Compromised fianchetto

    if (p->IsOnSq(White, Bishop, G2)
    && p->IsOnSq(Black, Pawn, E4)
    && Paint(E4) && e->control[Black][Pawn])
        Add(e, White, F_OTHERS, blockedFianchettoMg, blockedFianchettoEg);

    if (p->IsOnSq(White, Bishop, B2)
    && p->IsOnSq(Black, Pawn, D4)
    && Paint(D4) && e->control[Black][Pawn])
        Add(e, White, F_OTHERS, blockedFianchettoMg, blockedFianchettoEg);

    if (p->IsOnSq(Black, Bishop, G7)
    && p->IsOnSq(White, Pawn, E5)
    && Paint(E5) && e->control[White][Pawn])
        Add(e, Black, F_OTHERS, blockedFianchettoMg, blockedFianchettoEg);

    if (p->IsOnSq(Black, Bishop, B7)
    && p->IsOnSq(White, Pawn, D5)
    && Paint(D5) && e->control[White][Pawn])
        Add(e, Black, F_OTHERS, blockedFianchettoMg, blockedFianchettoEg);

    // Trapped bishop

    EvalTrappedBishop(p, e, White, H7, G6, bTrappedA2);
    EvalTrappedBishop(p, e, White, G8, F7, bTrappedA2);
    EvalTrappedBishop(p, e, White, A7, B6, bTrappedA2);
    EvalTrappedBishop(p, e, White, B8, C7, bTrappedA2);
    EvalTrappedBishop(p, e, White, A6, B5, bTrappedA3);
    EvalTrappedBishop(p, e, White, H6, G5, bTrappedA3);

    EvalTrappedBishop(p, e, Black, H2, G3, bTrappedA2);
    EvalTrappedBishop(p, e, Black, G1, F2, bTrappedA2);
    EvalTrappedBishop(p, e, Black, A2, B3, bTrappedA2);
    EvalTrappedBishop(p, e, Black, B1, C2, bTrappedA2);
    EvalTrappedBishop(p, e, Black, A3, B4, bTrappedA3);
    EvalTrappedBishop(p, e, Black, H3, G4, bTrappedA3);

    // Unstoppable passers

    EvalUnstoppablePassers(p, e);

    // Set phase

    int mg_phase = Min(max_phase, p->phase);
    int eg_phase = max_phase - mg_phase;

    // Sum all the eval factors

    for (int factor = 0; factor < N_OF_FACTORS; factor++) {
        mg_score += (e->mg[White][factor] - e->mg[Black][factor]) * weights[White][factor] / 100;
        eg_score += (e->eg[White][factor] - e->eg[Black][factor]) * weights[Black][factor] / 100;
    }

    // Merge mg/eg scores    

    score += (((mg_score * mg_phase) + (eg_score * eg_phase)) / max_phase);

    // Material imbalances
    // TODO: mg/eg split?

    int majorDelta = p->MajorCnt(White) - p->MajorCnt(Black) + p->cnt[White][Queen] - p->cnt[Black][Queen];
    int minorDelta = p->MinorCnt(White) - p->MinorCnt(Black);

    // Malus for being an exchange down

    if (majorDelta == -1 && minorDelta == 1)
        score -= exchange;
    if (majorDelta == 1 && minorDelta == -1)
        score += exchange;

    // Bonus for two minors vs rook // twoo minors and rook vs queen

    if (majorDelta == -1 && minorDelta == 2)
        score += minors2;
    if (majorDelta == 1 && minorDelta == -2)
        score -= minors2;

    // Bonus for minor piece (presumably) vs pawns

    if (majorDelta == 0 && minorDelta == 1)
        score += minorUp;
    if (majorDelta == 0 && minorDelta == -1)
        score -= minorUp;

    // Bonus for 3 pawns advantage

    if (majorDelta == 0 && minorDelta == 0) {
        if (p->cnt[White][Pawn] == p->cnt[Black][Pawn] + 2)
            score += pawns2;
        if (p->cnt[Black][Pawn] == p->cnt[White][Pawn] + 2)
            score -= pawns2;
    }

    // Material advantage in pawn endgame

    if (p->MajorCnt(White) + p->MajorCnt(Black) + p->MinorCnt(White) + p->MinorCnt(Black) == 0) {
        if (p->cnt[White][Pawn] > p->cnt[Black][Pawn]) score += (45);
        if (p->cnt[White][Pawn] < p->cnt[Black][Pawn]) score -= (45);
    }

    // Blurring evaluation for lowel levels

    if (engineLevel < numberOfLevels) {
        int blur = blurStepPerLevel * (1 + numberOfLevels - engineLevel);
        int rand_mod = (blur / 2) - ((p->hash_key) % blur);
        score += rand_mod;
    }

    score += CheckmateHelper(p);

    // Scale down drawish endgames

    int draw_factor = 64;
    if (score > 0) draw_factor = GetDrawFactor(p, White);
    else           draw_factor = GetDrawFactor(p, Black);
    score *= draw_factor;
    score /= 64;

    // Make sure eval doesn't exceed mate score

    if (score < -MAX_EVAL)
        score = -MAX_EVAL;
    else if (score > MAX_EVAL)
        score = MAX_EVAL;

    // Save eval score in the evaluation hash table

#ifndef USE_TUNING
    EvalTT[addr].key = p->hash_key;
    EvalTT[addr].score = score;
#endif
    // Return score relative to the side to move

    return p->side == White ? score : -score;
}

void Engine::ClearEvalHash(void) {

    for (int e = 0; e < EVAL_HASH_SIZE; e++) {
        EvalTT[e].key = 0;
        EvalTT[e].score = 0;
    }
}

void InitOptions(void) 
{
    for (int i = 0; i < N_OF_OPTIONS; i++) {
        options[i] = 100;
    }

    options[O_MATERIAL] = 100;
    options[O_OWN_ATT] = 100;
    options[O_OPP_ATT] = 100;
    options[O_OWN_MOB] = 100;
    options[O_OPP_MOB] = 100;
    options[O_OWN_TROP] = 21;
    options[O_OPP_TROP] = 21;
    options[O_OWN_PRES] = 100;
    options[O_OPP_PRES] = 100;
    options[O_OWN_PAWN] = 100;
    options[O_OPP_PAWN] = 100;
}

void InitWeights(void) {

    for (int fc = 0; fc < N_OF_FACTORS; fc++) 
    {
        weights[White][fc] = 100;
        weights[Black][fc] = 100;
    }

    int oppoSide = progSide ^ 1;

    weights[White][F_MAT] = options[O_MATERIAL];
    weights[Black][F_MAT] = options[O_MATERIAL];

    weights[progSide][F_ATT] = options[O_OWN_ATT];
    weights[oppoSide][F_ATT] = options[O_OPP_ATT];

    weights[progSide][F_MOB] = options[O_OWN_MOB];
    weights[oppoSide][F_MOB] = options[O_OPP_MOB];
  
    weights[progSide][F_PRES] = options[O_OWN_PRES];
    weights[oppoSide][F_PRES] = options[O_OPP_PRES];


    weights[progSide][F_PAWNS] = options[O_OWN_PAWN];
    weights[oppoSide][F_PAWNS] = options[O_OPP_PAWN];

    weights[progSide][F_TROP] = options[O_OWN_TROP];
    weights[oppoSide][F_TROP] = options[O_OPP_TROP];

    weights[progSide][F_OUTPOST] = 100;
    weights[oppoSide][F_OUTPOST] = 100;
}

void EvaluatePieces(Position* p, EvalData* e, int sd) {

    Bitboard bbPieces, bbMob, bbSafe, bbAtt, bbFile, bbFwd, bbSq;
    int op, sq, cnt, tmp, ksq;
    int ownPawnCnt = p->cnt[sd][Pawn];

    // Init variables

    op = Opp(sd);
    ksq = KingSq(p, op);
    Add(e, op, F_PST, Pst.mgOne[op][King][ksq], Pst.egOne[op][King][ksq]);

    e->control[op][King] = Att.King(ksq);
    e->att[sd] = 0;

    // 2022-07-05: not counting checks from squares occupied by own pieces fails
    // (what about pawns?)

    Bitboard nCheck = Att.Knight(ksq);
    Bitboard bCheck = Att.Bish(p->Filled(), ksq);
    Bitboard rCheck = Att.Rook(p->Filled(), ksq);
    Bitboard qCheck = bCheck | rCheck;
    Bitboard futureOutposts = Mask.outpost[sd] & ~e->control[op][Pawn];

    // Init enemy king zone for attack evaluation.

    Bitboard bbZone = Att.King(kingRoot[ksq]);

    // Knight

    bbPieces = p->Map(sd, Knight);
    while (bbPieces) {
        sq = PopFirstBit(&bbPieces);
        bbSq = Paint(sq);
        bbFwd = ShiftFwd(bbSq, sd);

        // Knight attacked by enemy pawn

        if (bbSq & e->control[op][Pawn]) 
            Add(e, sd, F_PRES, -7, -2);

        Add(e, sd, F_MAT, mg_value[Knight], eg_value[Knight]);
        if (p->Map(sd, King) & Mask.ksCastle[sd])
            Add(e, sd, F_PST, Pst.mgKs[sd][Knight][sq], Pst.egOne[sd][Knight][sq]);
        else
            Add(e, sd, F_PST, Pst.mgOne[sd][Knight][sq], Pst.egOne[sd][Knight][sq]);

        AddMg(e, sd, F_TROP, Dist.nTropismMg[sq][ksq]);

        // Knight loses value as pawns get exchanged

        Add(e, sd, F_OTHERS, 4 * (ownPawnCnt - 4), 4 * (ownPawnCnt - 4));

        // Knight shielded by own pawn

        if (bbFwd & p->Map(sd, Pawn))
        {
            Add(e, sd, F_OTHERS, Pst.mgShieldedN[sd][sq], 2);
        }

        // Knight shielded by opponents pawn

        if (bbFwd & p->Map(op, Pawn))
        {
            Add(e, sd, F_OTHERS, 10, 7);
        }

        // Knight mobility 
        //(excluding squares controlled by enemy pawns)

        bbMob = Att.Knight(sq) & ~p->cl_bb[sd];
        bbSafe = bbMob & ~e->control[op][Pawn];
        cnt = PopCnt(bbSafe);
        Add(e, sd, F_MOB, nMobMg[cnt], nMobEg[cnt]);

        // Update board control

        e->control[sd][Knight] |= Att.Knight(sq);

        // Knight threatens enemy bishop

        if (bbMob & p->Map(op, Bishop))
        {
            Add(e, sd, F_PRES, NattacksBMg, NattacksBEg);
        }

        // Knight check threat

        e->att[sd] += knightCheck * PopCnt(bbSafe & nCheck);

        // Knight attacks on enemy king zone

        bbAtt = Att.Knight(sq);
        if (bbAtt & bbZone)
            e->att[sd] += knightAttack * PopCnt(bbAtt & bbZone);

        // Knight outpost

        tmp = pstKnightOutpost[RelSq(sq, sd)];
        if (tmp) {
            int mul = 0;
            if (bbSq & ~e->bbPawnCanTake[op])
                mul += 5;
            if (bbSq & e->control[sd][Pawn])
                mul += 2;
            if (bbSq & e->dbl_control[sd])
                mul += 1;

            tmp *= mul;
            tmp /= 2;
            Add(e, sd, F_OUTPOST, tmp, tmp);
        }

        // Knight potential outpost

        if (bbSafe & futureOutposts) 
        {
            Add(e, sd, F_OUTPOST, 8, 2);
        }
    } // end of knight eval

    // Bishop

    bbPieces = p->Map(sd, Bishop);
    while (bbPieces) {
        sq = PopFirstBit(&bbPieces);
        bbSq = Paint(sq);
        bbFwd = ShiftFwd(bbSq, sd);

        // Bishop attacked by enemy pawn

        if (bbSq & e->control[op][Pawn]) 
            Add(e, sd, F_PRES, -8, -6);

        Add(e, sd, F_MAT, mg_value[Bishop], eg_value[Bishop]);
        Add(e, sd, F_PST, Pst.mgOne[sd][Bishop][sq], Pst.egOne[sd][Bishop][sq]);
        AddMg(e, sd, F_TROP, Dist.bTropismMg[sq][ksq]);

        // Bishop shielded by own pawn

        if (bbFwd & p->Map(sd, Pawn)) 
        {     
            Add(e, sd, F_OTHERS, shieldBishBaseMg, shieldBishBaseEg);

            // shielding pawn is defended
            if (bbFwd & e->control[sd][Pawn])
                Add(e, sd, F_OTHERS, Pst.mgShieldedB[sd][sq], 7);
        }

        // Bishop shielded by opponents pawn
        
        if (bbFwd & p->Map(op, Pawn)) 
        {
            Add(e, sd, F_OTHERS, shieldBishOppoMg, shieldBishOppoEg);
            if (SidesOf(bbSq) & p->Map(op, Pawn))
                Add(e, sd, F_OTHERS, 5, 8);
        }

        // Bishop mobility

        bbMob = Att.Bish(p->Filled(), sq);
        e->control[sd][Bishop] |= bbMob;
        bbSafe = bbMob & ~e->control[op][Pawn];
        cnt = PopCnt(bbSafe);
        Add(e, sd, F_MOB, bMobMg[cnt], bMobEg[cnt]);

        // Bishop attacks knight

        if (bbMob & p->Map(op, Knight))
        {
            Add(e, sd, F_PRES, BattacksNMg, BattacksNEg);
        }

        // Bishop check threats

        e->att[sd] += bishCheck * PopCnt(bbSafe & bCheck);

        // Bishop cannot reach enemy half of the board

        if ((bbSafe & Mask.away[sd]) == 0)
            Add(e, sd, F_MOB, bishRestrictedMg, bishRestrictedEg);

        // Bishop attacks on enemy king zone

        if (bbMob & p->Map(sd, Queen))
            bbAtt = Att.Bish(p->Filled() ^ p->Map(sd, Queen), sq);
        else
            bbAtt = bbMob;

        bbAtt &= bbZone;

        if (bbAtt) {
            e->att[sd] += safeBishAttack * PopCnt(bbAtt & ~e->control[op][Pawn]);
            e->att[sd] += unsafeBishAttack * PopCnt(bbAtt & e->control[op][Pawn]);
        }

        // Bishop outpost

        tmp = pstBishopOutpost[RelSq(sq, sd)];

        if (tmp) {
            int mul = 0;
            if (bbSq & ~e->bbPawnCanTake[op])
                mul += 5;
            if (bbSq & e->control[sd][Pawn])
                mul += 2;
            if (bbSq & e->dbl_control[sd])
                mul += 1;
            tmp *= mul;
            tmp /= 3;
            Add(e, sd, F_OUTPOST, tmp, tmp);
        }

        // Bishop potential outpost

        if (bbSafe & futureOutposts) 
        {
            Add(e, sd, F_OUTPOST, bishPotentialMg, bishPotentialEg);
        }

        // Pawns on bishop color

        if (bbSq & Mask.sqColor[White]) 
        {
            int tmp = pawnOnBColor * (PopCnt(p->Map(sd, Pawn) & Mask.sqColor[White]) - 4);
            tmp += PopCnt(p->Map(op, Pawn) & Mask.sqColor[White]) - 4;
            Add(e, sd, F_OTHERS, -tmp, -tmp);
        }
        else 
        {
            int tmp = pawnOnBColor * (PopCnt(p->Map(sd, Pawn) & Mask.sqColor[Black]) - 4);
            tmp += PopCnt(p->Map(op, Pawn) & Mask.sqColor[Black]) - 4;
            Add(e, sd, F_OTHERS, -tmp, -tmp);
        }
    } // end of bishop eval

    // Rook

    bbPieces = p->Map(sd, Rook);
    while (bbPieces) {
        sq = PopFirstBit(&bbPieces);
        Add(e, sd, F_MAT, mg_value[Rook], eg_value[Rook]);
        Add(e, sd, F_PST, Pst.mgOne[sd][Rook][sq], Pst.egOne[sd][Rook][sq]);
        AddMg(e, sd, F_TROP, Dist.rTropismMg[sq][ksq]);

        // Rook mobility

        bbMob = Att.Rook(p->Filled(), sq);
        e->control[sd][Rook] |= bbMob;
        bbSafe = bbMob & ~e->control[op][Pawn];
        cnt = PopCnt(bbMob);
        Add(e, sd, F_MOB, rMobMg[cnt], rMobEg[cnt]);

        if (bbMob & (p->Map(op, Knight) | p->Map(op, Bishop)))
            Add(e, sd, F_OTHERS, RattacksNMg, RattacksNEg);

        // Rook check threats

        e->att[sd] += rookCheck * PopCnt(bbSafe & rCheck);
        
        // Connected rooks

        if (bbMob & p->Map(sd, Rook)) 
        {
            Add(e, sd, F_LINES, Pst.rConMg[sd][sq], Pst.rConEg[sd][sq]);
        }

        // Rook attacks on enemy king zone

        bbAtt = Att.Rook(p->Filled() ^ p->Map(sd, Queen) ^ p->Map(sd, Rook), sq);
        bbAtt &= bbZone;
        if (bbAtt) 
        {
            e->att[sd] += safeRookAttack * PopCnt(bbAtt & ~e->control[op][Pawn]);
            e->att[sd] += unsafeRookAttack * PopCnt(bbAtt & e->control[op][Pawn]);
        }

        // Rook's file

        bbFile = FillNorth(Paint(sq)) | FillSouth(Paint(sq));

        //if (bbFile & p->Map(op, Queen))
        //    Add(e, sd, F_LINES, 6, 12); // NEUTRAL

        if (!(bbFile & p->Map(sd, Pawn))) 
        {
            if (!(bbFile & p->Map(op, Pawn))) 
            {
                Add(e, sd, F_LINES, rookOpenMg, rookOpenEg); // open file
                if (bbFile & bbZone)
                    AddMg(e, sd, F_OTHERS, 6);
            }
            else 
            {
                if (bbFile & (p->Map(op, Pawn) & e->control[op][Pawn])) 
                {
                    Add(e, sd, F_LINES, rookBadHalfMg, rookBadHalfEg); // "bad" half-open file
                }
                else 
                {
                    Add(e, sd, F_LINES, rookHalfMg, rookHalfEg); // "good" half-open file
                    if (bbFile & bbZone)
                        AddMg(e, sd, F_OTHERS, 3);
                }
            }
        }
        else 
        {
            Add(e, sd, F_LINES, rookClosedMg, rookClosedMg); // closed file
        }

        // Rook on 7th rank attacking pawns or cutting off enemy king

        if (Paint(sq) & bbRelRank[sd][rank7]) {
            if (p->Map(op, Pawn) & bbRelRank[sd][rank7]
            || p->Map(op, King) & bbRelRank[sd][rank8]) 
            {
                Add(e, sd, F_LINES, rookSeventhMg, rookSeventhEg);
            }
        }
    }

    // Queen

    bbPieces = p->Map(sd, Queen);
    while (bbPieces) {
        sq = PopFirstBit(&bbPieces);
        bbSq = Paint(sq);
        Add(e, sd, F_MAT, mg_value[Queen], eg_value[Queen]);
        Add(e, sd, F_PST, Pst.mgOne[sd][Queen][sq], Pst.egOne[sd][Queen][sq]);
        AddMg(e, sd, F_TROP, Dist.qTropismMg[sq][ksq]);

        // Premature queen developement

        if (bbSq & ~(Mask.rr[sd][rank1] | Mask.rr[sd][rank2])) {
            tmp = 0;
            if (p->IsOnSq(sd, Knight, RelSq(sd, B1))) tmp -= 3;
            if (p->IsOnSq(sd, Knight, RelSq(sd, G1))) tmp -= 3;
            if (p->IsOnSq(sd, Bishop, RelSq(sd, C1))) tmp -= 3;
            if (p->IsOnSq(sd, Bishop, RelSq(sd, F1))) tmp -= 3;
            if (p->IsOnSq(sd, Pawn, RelSq(sd, E2))) tmp -= 4;
            if (p->IsOnSq(sd, Pawn, RelSq(sd, D2))) tmp -= 4;
            AddMg(e, sd, F_OTHERS, tmp);
        }

        // Queen mobility

        bbMob = Att.Queen(p->Filled(), sq);
        e->control[sd][Queen] |= bbMob;
        bbSafe = bbMob & ~e->control[op][Pawn];
        e->att[sd] += queenCheck * PopCnt(bbSafe & qCheck);
        cnt = PopCnt(bbMob);
        Add(e, sd, F_MOB, qMobMg[cnt], qMobEg[cnt]);

        // Queen attacks on enemy king zone

        bbAtt = Att.Bish(p->Filled() ^ p->Map(sd, Bishop) ^ p->Map(sd, Queen), sq);
        bbAtt |= Att.Rook(p->Filled() ^ p->Map(sd, Rook) ^ p->Map(sd, Queen), sq);
        bbAtt &= bbZone;
        if (bbAtt) 
        {
            e->att[sd] += safeQueenAttack * PopCnt(bbAtt & ~e->control[op][Pawn]);
            e->att[sd] += unsafeQueenAttack * PopCnt(bbAtt & e->control[op][Pawn]);
        }
    }
}

void EvalKing(Position* p, EvalData* e, int side)
{
    int square = p->king_sq[side];
    int bitboard = Paint(square);;

    square = kingRoot[square];

    if (bitboard & kMask[side]) {
        if (p->Map(side, Rook) & krMask[side]) {
            Add(e, side, F_OTHERS, trappedRookMg, trappedRookEg);
        }
    }

    if (bitboard & qMask[side]) {
        if (p->Map(side, Rook) & qrMask[side])
            Add(e, side, F_OTHERS, trappedRookMg, trappedRookEg);
    }
}

void EvalKingAttacks(Position* p, EvalData* e, int sd) {

    int op = sd ^ 1;
    int ksq = p->king_sq[op];
    Bitboard zone = Att.King(ksq);
    Bitboard defended = e->control[op][Pawn] | e->control[op][Knight] | e->control[op][Bishop] | e->control[op][Rook] | e->control[op][Queen];
    Bitboard attacked = e->control[sd][Pawn] | e->control[sd][Knight] | e->control[sd][Bishop] | e->control[sd][Rook];
    zone &= ~defended;
    zone &= attacked;
    e->att[sd] += queenContactCheck * PopCnt(zone & e->control[sd][Queen]);
    AddMg(e, sd, F_ATT, Danger.tab[Min(400, e->att[sd])]);
}

void Engine::PawnKingEval(Position* p, EvalData* e) {
    int addr = p->pawn_key % PAWN_HASH_SIZE;

#ifndef USE_TUNING
    if (PawnTT[addr].key == p->pawn_key) {
        e->mg[White][F_PAWNS] = PawnTT[addr].mg_pawns[White];
        e->mg[Black][F_PAWNS] = PawnTT[addr].mg_pawns[Black];
        e->eg[White][F_PAWNS] = PawnTT[addr].eg_pawns[White];
        e->eg[Black][F_PAWNS] = PawnTT[addr].eg_pawns[Black];
        e->mg[White][F_SHIELD] = PawnTT[addr].shield[White];
        e->mg[Black][F_SHIELD] = PawnTT[addr].shield[Black];
        return;
    }
#endif

    if (p->PawnComplex(White, D4, E5) && p->PawnComplex(Black, E6, D5)) {
        e->mg[White][F_PAWNS] += 20;
        if (p->IsOnSq(Black, Pawn, C5) && !p->IsOnSq(White, Pawn, C3))
            e->mg[Black][F_PAWNS] += 25;
    }

    // f4/f5

    const int c2malus = 0;
    const int f4bonus = 21;
    const int f2malus = 0;
    const int botwinnik_bonus = 0;
    const int tension_bonus = 3;

    if (p->Map(White, King) & Mask.ksCastle[White] &&
       (p->Map(Black, King) & Mask.ksCastle[Black])) {

        if (p->PawnComplex(White, C4, D4)) {
            if (p->IsOnSq(Black, Pawn, D5))
                AddMg(e, White, F_PAWNS, tension_bonus);
        }

        if (p->PawnComplex(White, D3, E4)) {
            //if (p->IsOnSq(White, Pawn, F2))
            //    AddMg(e, White, F_PAWNS, f2malus);
            if (p->IsOnSq(White, Pawn, F4))
            AddMg(e, White, F_PAWNS, f4bonus);
            //if (p->IsOnSq(White, Pawn, C4))
            //    AddMg(e, White, F_PAWNS, botwinnik_bonus);
        }

        if (p->PawnComplex(Black, D6, E5)) {
            //if (p->IsOnSq(Black, Pawn, F7))
            //    AddMg(e, Black, F_PAWNS, f2malus);
            if (p->IsOnSq(Black, Pawn, F5))
            AddMg(e, Black, F_PAWNS, f4bonus);
            //if (p->IsOnSq(Black, Pawn, C5))
            //    AddMg(e, Black, F_PAWNS, botwinnik_bonus);
        }

        //if (p->PawnComplex(White, E3, D4)) {
        //    if (p->IsOnSq(White, Pawn, C2))
        //        AddMg(e, White, F_PAWNS, c2malus);
        //}

        if (p->PawnComplex(Black, C5, D5)) {
            if (p->IsOnSq(White, Pawn, D4))
                AddMg(e, Black, F_PAWNS, tension_bonus);
        }

        //if (p->PawnComplex(Black, E6, D5)) {
        //    if (p->IsOnSq(Black, Pawn, C7))
        //        AddMg(e, Black, F_PAWNS, c2malus);
        //}

    }

    // No luft

    if (p->IsOnSq(White, King, H1) && p->PawnComplex(White, H2, G2))
        Add(e, White, F_SHIELD, noLuftMg, noLuftEg);

    if (p->IsOnSq(White, King, G1) && p->PawnComplex(White, H2, G2, F2))
        Add(e, White, F_SHIELD, noLuftMg, noLuftEg);

    if (p->IsOnSq(White, King, A1) && p->PawnComplex(White, A2, B2))
        Add(e, White, F_SHIELD, noLuftMg, noLuftEg);

    if (p->IsOnSq(White, King, B1) && p->PawnComplex(White, A2, B2, C2))
        Add(e, White, F_SHIELD, noLuftMg, noLuftEg);


    if (p->IsOnSq(Black, King, H8) && p->PawnComplex(Black, H7, G7))
        Add(e, Black, F_SHIELD, noLuftMg, noLuftEg);

    if (p->IsOnSq(Black, King, G8) && p->PawnComplex(Black, H7, G7, F7))
        Add(e, Black, F_SHIELD, noLuftMg, noLuftEg);

    if (p->IsOnSq(Black, King, A8) && p->PawnComplex(Black, A7, B7))
        Add(e, Black, F_SHIELD, noLuftMg, noLuftEg);

    if (p->IsOnSq(Black, King, B8) && p->PawnComplex(Black, A7, B7, C7))
        Add(e, Black, F_SHIELD, noLuftMg, noLuftEg);

    // Pawn chains (KID/KIA)

    if (p->Map(White, King) & Mask.ksCastle[White]) {
        if (p->PawnComplex(White, D5, E4, F3)) {
            if (p->PawnComplex(Black, D6, E5, F4)) {
                e->mg[Black][F_PAWNS] += chainBase;
                if (p->PawnComplex(Black, G5, H4))
                    e->mg[Black][F_PAWNS] += chainStBad;
                if (p->IsOnSq(Black, Pawn, G5))
                    e->mg[Black][F_PAWNS] += chainSt0;
                if (p->PawnComplex(Black, G5, H5))
                    e->mg[Black][F_PAWNS] += chainSt1;
                if (p->IsOnSq(Black, Pawn, G4))
                    e->mg[Black][F_PAWNS] += chainSt2;
            }
        }
    }

    if (p->Map(Black, King) & Mask.ksCastle[Black]) {
        if (p->PawnComplex(Black, D4, E5, F6)) {
            if (p->PawnComplex(White, D3, E4, F5)) {
                e->mg[White][F_PAWNS] += chainBase;
                if (p->PawnComplex(White, G4, H5))
                    e->mg[White][F_PAWNS] += chainStBad;
                if (p->IsOnSq(White, Pawn, G4))
                    e->mg[White][F_PAWNS] += chainSt0;
                if (p->PawnComplex(White, G4, H4))
                    e->mg[White][F_PAWNS] += chainSt1;
                if (p->IsOnSq(White, Pawn, G5))
                    e->mg[White][F_PAWNS] += chainSt2;
            }
        }
    }

    EvaluatePawns(p, e, White);
    EvaluatePawns(p, e, Black);
    EvaluateKing(p, e, White);
    EvaluateKing(p, e, Black);

    // King on the pawnless wing in the endgame

    /*
    if ((p->MapType(Pawn) & Mask.kingside) == 0) {
        e->eg[White][F_PAWNS] += hateKingside[p->king_sq[White]];
        e->eg[Black][F_PAWNS] += hateKingside[p->king_sq[Black]];
    }

    if ((p->MapType(Pawn) & Mask.queenside) == 0) {
        e->eg[White][F_PAWNS] += hateQueenside[p->king_sq[White]];
        e->eg[Black][F_PAWNS] += hateQueenside[p->king_sq[Black]];
    }
*/

#ifndef USE_TUNING
    PawnTT[addr].key = p->pawn_key;
    PawnTT[addr].mg_pawns[White] = e->mg[White][F_PAWNS];
    PawnTT[addr].mg_pawns[Black] = e->mg[Black][F_PAWNS];
    PawnTT[addr].eg_pawns[White] = e->eg[White][F_PAWNS];
    PawnTT[addr].eg_pawns[Black] = e->eg[Black][F_PAWNS];
    PawnTT[addr].shield[White] = e->mg[White][F_SHIELD];
    PawnTT[addr].shield[Black] = e->mg[Black][F_SHIELD];
#endif

}

void EvaluatePawns(Position* p, EvalData* e, int sd) {

    Bitboard bbPieces, bbSecond, frontSpan;
    int sq, companion, isUnopposed;
    bool isPhalanx, isDefended;
    int op = Opp(sd);

    // Loop through the pawns, evaluating each one

    bbPieces = p->Map(sd, Pawn);
    while (bbPieces) {
        sq = PopFirstBit(&bbPieces);
        frontSpan = FrontSpan(Paint(sq), sd);

        if (p->Map(sd, King) & Mask.ksCastle[sd]) {
            if (e->isKID[sd])
                Add(e, sd, F_PAWNS, Pst.mgKidLow[sd][Pawn][sq], Pst.egOne[sd][Pawn][sq]);
            else if (e->isKID[op])
                Add(e, sd, F_PAWNS, Pst.mgKidHigh[sd][Pawn][sq], Pst.egOne[sd][Pawn][sq]);
            else
                Add(e, sd, F_PAWNS, Pst.mgKs[sd][Pawn][sq], Pst.egOne[sd][Pawn][sq]);

        }
        else if (p->Map(sd, King) & Mask.qsCastle[sd])
            Add(e, sd, F_PAWNS, Pst.mgQs[sd][Pawn][sq], Pst.egOne[sd][Pawn][sq]);
        else
            Add(e, sd, F_PAWNS, Pst.mgOne[sd][Pawn][sq] /* + Tuner.adjust[RelSq(sq, sd)]*/, Pst.egOne[sd][Pawn][sq]);


        isUnopposed = ((frontSpan & p->Map(op, Pawn)) == 0);
        isPhalanx = (p->Map(sd, Pawn) & SidesOf(Paint(sq))) != 0;
        isDefended = ((Paint(sq) & e->control[sd][Pawn]) != 0);

        // Relationships

        bbSecond = p->Map(sd, Pawn);
        while (bbSecond) {
            companion = PopFirstBit(&bbSecond);
            if (companion > sq) {
                Add(e, sd, F_PAWNS, Pst.pawnRelationshipMg[sd][sq][companion], Pst.pawnRelationshipEg[sd][sq][companion]);
                /**   if (RelSq(sq, sd) == D5) {
                       Add(e, sd, F_PAWNS, Tuner.secretIngredient, 0);
                       Add(e, sd, F_PAWNS, Tuner.adjust[RelSq(companion, sd)], 0);
                   }*/
            }
        }

        // Candidate passer

        if ((isPhalanx || isDefended) && isUnopposed) {
            if (PopCnt((Mask.passed[sd][sq] & p->Map(Opp(sd), Pawn))) == 1) {
                if (PopCnt(Mask.support[sd][sq] & p->Map(sd, Pawn)) > 0) {
                    Add(e, sd, F_PAWNS, candidate_mg[sd][Rank(sq)], candidate_eg[sd][Rank(sq)]);
                }
            }
        }

        // Isolated pawn

        if (!(Mask.adjacent[File(sq)] & p->Map(sd, Pawn))) {
            Add(e, sd, F_PAWNS, isolPawnMg, isolPawnEg);
            if (isUnopposed)
                AddMg(e, sd, F_PAWNS, isolOpenMg);
        }

        // Backward pawn

        else if ((Mask.support[sd][sq] & p->Map(sd, Pawn)) == 0) {
            Add(e, sd, F_PAWNS, Pst.mgBackward[sd][sq], -8);
            if (isUnopposed)
                AddMg(e, sd, F_PAWNS, -8);
        }
    }
}

void EvaluatePassers(Position* p, EvalData* e, int sd) {

    Bitboard bbPawns, bbStop, bbNextStop, bbSpan, allAtt, allDef;
    int sq, fl_unopposed;
    bool isPhalanx, isDefended;
    int op = Opp(sd);

    // Loop through the pawns, evaluating each one

    bbPawns = p->Map(sd, Pawn);
    while (bbPawns) {
        sq = PopFirstBit(&bbPawns);
        Add(e, sd, F_MAT, mg_value[Pawn], eg_value[Pawn]);

        // Passed pawn

        if (!(Mask.passed[sd][sq] & p->Map(Opp(sd), Pawn))) {

            if (sd == White) bbSpan = FillNorth(ShiftNorth(Paint(sq)));
            else             bbSpan = FillSouth(ShiftSouth(Paint(sq)));

            if (bbSpan & p->Map(sd, Pawn)) {
                Add(e, sd, F_PASSERS, candidate_mg[sd][Rank(sq)], candidate_eg[sd][Rank(sq)]);
            }
            else {

                isPhalanx = (p->Map(sd, Pawn) & SidesOf(Paint(sq))) != 0;
                isDefended = ((Paint(sq) & e->control[sd][Pawn]) != 0);
                bbStop = ShiftFwd(Paint(sq), sd);
                bbNextStop = ShiftFwd(bbStop, sd);

                int mp = passed_bonus_mg[sd][Rank(sq)];
                int ep = passed_bonus_eg[sd][Rank(sq)]
                -((passed_bonus_eg[sd][Rank(sq)] * Dist.bonus[sq][p->king_sq[op]]) / 35)
                +((passed_bonus_eg[sd][Rank(sq)] * Dist.bonus[sq][p->king_sq[sd]]) / 25);

                int mul = 100;
                if (isPhalanx)
                    mul += phalanxPasser;
                else if (p->cl_bb[op] & bbStop)
                    mul += blockedPasser;
                else if (isDefended)
                    mul += defendedPasser;
                else {

                    // opponent is the only side to control square in front of a passer

                    if ((bbStop & e->AllAtt(p, op))
                        && (bbStop & ~e->AllAtt(p, sd)))
                        mul += stopSquareOpp;

                    // we are the only side to control control square in front of a passer

                    if ((bbStop & e->AllAtt(p, sd))
                        && (bbStop & ~e->AllAtt(p, op)))
                        mul += stopSquareOwn;
                }

                Add(e, sd, F_PASSERS, mp * mul / 100, ep * mul / 100);
            }
        }
    }
}

void EvaluateKing(Position* p, EvalData* e, int sd) {

    const int startSq[2] = { E1, E8 };
    const int qCastle[2] = { B1, B8 };
    const int kCastle[2] = { G1, G8 };

    Bitboard bbKingFile, bbNextFile;
    int result = 0;
    int sq = KingSq(p, sd);

    // Normalize king square for pawn shield evaluation,
    // to discourage shuffling the king between g1 and h1.

    if (Paint(sq) & bbKSCastle[sd]) sq = kCastle[sd];
    if (Paint(sq) & bbQSCastle[sd]) sq = qCastle[sd];

    // Evaluate shielding and storming pawns on each file.

    bbKingFile = FillNorth(Paint(sq)) | FillSouth(Paint(sq));
    result += EvalKingFile(p, sd, bbKingFile);

    bbNextFile = ShiftEast(bbKingFile);
    if (bbNextFile) 
        result += EvalKingFile(p, sd, bbNextFile);

    bbNextFile = ShiftWest(bbKingFile);
    if (bbNextFile) 
        result += EvalKingFile(p, sd, bbNextFile);

    e->mg[sd][F_SHIELD] += result;
}

int EvalKingFile(Position* p, int sd, Bitboard bbFile) {

    int shelter = EvalFileShelter(bbFile & p->Map(sd, Pawn), sd);
    int storm = EvalFileStorm(bbFile & p->Map(Opp(sd), Pawn), sd);

    if (bbFile & bbCentralFile) 
        return (shelter / 2) + storm;
    else 
        return shelter + storm;
}

int EvalFileShelter(Bitboard bbOwnPawns, int sd) {

    if (!bbOwnPawns) return -36;
    if (bbOwnPawns & bbRelRank[sd][rank2]) return    2;
    if (bbOwnPawns & bbRelRank[sd][rank3]) return  -10;
    if (bbOwnPawns & bbRelRank[sd][rank4]) return  -20;
    if (bbOwnPawns & bbRelRank[sd][rank5]) return  -27;
    if (bbOwnPawns & bbRelRank[sd][rank6]) return  -32;
    if (bbOwnPawns & bbRelRank[sd][rank7]) return  -35;
    return 0;
}

int EvalFileStorm(Bitboard bbOppPawns, int sd) {

    if (!bbOppPawns) return -16;
    if (bbOppPawns & bbRelRank[sd][rank3]) return -32;
    if (bbOppPawns & bbRelRank[sd][rank4]) return -16;
    if (bbOppPawns & bbRelRank[sd][rank5]) return -8;
    return 0;
}

void EvaluatePressure(Position* p, EvalData* e, int sd) {

    int s, t;
    int op = sd ^ 1;
    Bitboard opp = p->cl_bb[op];
    Bitboard att = e->control[sd][Pawn] | e->control[sd][Knight] | e->control[sd][Bishop] | e->control[sd][Rook] | e->control[sd][Queen] | e->control[sd][King];
    Bitboard def = e->control[op][Pawn] | e->control[op][Knight] | e->control[op][Bishop] | e->control[op][Rook] | e->control[op][Queen] | e->control[op][King];
    Bitboard ctrl = att & ~def;
    Bitboard hang = (opp & ctrl) | (opp & e->control[sd][Pawn]);
    Bitboard behind;

    //find squares behind own pawns

    if (sd == White)
        behind = FillSouth(p->Map(White, Pawn));
    else
        behind = FillNorth(p->Map(Black, Pawn));

    // evaluate space

    int minors = p->cnt[sd][Knight] + p->cnt[sd][Bishop];
    Bitboard space = Mask.space[sd];
    space &= (Mask.f[fileC] | Mask.f[fileD] | Mask.f[fileE] | Mask.f[fileF]);
    // TODO: try to include opponent's king wing

    space &= att;
    space |= ~def;

    int spaceBonus = minors * PopCnt(space) / 2;

    space |= behind;
    spaceBonus += minors * PopCnt(space);

    e->mg[sd][F_OTHERS] += (spaceBonus + minors * PopCnt(space)) * 33 / 100;

    while (hang) {
        s = PopFirstBit(&hang);
        t = TpOnSq(p, s);
        Add(e, sd, F_PRES, hangingMg[t], hangingEg[t]);
    }
}

void EvalBishopAtHome(Position* p, EvalData* e, int c, int bish, int pawn, int block, Bitboard king) {

    if (p->IsOnSq(c, Bishop, bish)) {

        // Case 1: central pawn whose move would open
        // the bishop is blocked - that's bad

        if (p->IsOnSq(c, Pawn, pawn)) {
            if (Paint(block) & p->Filled())
                Add(e, c, F_OTHERS, bBlockedMg, bBlockedEg);
        }
    }
}

void EvalUnstoppablePassers(Position* p, EvalData* e)
{
    Bitboard pawns, path;
    int wDst = 8;
    int bDst = 8;
    int square, enemyKing, pawnSq, tempo, promDst;

    // White unstoppable passers

    if (p->NonPawnCnt(Black) == 0) {

        enemyKing = p->king_sq[Black];
        if (p->side == Black)
            tempo = 1;
        else
            tempo = 0;

        pawns = p->Map(White, Pawn);
        while (pawns) {
            square = PopFirstBit(&pawns);
            if (!(Mask.passed[White][square] & p->Map(Black, Pawn))) {
                path = FrontSpan(Paint(square), White);
                pawnSq = ((White - 1) & 56) + (square & 7);
                promDst = Min(5, Dist.cheb[square][pawnSq]);

                if (promDst < (Dist.cheb[enemyKing][pawnSq] - tempo)) {
                    if (path & p->Map(White, King)) promDst++;
                    wDst = Min(wDst, promDst);
                }
            }
        }
    }

    // Black unstoppable passers

    if (p->NonPawnCnt(White) == 0) {

        enemyKing = p->king_sq[White];
        if (p->side == White)
            tempo = 1;
        else
            tempo = 0;

        pawns = p->Map(Black, Pawn);
        while (pawns) {
            square = PopFirstBit(&pawns);
            if (!(Mask.passed[Black][square] & p->Map(White, Pawn))) {
                path = FrontSpan(Paint(square), Black);
                pawnSq = ((Black - 1) & 56) + (square & 7);
                promDst = Min(5, Dist.cheb[square][pawnSq]);

                if (promDst < (Dist.cheb[enemyKing][pawnSq] - tempo)) {
                    if (path & p->Map(Black, King)) promDst++;
                    bDst = Min(bDst, promDst);
                }
            }
        }
    }

    if (wDst < bDst - 1) Add(e, White, F_OTHERS, 0, 500);
    if (bDst < wDst - 1) Add(e, Black, F_OTHERS, 0, 500);
}

void EvalTrappedBishop(Position* p, EvalData* e, int c, int bish, int pawn, int sc)
{
    if (p->IsOnSq(c, Bishop, bish) && p->IsOnSq(c ^ 1, Pawn, pawn))
        Add(e, c, F_OTHERS, sc, sc);
}

void EvalPin(Position* p, EvalData* e, int c, int pinned0, int pinned1, int knight, int bish0, int bish1) 
{
    if (p->IsOnSq(c^1, Knight, knight)) {
        if (p->IsOnSq(c, Bishop, bish0)
        || (p->IsEmpty(Paint(bish0)) && p->IsOnSq(c, Bishop, bish1))) 
        {
            if (p->IsOnSq(c ^ 1, King, pinned1)
            || p->IsOnSq(c ^ 1, Queen, pinned1))
            {
                Add(e, c, F_OTHERS, bPinMg, bPinEg);
            }
            else if (p->IsEmpty(Paint(pinned1))) 
            {
                if (p->IsOnSq(c^1, King, pinned0)
                || p->IsOnSq(c^1, Queen, pinned0)
                    || p->IsOnSq(c ^ 1, Rook, pinned0)
                    || p->IsOnSq(c ^ 1, Rook, pinned0))
                    Add(e, c, F_OTHERS, bPinMg, bPinEg);
            }
            else if (p->IsOnSq(c ^ 1, Bishop, pinned1)) 
            {
                AddMg(e, c, F_OTHERS, bPinBlunt);
            }
        }
    }
}

void Add(EvalData* e, int sd, int factor, int mg_bonus, int eg_bonus) 
{
    e->mg[sd][factor] += mg_bonus;
    e->eg[sd][factor] += eg_bonus;
}

void AddMg(EvalData* e, int sd, int factor, int mg_bonus)
{
    e->mg[sd][factor] += mg_bonus;
}

void PrintEval(Position* p) 
{
    EvalData e;
    int mg_score, eg_score, total;
    int mg_phase = Min(max_phase, p->phase);
    int eg_phase = max_phase - mg_phase;

    printf("Total score: %d\n", mainEngine.Evaluate(p, &e, 0));
    printf("-----------------------------------------------------------------\n");
    printf("Factor     | Val (perc) |   Mg (  WC,   BC) |   Eg (  WC,   BC) |\n");
    printf("-----------------------------------------------------------------\n");
    for (int factor = 0; factor < N_OF_FACTORS; factor++) {
        mg_score = e.mg[White][factor] - e.mg[Black][factor];
        eg_score = e.eg[White][factor] - e.eg[Black][factor];
        total = (((mg_score * mg_phase) + (eg_score * eg_phase)) / max_phase);

        printf(factor_name[factor]);
        printf(" | %4d (%3d) | %4d (%4d, %4d) | %4d (%4d, %4d) |\n", total, weights[White][factor], 
            mg_score, e.mg[White][factor], e.mg[Black][factor],
            eg_score, e.eg[White][factor], e.eg[Black][factor]);
    }
    printf("-----------------------------------------------------------------\n");
}
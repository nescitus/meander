#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "meander.h"
#include "timer.h"
#include <iostream>

const int bMobEg[] = { -22, -18, -13,  -8,  -3,   2,   8,  11,  13,  14,  15,  14,  15,  16, }; // temp

int engineLevel = numberOfLevels;
int evalBlur = 0;

void ReadLine(char *str, int n) {
  char *ptr;

  if (fgets(str, n, stdin) == NULL)
    exit(0);
  if ((ptr = strchr(str, '\n')) != NULL)
    *ptr = '\0';
}

char *ParseToken(char *string, char *token) {

  while (*string == ' ')
    string++;
  while (*string != ' ' && *string != '\0')
    *token++ = *string++;
  *token = '\0';
  return string;
}

void UciLoop(void) {

#ifdef USE_TUNING
    printf("This is a tuning version that takes up more memory and plays a bit weaker\n");
#endif

  char command[4096], token[80], *ptr;
  Position p[1];

  setbuf(stdin, NULL);
  setbuf(stdout, NULL);
  SetPosition(p, START_POS);
  AllocTrans(16);
  for (;;) {
    ReadLine(command, sizeof(command));
    ptr = ParseToken(command, token);
    if (strcmp(token, "uci") == 0) {
      printf("id name Meander 1.120\n");
      printf("id author Pawel Koziol (based on Sungorus 1.4 by Pablo Vazquez)\n");
      printf("option name Hash type spin default 16 min 1 max 4096\n");
      printf("option name Clear Hash type button\n");
	  printf("option name OwnAttack type spin default %d min 0 max 500\n", options[O_OWN_ATT]);
      printf("option name OppAttack type spin default %d min 0 max 500\n", options[O_OPP_ATT]);
      printf("option name OwnMobility type spin default %d min 0 max 500\n", options[O_OWN_MOB]);
      printf("option name OppMobility type spin default %d min 0 max 500\n", options[O_OPP_MOB]);
      printf("option name OwnTropism type spin default %d min 0 max 500\n", options[O_OWN_TROP]);
      printf("option name OppTropism type spin default %d min 0 max 500\n", options[O_OPP_TROP]);
      printf("option name OwnPressure type spin default %d min 0 max 500\n", options[O_OWN_PRES]);
      printf("option name OppPressure type spin default %d min 0 max 500\n", options[O_OPP_PRES]);
      printf("option name OwnPawnStruct type spin default %d min 0 max 500\n", options[O_OWN_PAWN]);
      printf("option name OppPawnStruct type spin default %d min 0 max 500\n", options[O_OPP_PAWN]);
	  //printf("option name PassedPawns type spin default %d min 0 max 500\n", weights[F_PASSERS]);
      printf("option name Level type spin default %d min 0 max 1024\n", engineLevel);
      printf("uciok\n");
    }
    else if (strcmp(token, "isready") == 0) {
        printf("readyok\n");
#ifdef USE_TUNING
    }
    else if (strcmp(token, "one") == 0) {
        int pv[MAX_PLY];
        double current, best = 1.0;
        Tuner.Init();

        for (int i = -5; i < 6; i++) {
            Tuner.secretIngredient = i;
            current = Tuner.TexelFit(p, pv);
            if (current < best) {
                best = current;
                printf("%d gains - %lf!\n", i, best);
            }
            else {
                printf("%d fails - %lf\n", i, best);
            }
        }
    }
    else if (strcmp(token, "fit") == 0) {
        int pv[MAX_PLY];
        Tuner.Init();
        printf("info string current fit: %lf\n", Tuner.TexelFit(p, pv));
    }
    else if (strcmp(token, "tune") == 0) {
        int pv[MAX_PLY];
        double current, best = 1.0;
        Tuner.Init();

        for (int s = 0; s < 64; s++) {
            Tuner.adjust[s] = 0;
        }

        int step = 1;

            for (int s = 8; s < 56; s++) {

                printf("square % d\n", s);
                current = Tuner.TexelFit(p, pv);
                best = current;
                printf("zero vfit %lf\n", current);
                Tuner.adjust[s] = -step;
                current = Tuner.TexelFit(p, pv);
                printf("minus fit %lf\n", current);
                if (current < best) {
                    best = current;
                    goto skip;
                }
                Tuner.adjust[s] = step;
                current = Tuner.TexelFit(p, pv);
                printf("plus  fit %lf\n", current);
                if (current >= best)
                    Tuner.adjust[s] = 0;
                else best = current;
            skip:

                if (Tuner.adjust[s] != 0) {
                    printf("--------------------------------------------\n");
                    printf("new fit  %lf\n", best);
                    printf("--------------------------------------------\n");
                    
                    for (int sq = 0; sq < 64; sq++) {
                        int inv = sq ^ (Black * 56);
                        int val = Pst.mgOne[White][Pawn][sq] + Tuner.adjust[sq];
                        if (sq == s)
                            printf("%3d,*", val);
                        else
                            printf("%3d, ", val);

                        if ((sq + 1) % 8 == 0) printf("\n");
                    }
                    
                }
            }
    
#endif
    } else if (strcmp(token, "setoption") == 0) {
      ParseSetoption(ptr);
    } else if (strcmp(token, "position") == 0) {
      ParsePosition(p, ptr);
    } else if (strcmp(token, "perft") == 0) {
      ptr = ParseToken(ptr, token);
	  int depth = atoi(token);
	  if (depth == 0) depth = 5;
	  Timer.SetStartTime();
	  nodes = mainEngine.Perft(p, 0, depth);
	  printf (" perft %d : %d nodes in %d miliseconds\n", depth, nodes, Timer.GetElapsedTime() );
    } else if (strcmp(token, "print") == 0) {
      PrintBoard(p);
    } else if (strcmp(token, "eval") == 0) {
      PrintEval(p);
    } else if (strcmp(token, "step") == 0) {
      ParseMoves(p, ptr);
    } else if (strcmp(token, "go") == 0) {
      ParseGo(p, ptr);
    } else if (strcmp(token, "bench") == 0) {
      ptr = ParseToken(ptr, token);
      Bench(atoi(token));
    } else if (strcmp(token, "quit") == 0) {
      exit(0);
    }
  }
}

void ParseSetoption(char *ptr) {

  char token[80], name[80], value[80] = "";

  ptr = ParseToken(ptr, token);
  name[0] = '\0';
  for (;;) {
    ptr = ParseToken(ptr, token);
    if (*token == '\0' || strcmp(token, "value") == 0)
      break;
    strcat(name, token);
    strcat(name, " ");
  }
  name[strlen(name) - 1] = '\0';
  if (strcmp(token, "value") == 0) {
    value[0] = '\0';

    for (;;) {
      ptr = ParseToken(ptr, token);
      if (*token == '\0')
        break;
      strcat(value, token);
      strcat(value, " ");
    }
    value[strlen(value) - 1] = '\0';
  }

  if (strcmp(name, "Hash") == 0)
  {
    AllocTrans(atoi(value));
  }
  else if (strcmp(name, "Clear Hash") == 0) 
  {
    ResetEngine();
  } 
  else if (strcmp(name, "OwnAttack") == 0) 
  {
    options[O_OWN_ATT] = atoi(value);
    ResetEngine();
  } 
  else if (strcmp(name, "OppAttack") == 0)
  {
      options[O_OPP_ATT] = atoi(value);
      ResetEngine();
  }
  else if (strcmp(name, "OwnMobility") == 0) 
  {
    options[O_OWN_MOB] = atoi(value);
    ResetEngine();
  }
  else if (strcmp(name, "OppMobility") == 0)
  {
      options[O_OPP_MOB] = atoi(value);
      ResetEngine();
  }
  else if (strcmp(name, "OwnPressure") == 0)
  {
      options[O_OWN_PRES] = atoi(value);
      ResetEngine();
  }
  else if (strcmp(name, "OppPressure") == 0)
  {
      options[O_OPP_PRES] = atoi(value);
      ResetEngine();
  }
  else if (strcmp(name, "OwnPawnStruct") == 0)
  {
      options[O_OWN_PAWN] = atoi(value);
      ResetEngine();
  }
  else if (strcmp(name, "OppPawnStruct") == 0)
  {
      options[O_OPP_PAWN] = atoi(value);
      ResetEngine();
  }
  else if (strcmp(name, "OwnTropism") == 0)
  {
      options[O_OWN_TROP] = atoi(value);
      ResetEngine();
  }
  else if (strcmp(name, "OppTropism") == 0)
  {
      options[O_OPP_TROP] = atoi(value);
      ResetEngine();
  }
  else if (strcmp(name, "Level") == 0) {
      engineLevel = atoi(value);
      ResetEngine();
  }
}

void ParseMoves(Position *p, char *ptr) {
	
  char token[80];
  UNDO u[1];
  int move;

  for (;;) {

    // Get next move to parse

    ptr = ParseToken(ptr, token);

	// No more moves!

    if (*token == '\0') 
        break;

    // Read move

    move = StrToMove(p, token);

    // Stuff for recapture detection

    lastTargetSquare = Tsq(move);
    lastVictim = TpOnSq(p, lastTargetSquare);

    // Make move

    p->DoMove(move, u);

	// We won't be taking back moves beyond this point:

    if (p->rev_moves == 0) p->head = 0;
  }
}

void ParsePosition(Position *p, char *ptr) {

  char token[80], fen[80];

  ptr = ParseToken(ptr, token);
  if (strcmp(token, "fen") == 0) {
    fen[0] = '\0';
    for (;;) {
      ptr = ParseToken(ptr, token);

      if (*token == '\0' || strcmp(token, "moves") == 0)
        break;

      strcat(fen, token);
      strcat(fen, " ");
    }
    SetPosition(p, fen);
  } else {
    ptr = ParseToken(ptr, token);
    SetPosition(p, START_POS);
  }

  if (strcmp(token, "moves") == 0)
    ParseMoves(p, ptr);
}

void ParseGo(Position *p, char *ptr) {

  char token[80], bestmove_str[6], ponder_str[6];
  int pv[MAX_PLY];
  mainEngine.isMain = true;
  helpEngine.isMain = false;
  mainEngine.depthReached = 0;
  helpEngine.depthReached = 0;

  Timer.Clear();
  pondering = 0;

  for (;;) {
    ptr = ParseToken(ptr, token);
    if (*token == '\0')
      break;
    if (strcmp(token, "ponder") == 0) {
      pondering = 1;
    } else if (strcmp(token, "wtime") == 0) {
      ptr = ParseToken(ptr, token);
      Timer.SetData(W_TIME, atoi(token));
    } else if (strcmp(token, "btime") == 0) {
      ptr = ParseToken(ptr, token);
      Timer.SetData(B_TIME, atoi(token));
    } else if (strcmp(token, "winc") == 0) {
      ptr = ParseToken(ptr, token);
      Timer.SetData(W_INC, atoi(token));
    } else if (strcmp(token, "binc") == 0) {
      ptr = ParseToken(ptr, token);
      Timer.SetData(B_INC, atoi(token));
    } else if (strcmp(token, "movestogo") == 0) {
      ptr = ParseToken(ptr, token);
      Timer.SetData(MOVES_TO_GO, atoi(token));
    } else if (strcmp(token, "depth") == 0) {
      ptr = ParseToken(ptr, token);
      Timer.SetData(FLAG_INFINITE, 1);
      Timer.SetData(MAX_DEPTH, atoi(token));
    } else if (strcmp(token, "infinite") == 0) {
      Timer.SetData(FLAG_INFINITE, 1);
    }
  }

  Timer.SetSideData(p->side);
  Timer.SetMoveTiming();
  Think(p, pv);

  MoveToStr(pv[0], bestmove_str);
  if (pv[1]) {
    MoveToStr(pv[1], ponder_str);
    printf("bestmove %s ponder %s\n", bestmove_str, ponder_str);
  } else
    printf("bestmove %s\n", bestmove_str);
}

void ResetEngine(void) {

  mainEngine.ClearHist(); // TODO: for all engine instances
  mainEngine.ClearEvalHash();

  ClearTrans();
}
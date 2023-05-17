#include "meander.h"

#ifdef USE_TUNING

void cTuner::Init() {
    cnt10 = 0;
    cnt01 = 0;
    cnt05 = 0;

    FILE* epdFile = NULL;
    epdFile = fopen("quiet-extended.epd", "r");
    printf("reading epdFile 'quiet-extended.epd' (%s)\n", epdFile == NULL ? "failure" : "success");

    char line[256];
    char* pos;
    std::string posString;
    int readCnt = 0;

    if (epdFile == NULL) {
        printf("Epd file not found!");
        return;
    }

    while (fgets(line, sizeof(line), epdFile)) {    // read positions line by line

        while ((pos = strpbrk(line, "\r\n"))) *pos = '\0'; // cleanup
        posString = line;
        readCnt++;
        if (readCnt % 1000000 == 0)
            printf("%d positions loaded\n", readCnt);

        if (posString.find("1/2-1/2") != std::string::npos) {
            epd05[cnt05] = posString;
            cnt05++;
        }
        else if (posString.find("1-0") != std::string::npos) {
            epd10[cnt10] = posString;
            cnt10++;
        }
        else if (posString.find("0-1") != std::string::npos) {
            epd01[cnt01] = posString;
            cnt01++;
        }
    }

    fclose(epdFile);
    printf("%d Total positions loaded\n", readCnt);

    /*
    Position p;
    int pv[MAX_PLY];
    for (int i = -10; i <= 10; i++) {
        Tuner.secretIngredient = i;
        printf("FIT FOR %d: %lf\n", i, Tuner.TexelFit(&p, pv));
    }*/

}

double cTuner::TexelFit(Position* p, int* pv) {

    int score = 0;
    double sigmoid = 0.0;
    double sum = 0.0;
    double k_const = 1.250;
    int iteration = 0;
    //Trans.Clear();
    //ClearAll();

    double result = 1;

    for (int i = 0; i < cnt10; ++i) {
        iteration++;
        char* cstr = new char[epd10[i].length() + 1];
        strcpy(cstr, epd10[i].c_str());
        SetPosition(p, cstr);
        delete[] cstr;
        //Par.InitAsymmetric(p);
        score = mainEngine.Quiesce(p, 0, -INF, INF, pv);
        if (p->side == Black) score = -score;
        sigmoid = TexelSigmoid(score, k_const);
        sum += ((result - sigmoid) * (result - sigmoid));
    }

    result = 0;

    for (int i = 0; i < cnt01; ++i) {
        iteration++;
        char* cstr = new char[epd01[i].length() + 1];
        strcpy(cstr, epd01[i].c_str());
        SetPosition(p, cstr);
        delete[] cstr;
        //Par.InitAsymmetric(p);
        score = mainEngine.Quiesce(p, 0, -INF, INF, pv);
        if (p->side == Black) score = -score;
        sigmoid = TexelSigmoid(score, k_const);
        sum += ((result - sigmoid) * (result - sigmoid));
    }

    result = 0.5;

    for (int i = 0; i < cnt05; ++i) {
        iteration++;
        char* cstr = new char[epd05[i].length() + 1];
        strcpy(cstr, epd05[i].c_str());
        SetPosition(p, cstr);
        delete[] cstr;
        //Par.InitAsymmetric(p);
        score = mainEngine.Quiesce(p, 0, -INF, INF, pv);
        if (p->side == Black) score = -score;
        sigmoid = TexelSigmoid(score, k_const);
        sum += ((result - sigmoid) * (result - sigmoid));
    }

    return 1000 * ((1.0 / iteration) * sum);
}

double cTuner::TexelSigmoid(int score, double k) {

    double exp = -(k * ((double)score) / 400.0);
    return 1.0 / (1.0 + pow(10.0, exp));
}

#endif
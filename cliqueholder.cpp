#include "cliqueholder.h"
#include "gadget.h"
#include <cstdio>
#include <algorithm>
#include <bitset>
#include <cassert>
#include <cmath>
#include <iostream>
using namespace std;

extern VI lookup;
extern Graph g;
double visi_lastdelete=0;

inline bool compv(int a, int b) {
    return lookup[a]<lookup[b];
}

CliqueHolder::CliqueHolder() {
}

void CliqueHolder::init(double _tau, bool _filter, FILE *_fout) {
    
    fout = _fout;
    cnt = sumsize = 0;
    filter = _filter;
    tau = _tau;
}

bool CliqueHolder::exactFilter(VI &C1, VI &C2, int t) {    
    int f1 = C1.front(), e1 = C1.back();
    int f2 = C2.front(), e2 = C2.back();
    return min(e1,e2)-max(f1,f2)<=t || (C1*C2).size()<=t;
}
int taggg=0,tagge=0;
bool CliqueHolder::passFilter(VI &C) {
    
    int upovl = (int)floor(C.size()*getTau());
    
    multimap<int,int>::iterator itlow, itup, it;
    itlow= lv.begin();
    itup= lv.upper_bound(g.deg(D.front())-1);
    
    vector<multimap<int,int>::iterator> toerase;
    for (it=itlow; it!=itup; ++it)
        toerase.push_back(it);
    for (int i=0; i<toerase.size(); ++i)
        lv.erase(toerase[i]);
    toerase.clear();
    
    bool pass=true;
    int ncomp=0;
    for (it=itup; it!= lv.end(); ++it) {
        int i= (*it).second;
        ++ncomp;
        VI &cli=cliques[i];
        int j=cli.size()-1;
        while (j>=0 && lookup[C.front()] < lookup[cli[j]]) --j;
        if (cli.size()-j<3) {
            toerase.push_back(it);
            continue;
        }
        
        if (cliques[i].size()<upovl)
            continue;
        
        VI P=cli;
        sort(P.begin(), P.end());
        taggg+=P.size()+C.size();
        if (!exactFilter(P, C, upovl)) {
            pass=false;
            break;
        }
    }
    
    for (int i=0; i<toerase.size(); ++i)
        lv.erase(toerase[i]);
    
    return pass;
}


double visibility=0.0;
int maxtuan;
int lsnumber=0;
int lessthan2 = 0;
int realfinalprune = 0;

bool CliqueHolder::insert(VI &C, char* function) {
    
        if (C.size()<2)
    {lessthan2++;
        lsnumber++;
        return false;}
    
        if (function[0]=='N')
    {
        int upovl = (int)floor(C.size()*getTau());
        if ((L*C).size()>upovl){            realfinalprune++;
            lsnumber++;
            visi_lastdelete+=(L*C).size()/double(C.size());
            return false;}
    }
    taggg+=L.size()+C.size();
    D=C;
    tagge++;
    sort(D.begin(), D.end(), compv);
    
    if (filter) {
        if (!passFilter(C))
            return false;
    }
    
    int id=cliques.size();
    cliques.push_back(D);
    lv.insert(make_pair(g.deg(D.back()),id));
    
    
    int qe=(L*C).size();
    double temp=(double )qe/ (double)C.size();
    visibility+=temp;
    
    
    sumsize += C.size();
    L = C;
    if (C.size()> maxcli.size())
        maxcli = C;
    
    vprint(D, fout);
    return true;
}

int CliqueHolder::updateScore(int i, VI &D) {
    
        VI &C = cliques[i];
    C= C-D;
    return C.size();
}

int CliqueHolder::topk(int k) {
    
    printf("top-%d diverse cliques\n\n");
    int quality=0;
    VI best;
    int nc=cliques.size();
    vector<bool> inans(nc, 0);
    scores.resize(nc, -1);
    for (int i=0; i<min(k,nc); ++i) {
        int scorebest=-1, ibest=-1;
        for (int j=0; j<nc; ++j)
            if (!inans[j]) {
                int score = updateScore(j, best);                 if (score>scorebest) {
                    scorebest = score;
                    ibest = j;
                }
            }
        quality+= scorebest;
        assert(scorebest>=0 && ibest>=0);
        best = cliques[ibest];
        inans[ibest]=1;
        vprint(best);
        printf("\n");
    }
    
    return quality;
}



int lsnumberfunc()
{
    return lsnumber;
}





int summarysize(void)
{
    return tagge;
}
int realfinalprunefunc()
{
    return realfinalprune;
}
int lessthan2func()
{
    return lessthan2;
}
int visi_lastdeletefunc()
{
    return visi_lastdelete;
}

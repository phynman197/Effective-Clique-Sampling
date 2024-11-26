#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstdio>
#include <cassert>
#include <cstring>
#include <queue>
#include <algorithm>
#include <cmath>
#include <ctime>
#include "graph.h"
#include "gadget.h"
#include "cliqueholder.h"
#include "TemData.hpp"
#include "TrussDe.hpp"

using namespace std;
string datasetname;
void cliSearch2(VI &C, VI &cand, VI &prev);
int realfinalprunefunc();
int lessthan2func();
int summarysize(void);
int visi_lastdeletefunc();
int lsnumberfunc();
typedef vector<int> VI;
typedef vector<VI> VVI;

Graph g;
double tau;
bool randomized, filter, dotopk;
char est;

CliqueHolder holder;VI tmp, unit(1);
int *lookup;
int ntofilter;VI L, D, E, X, hg;
FILE *fcliques;

int *vtable;
int *vCore;



double visi = 0;int ndelete = 0;

struct doubleint{
    int x;
    int y;
};


bool LessSort (doubleint a,doubleint b) {
    return (a.y>b.y); }

int degeneracyOrdering(Graph & g, int par, char* order) {
    
    int n=g.V();    int *bin = (int*)alloc(n);
    int *pv = (int*)alloc(n);
    int *pos = (int*)alloc(n);
    int *tdeg = (int*)alloc(n);
    int* templookup = (int*)alloc(n);
    int*tempdegree = (int*)alloc(n);    
    memset(bin, 0, sizeof(int)*n);     memset(tdeg, 0, sizeof(int)*n);
    
    int maxCoreNumber = 0;

    
    for (int i=0; i<n; ++i) tdeg[i] = g.deg(i);    for (int i=0; i<n; ++i) ++bin[tdeg[i]];    
    int c=0;
    for (int i=0; i<n; ++i) {
        int d=bin[i];
        bin[i] = c;
        c += d;
    }    for (int i=0; i<n; ++i) {
        pos[i]=bin[tdeg[i]];        tempdegree[i] = pos[i];
        pv[pos[i]]=i;        ++bin[tdeg[i]];    }
    for (int i=n-1; i>0; --i)
        bin[i]=bin[i-1];
    bin[0]=0;    
    for (int i=0; i<n; ++i) {
        int v=pv[i], dv=tdeg[v];        
        
        
        if(dv>maxCoreNumber){
            maxCoreNumber = dv;
                    }
        if(par==0){
            
       
            
            
            
            if (order[0] == 'I')
                lookup[v]=i;
            if (order[0] == 'R')
                lookup[v]=v;
            if (order[0] == 'D')
                lookup[v]=n-1-i;
            
            
            
            
            
            
            
            
            
        }
        for (int j=0; j<g.deg(v); ++j) {
            int w=(g.adjvec(v))[j], dw=tdeg[w];
            if (dw>dv) {
                int pw=pos[w];
                int pt=bin[dw];
                int t=pv[pt];
                if (t!=w) {
                    pos[w]=pt, pos[t]=pw;
                    pv[pw]=t, pv[pt]=w;
                }
                ++bin[dw];
                --tdeg[w];

            }
        }
    }
    
    
    
    

    free(bin);
    free(pos);
    free(pv);
    if(par==0){
        for(int i=0;i<g.V();i++){
            vCore[i]=tdeg[i];
        }
    }

    free(tdeg);
    free(templookup);
    free(tempdegree);
    
    if(par==0){

                    if (order[0] == 'T')
                        {
                        TrussDe TrussDecomposition;
                        TrussDecomposition.runTD("no_use", lookup);
                    }
                }
    
    return maxCoreNumber;

}


int hLocalDegreeDobund(VI & cand){
    
    int i=0;
    for(int v: cand){
        vtable[v]=i;
        ++i;
    }
    
        Graph localG(cand.size());
    int maxDeg = 0;
    for(int v: cand){
        VI nvs = g.adjvec(v);         VI nvsincand = cand*nvs;
        int vInCand = vtable[v];
        localG.setDeg(vInCand,nvsincand.size());
        if(localG.deg(vInCand)>maxDeg){
            maxDeg = localG.deg(vInCand);
        }
    }
    
    int *count =(int*)alloc(maxDeg);
        
        
    for(int v: cand){
        int vInCand = vtable[v];
        count[localG.deg(vInCand)]+=1;
    }
    
    
    int result = maxDeg;
    int acc=0;
    if(maxDeg>0){
        for(int j=maxDeg-1; j>=0;--j){
            acc+=count[j];
            if(acc>j+1){                result =j+1;
                break;
            }
        }
        
    }
    free(count);
    return result+1;
    
    
}

int MaxDegree(VI & cand){
    
    int i=0;
    for(int v: cand){
        vtable[v]=i;
        ++i;
    }
    
        Graph localG(cand.size());
    int maxDeg = 0;
    for(int v: cand){
        VI nvs = g.adjvec(v);         VI nvsincand = cand*nvs;
        int vInCand = vtable[v];
        localG.setDeg(vInCand,nvsincand.size());
        if(localG.deg(vInCand)>maxDeg){
            maxDeg = localG.deg(vInCand);
        }
    }
    
    return maxDeg+1;
    
}


TemData coreBound(VI &cand){
    TemData t;
    int bound = 0;
                        int i=0;
        for(int v: cand){
                vtable[v]=i;
        ++i;
    }
    Graph localG(cand.size());
            int maxInt =0;
    int maxV = -1;
    for(int v: cand){
        VI nvs = g.adjvec(v);         VI nvsincand = cand*nvs;
        int vInCand = vtable[v];
        localG.setDeg(vInCand,nvsincand.size());
        if(maxInt<nvsincand.size()){
            maxInt = nvsincand.size();
            maxV = v;
        }
        for(int j:nvsincand){
            
            int jInCand = vtable[j];
            localG.addEdge(vInCand,jInCand);
                    }
    }
    
    char* a = new char[5];
    a[0] = 'R';
    t.bound = degeneracyOrdering(localG,1,a)+1;
    t.maxInters = maxInt;
    t.maxV = maxV;
            return t;
}

int  hCoreBound(VI & cand){
    
    int maxdep=0;
    for(int v: cand){
        if(maxdep<vCore[v]){
            maxdep = vCore[v];
        }
    }
    
    int *count =(int*)alloc(maxdep);
        
        
    for(int v: cand){
        count[vCore[v]]+=1;
    }
    
    
    int result = maxdep;
    
    if(maxdep>0){
        for(int j=maxdep-1; j>=0;--j){
            if(count[j]>j){
                result =j;
                break;
            }
        }
        
    }
    free(count);
    return result;
}


inline double NewprobSample(double r) {
    return r<tau? (tau-r)/(1-r) :0;
}

inline double OldprobSample(double r) {
        return(1.0-r)*(2.0-tau)/(2.0-r-tau);
}

inline double probKeep(double r, double pprod, int d, char* function) {    if (function[0]=='N')
        return pow(NewprobSample(r), 1.0/d);
    else
        return pow(OldprobSample(r), 1.0/d);


        
}

inline bool keepBranch(double pr) {
    return double(rand())/RAND_MAX < pr;
}








void cliSearch(VI &C, VI &cand, VI &prev, double pprod, char* bound, char* function) {
    
        if (cand.empty() && prev.empty()) {
        ++ntofilter;
        holder.insert(C, function);
        return;
    }
    
    if (cand.empty() && !prev.empty()) {

        return;
    }
    
        int nc=cand.size();
    int maxdep;    
    if (bound[0]=='L')
        maxdep = nc;
    
    
    if (bound[0]=='C')
    {
        TemData t = coreBound(cand);
        maxdep = t.bound;    }
    
    if (bound[0]=='H')
    {
        
        maxdep = hLocalDegreeDobund(cand);
    }

    if (bound[0]=='M')
    {
        
        maxdep = MaxDegree(cand);
    }

    
        L=holder.last();
    X=C*L;    E= cand-L;
    int cx=X.size(), ce=E.size(), cc=C.size();
    double minr=1.0;
    for (int t=1; t<=maxdep; ++t) {
        double tr= double(max(t-ce,0)+cx)/(cc+t);
        minr = min(tr, minr);
    }
    
    double pr=1.0;
    int maxl = maxdep+C.size();

        pr = probKeep(minr, pprod, maxl, function);
        if (!keepBranch(pr))
        {
                        int maxdeg=-1, pivot=-1;
            tmp=cand+prev;
            for (int i=0; i<tmp.size(); ++i) {
                int v=tmp[i];
                int dv=(g.adjvec(v)*cand).size();
                if (dv>maxdeg)
                    maxdeg=dv, pivot = v;
            }
            
                        VI doing(cand-g.adjvec(pivot));
            for (int i=0; i<doing.size(); ++i) {
                int v = doing[i];
                unit[0]=v;                C= C+unit;
                cand= cand-unit;
                VI candt(cand*g.adjvec(v)), prevt(prev*g.adjvec(v));                
                
                int before = ndelete;                 cliSearch2(C, candt, prevt);
                
                
                unit[0]=v;
                C= C-unit;
                prev= prev+unit;
            }
        }
    else
    {
    
        int maxdeg=-1, pivot=-1;
    tmp=cand+prev;
    for (int i=0; i<tmp.size(); ++i) {
        int v=tmp[i];
        int dv=(g.adjvec(v)*cand).size();
        if (dv>maxdeg)
            maxdeg=dv, pivot = v;
    }
    
            
    VI doing(cand-g.adjvec(pivot));
    for (int i=0; i<doing.size(); ++i) {
        int v = doing[i];
        unit[0]=v;        C= C+unit;
        cand= cand-unit;
        VI candt(cand*g.adjvec(v)), prevt(prev*g.adjvec(v));        cliSearch(C, candt, prevt, pprod*pr, bound, function);
        unit[0]=v;
        C= C-unit;
        prev= prev+unit;
    }
    }
}












void cliSearch2(VI &C, VI &cand, VI &prev) {
    
        if (cand.empty() && prev.empty()) {
        L=holder.last();
        int qq=(L*C).size();
        double temp=(double )qq/ (double)C.size();
        visi+=temp;
        ndelete++;
        return;
    }
    
    if (cand.empty() && !prev.empty()) {

        return;
    }
    
    
        int maxdeg=-1, pivot=-1;
    tmp=cand+prev;
    for (int i=0; i<tmp.size(); ++i) {
        int v=tmp[i];
        int dv=(g.adjvec(v)*cand).size();
        if (dv>maxdeg)
            maxdeg=dv, pivot = v;
    }
    
        VI doing(cand-g.adjvec(pivot));
    for (int i=0; i<doing.size(); ++i) {
        int v = doing[i];
        unit[0]=v;        C= C+unit;
        cand= cand-unit;
        VI candt(cand*g.adjvec(v)), prevt(prev*g.adjvec(v));        cliSearch2(C, candt, prevt);
        unit[0]=v;
        C= C-unit;
        prev= prev+unit;
    }
}









int pritag(void);

int main(int argc, char** argv)
{
    
    clock_t start, finish;
    char ses[50]="Ainput3.txt";    list2adj(argv[1],ses);
    datasetname = argv[1];
    cout<<"input yes"<<endl;
    g.build(ses);
    vCore =  (int*)alloc(g.V());
    vtable = new int[g.V()];
        start = clock();
    
    tau = atof(argv[2]);
    randomized = (argv[3][0]=='R');
    filter = (argv[4][0]=='G');
    fcliques = fopen(argv[5], "w");
    
    lookup = (int*)alloc(g.V());    int* sortedV = new int[g.V()];
    degeneracyOrdering(g,0,argv[6]);
    
        VI oc, odoing, ocand, oprev;    for (int i=0; i<g.V(); ++i) {
        odoing.push_back(i);
    }


    
        holder.init(tau, filter, fcliques);
    
    for (int ci=0; ci<odoing.size(); ++ci)
    {
                int i=odoing[ci];
        
        ocand.clear();
        oprev.clear();
        
        vector<doubleint> vint;
        
                
              
        
        
                for (int j=0; j<g.deg(i); ++j) {            int v= g.dest(i,j);

            if (lookup[i]<lookup[v]){
                doubleint t;
                t.x = v;
                t.y = lookup[v];
                vint.push_back(t);
                            }
            else
                oprev.push_back(v);
        }

        if (!vint.empty())
            sort(vint.begin(), vint.end(), LessSort);
                while (!vint.empty())
        {

            doubleint tt = *(vint.end()-1);
                                    ocand.push_back(tt.x);
            vint.pop_back();
        }
        
                
        
        
        
        
        
        
        
        oc.clear();
        oc.push_back(i);
        cliSearch(oc, ocand, oprev, 1.0, argv[7], argv[8]);
    }
    double  duration;
    finish = clock();
    duration = (double)(finish - start) / CLOCKS_PER_SEC;
    
    
    
    
    
    
    
    
    
        printf("\n");
    cout<<"clique total number： "<<ndelete + lessthan2func() + realfinalprunefunc() + summarysize()<<endl;
    cout<<"during sampling ndelete: "<<ndelete<<endl;
    cout<<"last step deleted："<<lessthan2func()+realfinalprunefunc()<<endl;
    cout<<"Summary Size: "<<summarysize()<<endl;
    
    
    cout<<"TIME= "<<duration<<endl;
    double visiout = double(visi+visi_lastdeletefunc()+summarysize())/(ndelete
                                                                       +realfinalprunefunc()+summarysize());
    cout<<"average visibility：visi = "<<visiout<<endl;
    cout<<"single vertex："<<lessthan2func()<<endl<<endl;
    
    ofstream oFile;
    
    string boundstr = argv[7];
    string functionstr = argv[8];
    string orderstr = argv[6];
         oFile.open(string("/Users/xiaofanli/Desktop/Research/Code/ICDMcode/newsizeTruss/output/") + string("s") + boundstr + orderstr + functionstr + string(".csv"), ios::app );        if (atof(argv[2])==0.5)
    {
        oFile<<argv[1]<<","<<argv[3]<<","<<argv[6]<<","<<argv[7]<<","<<argv[8]<<endl;

        oFile<<"0.5"<<","<<"0.5"<<","<<"0.6"<<","<<"0.6"<<","<<"0.7"<<","<<"0.7"<<","<<"0.8"<<","<<"0.8"<<","<<"0.9"<<","<<"0.9"<<endl;

    }
    oFile <<visiout<<","<<summarysize();
    if (atof(argv[2])==0.9)
    {
        oFile<<endl<<endl;

    }
    else
        oFile<<",";


    oFile.close();
    
    fclose(fcliques);
    free(lookup);
    delete [] sortedV;

    return 0;
}

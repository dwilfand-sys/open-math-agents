// Independent integer-only audit, using complete residue rows and subwindows.
#include <array>
#include <cassert>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 array<int,119> cap{};ifstream f(argc>1?argv[1]:"/tmp/r5-table.txt");string line;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int n,v;if(s>>n>>v)cap[n]=v;}
 cap[116]=68;
 for(int N:{117,118}){
  int den=N==117?113:54,K=N==117?69:70;vector<int>w(N+1,N==117?65:31);
  if(N==117){for(int i:{1,2,116,117})w[i]=113;}
  else{for(int i:{1,2,3,116,117,118})w[i]=54;for(int i:{4,5,114,115})w[i]=27;}
  int total=0;for(int i=1;i<=N;i++){total+=w[i];assert(w[i]==w[N+1-i]);}assert(total==den*K);
  long long checks=0;
  for(int d=1;d<N;d++)for(int r=1;r<=d;r++){
   vector<int>prefix{0};for(int i=r;i<=N;i+=d)prefix.push_back(prefix.back()+w[i]);
   for(int l=0;l+1<(int)prefix.size();l++)for(int h=l+1;h<(int)prefix.size()&&h-l<=116;h++){
    assert(prefix[h]-prefix[l]<=den*cap[h-l]);checks++;
   }
  }
  // Scalar table comparisons used in the short written proof.
  if(N==117){for(int m=2;m<=115;m++)assert(226+65*(m-2)<=113*cap[m]);}
  else{for(int m=6;m<=114;m++)assert(162+31*(m-3)<=54*cap[m]);}
  cout<<"N="<<N<<" K="<<K<<" checks="<<checks<<" all exact inequalities passed\n";
 }
}

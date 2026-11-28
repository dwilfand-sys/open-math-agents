// Audit the recovered statement, not its unrecovered proof.
// Translate any three-point set to {0,a,b}, and test every invertible step.
#include <algorithm>
#include <cstdlib>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
int main(int argc,char**argv){
 int upto=argc>1?std::atoi(argv[1]):200;long long triples=0,units_tested=0,direct_triples=0;
 for(int N=4;N<=upto;N+=2){
  std::vector<int> units;for(int u=1;u<N;++u)if(std::gcd(u,N)==1)units.push_back(u);
  std::vector<uint64_t> arcs;
  if(N<=60)for(int d:units)for(int start=0;start<N;++start){
   uint64_t mask=0;for(int j=0;j<N/2;++j)mask|=uint64_t(1)<<((start+j*d)%N);arcs.push_back(mask);
  }
  for(int a=1;a<N;++a)for(int b=a+1;b<N;++b){
   ++triples;bool predicted=a==N/2||b==N/2||b-a==N/2||(3*a==N&&3*b==2*N);
   bool hits=true;
   for(int u:units){
    ++units_tested;int x=u*a%N,y=u*b%N;if(x>y)std::swap(x,y);
    if(std::max({x,y-x,N-y})>N/2){hits=false;break;}
   }
   if(hits!=predicted){std::cout<<"COUNTEREXAMPLE "<<N<<" 0 "<<a<<" "<<b<<" hits="<<hits<<" predicted="<<predicted<<std::endl;return 2;}
   if(N<=60){
    ++direct_triples;uint64_t H=1|(uint64_t(1)<<a)|(uint64_t(1)<<b);bool direct=true;
    for(uint64_t arc:arcs)if((arc&H)==0){direct=false;break;}
    if(direct!=hits){std::cerr<<"DIRECT ARC MISMATCH\n";return 3;}
   }
  }
 }
 std::cout<<"AGREED through "<<upto<<"; normalized triples "<<triples<<"; unit tests "<<units_tested<<"; direct arc triples "<<direct_triples<<"\n";
}

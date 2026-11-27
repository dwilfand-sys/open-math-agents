'use strict';

const {scale}=require('./lagneau_crt_bound.cjs');
const probabilityUnits=1_000_000;
const hazardUnits=100_000;
const probabilityStep=scale/BigInt(probabilityUnits);
const hazardStep=scale/BigInt(hazardUnits);

// Replace each of two stochastically independent risks by a smaller discrete
// variable. A lower bound for P(H>=h) remains valid at each lower grid point.
function distribution(tails) {
  const result=[];
  let previous=0;
  const levels=[...tails].sort(([a],[b])=>b-a);
  for(const [level,tail] of levels) {
    if(level>0 && tail>previous) {
      result.push([level,tail-previous]);
      previous=tail;
    }
  }
  if(previous<probabilityUnits)result.push([0,probabilityUnits-previous]);
  return result;
}

function jointUpper(prior,weight,left,right) {
  const histogram=new Map();
  for(const [i,ni] of left)for(const [j,nj] of right) {
    // 1-(1-i/N)(1-j/N), rounded down to an integer number of steps.
    const level=i+j-Math.ceil(i*j/hazardUnits);
    histogram.set(level,(histogram.get(level)||0)+ni*nj);
  }
  const probabilityProduct=BigInt(probabilityUnits)**2n;
  let unfilled=prior*probabilityProduct, lost=0n;
  for(const [level,frequency] of [...histogram].sort(([a],[b])=>a-b)) {
    const capacity=weight*BigInt(frequency);
    const take=unfilled<capacity?unfilled:capacity;
    lost+=take*BigInt(level);
    unfilled-=take;
    if(!unfilled)break;
  }
  if(unfilled)throw Error('Prior exceeds small-mask measure');
  return prior-lost/(probabilityProduct*BigInt(hazardUnits));
}

function connect() {
  let negative;
  return {marginal({weight,mask,prior,positive,mixed}) {
    if(!positive)negative=null;
    if(mixed || prior===0n || (positive && !negative))return;
    // Masks with at most three selected small primes carry most of the mass.
    let bits=mask;
    for(let i=0;i<3 && bits;i++)bits&=bits-1;
    if(bits)return;
    const tails=new Map();
    return {
      record(h,tail) {
        const i=Number(h/hazardStep), n=Number(tail/probabilityStep);
        if(i>0 && n>(tails.get(i)||0))tails.set(i,n);
      },
      finish(oldUpper) {
        const law=distribution(tails);
        if(!positive) {
          negative={weight,mask,prior,law};
          return oldUpper;
        }
        if(negative.mask!==mask || negative.weight!==weight)throw Error('Incompatible sign weights');
        const upper=jointUpper(negative.prior,weight,negative.law,law);
        negative=null;
        return upper<oldUpper?upper:oldUpper;
      }
    };
  }};
}
module.exports={connect,distribution,jointUpper,hazardUnits,probabilityUnits};

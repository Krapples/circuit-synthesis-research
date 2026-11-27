"use strict";
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};let seed=870067;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const bit=(x,i)=>(x>>>i)&1,par=x=>{let p=0;for(;x;x&=x-1)p^=1;return p};
 let cases=0,assignments=0,rank0=0,rank1=0,rank2=0,phaseChecks=0,protectedChecks=0,pairedChecks=0,outputChecks=0;
 for(let z=0;z<1200;z++){
  let d=1+rnd(6),q=1+rnd(4),h=rnd(1+Math.floor((d-1)/2)),free=d-2*h,mask=(1<<free)-1,n=d+q;
  let a=rnd(1<<n),b=rnd(1<<n),ca=rnd(2),cb=rnd(2),out=rnd(2);
  let u=a&mask,v=b&mask,rank=(!u&&!v)?0:(!u||!v||u===v)?1:2;
  if(rank===0){rank0++;continue}if(rank===2){rank2++;continue}rank1++;
  if(!u){[a,b]=[b,a];[ca,cb]=[cb,ca];u=a&mask}
  let pivot=0;while(!bit(u,pivot))pivot++;
  let others=Array.from({length:n},(_,i)=>i).filter(i=>i!==pivot),child=rnd(1<<n),seen=new Set;
  for(let t=0;t<1<<(n-1);t++){
   let x=0;for(let j=0;j<others.length;j++)x|=bit(t,j)<<others[j];
   let p=par(a&x)^ca;x|=p<<pivot;
   assert((par(a&x)^ca)===0,"controlling");assert((x>>d)===(t>>(d-1)),"protected query");
   let ok=true;for(let j=0;j<h;j++)if(bit(x,free+2*j)&&bit(x,free+2*j+1))ok=false;
   if(!ok)continue;
   let g=((par(a&x)^ca)&(par(b&x)^cb))^out,old=g^par(child&x),now=out^par(child&x);
   assert(g===out&&old===now,"deletion");assert(!seen.has(x),"injective");seen.add(x);assignments++;phaseChecks++;protectedChecks++;if(h)pairedChecks++;outputChecks++;
  }
  assert(seen.size===(1<<(free-1+q))*3**h,"domain size");cases++;
 }
 // Rank-one deficit ledger, for arbitrary sequences of local moves.
 let ledgers=0;
 for(let z=0;z<1000;z++){let D=1+rnd(100),a=D,r=0,p=0,W=0;while(a>0&&rnd(4)){let b=rnd(2);if(b){r++;W-=8}else{p++;W-=10}a--}assert(W===-10*(D-a)+2*r&&W===-8*(D-a)-2*p,"ledger");ledgers++}
 return {seed:870067,cases,rank0,rank1,rank2,assignments,phaseChecks,protectedChecks,pairedChecks,outputChecks,ledgers}
}
console.log(JSON.stringify(replay(),null,2));

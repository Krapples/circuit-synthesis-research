"use strict";
// Exhaustive local C4-free rectangle, cleaner and star replacement identities.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};let seed=870069;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n},pc=x=>{let n=0;for(;x;x&=x-1)n++;return n};
 function graph(l,r,mask){let n=l+r,edges=[],N=Array(n).fill(0);for(let i=0;i<l;i++)for(let j=0;j<r;j++)if(mask>>(i*r+j)&1){let k=l+j;edges.push((1<<i)|(1<<k));N[i]|=1<<k;N[k]|=1<<i}if(N.some((a,i)=>N.some((b,j)=>i<j&&pc(a&b)>1)))return null;let f=0n;for(let x=0;x<1<<n;x++)if(edges.some(e=>(e&x)===e))f|=1n<<BigInt(x);return {n,edges,N,f}}
 function tabs(n){return Array.from({length:1<<n},(_,s)=>{let f=0n;for(let x=0;x<1<<n;x++)if(x&s)f|=1n<<BigInt(x);return f})}
 let graphs=0,rectangles=0,dirty=0,cleanReaders=0,edgeChecks=0,both=0,one=0,none=0,overlap=0,overlapClean=0,strict=0,tie=0,controls=[];
 for(let [l,r] of [[2,2],[2,3],[3,3]]){let n=l+r,T=tabs(n),G=0;for(let z=1;z<1<<(l*r);z++){let g=graph(l,r,z);if(!g)continue;graphs++;G++;for(let A=1;A<1<<n;A++)for(let B=A;B<1<<n;B++){if(pc(A)<2||pc(B)<2||A&B)continue;rectangles++;let J=T[A]&T[B];if((J&~g.f)===0n)continue;dirty++;let ca=0,cb=0,valid=[];
 for(let C=1;C<1<<n;C++){if((J&T[C]&~g.f)!==0n)continue;valid.push(C);cleanReaders++;let a=A&C,b=B&C;ca|=a;cb|=b;for(let i=0;i<n;i++){if(a>>i&1)assert((g.N[i]&B)===B,"row universal");if(b>>i&1)assert((g.N[i]&A)===A,"column universal")}assert(pc(a)<=1&&pc(b)<=1,"C4 centres");
 let edges=g.edges.filter(e=>((J&T[C])>>BigInt(e))&1n),pred=g.edges.filter(e=>((e&a)&&(e&B))||((e&b)&&(e&A)));assert(edges.join()===pred.join(),"reader edge formula");edgeChecks++;
 }
 assert(pc(ca)<=1&&pc(cb)<=1,"global centres");let k=Number(!!ca)+Number(!!cb);if(k===2)both++;else if(k===1)one++;else none++;
 if(k>0&&valid.length){let U=valid[rnd(valid.length)],v=valid[rnd(valid.length)],W=U|v,aa=A&W,bb=B&W,old=(J&T[W]),newf=(T[aa]&T[B])|(T[bb]&T[A]);assert((newf&~g.f)===0n,"star safe");assert(g.edges.every(e=>((old>>BigInt(e))&1n)===((newf>>BigInt(e))&1n)),"union pair exact");let K=Number(!!aa)+Number(!!bb);for(let readers=1;readers<=5;readers++){let delta=2*K-1-readers;if(delta<0)strict++;if(delta===0)tie++}}
 }
 // overlap >=2 forces a unique common cleaner for every pure reader.
 for(let A=1;A<1<<n;A++)for(let B=A;B<1<<n;B++){let I=A&B;if(pc(I)<2)continue;overlap++;let J=T[A]&T[B],all=0;for(let C=1;C<1<<n;C++){if((J&T[C]&~g.f)!==0n)continue;all|=C;overlapClean++;for(let i=0;i<n;i++)if(I>>i&1)assert((g.N[i]&C)===C,"intersection cleaner")}assert(pc(all)<=1,"unique global cleaner")}
 }controls.push({l,r,graphs:G})}
 // Explicit P4 local obstruction: both exposed centres; neither global
 // expansion J->A nor J->B is sound at reader C=(a OR b).
 let g=graph(2,2,7),T=tabs(4),A=3,B=12,C=5,J=T[A]&T[B];assert((J&T[C])===g.f,"P4 factorization");assert((T[A]&T[C]&~g.f)!==0n&&(T[B]&T[C]&~g.f)!==0n,"no operand expansion");
 // Actual five-gate dirty circuit has four-gate clean star cover.
 let clean=(T[1]&T[12])|(T[2]&T[4]);assert(clean===g.f,"P4 clean comparator");
 return {seed:870069,graphs,rectangles,dirty,cleanReaders,edgeChecks,both,one,none,overlap,overlapClean,strict,tie,controls,p4:{dirtyGates:5,cleanGates:4}}
}
console.log(JSON.stringify(replay(),null,2));

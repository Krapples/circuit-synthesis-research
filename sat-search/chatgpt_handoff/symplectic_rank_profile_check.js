"use strict";
// Exact symplectic contraction and rank profile regression.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870040;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const bit=i=>1n<<BigInt(i);
 const pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 function basis(vs){let p=new Map;for(let v of vs)while(v){let k=v&-v;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}return [...p.values()]}
 const rank=vs=>basis(vs).length;
 function diff(h,s){let S=new Set;for(let m of h){let x=m&s;for(let j=x;j;j=(j-1)&x){let v=m^j;S.has(v)?S.delete(v):S.add(v)}}return [...S]}
 function poly(m,r){let H=[];for(let i=0;i<1<<m;i++)if(pc(i)===r){let mask=0;for(let j=0;j<m;j++)if(i>>j&1)mask|=3<<(2*j);H.push(mask)}return H}
 function om(a,b,m){let p=0;for(let i=0;i<m;i++)p^=((a>>(2*i)&1)&(b>>(2*i+1)&1))^((a>>(2*i+1)&1)&(b>>(2*i)&1));return p}
 function space(B){let K=[0];for(let b of B)K.push(...K.map(x=>x^b));return K}
 function topDegree(h){return h.reduce((a,b)=>Math.max(a,pc(b)),0)}
 function allPlanes(n,d){let out=[];function go(B,pivs){if(B.length===d){out.push(B);return}let start=pivs.length?pivs[pivs.length-1]+1:0;for(let p=start;p<=n-(d-B.length);p++){let next=B.map(b=>b); // rightmost? choose lowest-bit pivot p; earlier rows must zero at p.
 // build RREF at final pivot choices instead
 go(next.concat(1<<p),pivs.concat(p))
 }} 
 // enumerate pivot sets then free entries to right, excluding all pivots
 function piv(P,start){if(P.length===d){let mask=P.reduce((a,p)=>a|(1<<p),0),B=P.map(p=>1<<p);function fill(i){if(i===d){out.push(B.slice());return}let free=((1<<n)-1)^((1<<(P[i]+1))-1);free&=~mask;for(let s=free;;s=(s-1)&free){B[i]=(1<<P[i])|s;fill(i+1);if(!s)break}}fill(0);return}for(let p=start;p<=n-(d-P.length);p++)piv(P.concat(p),p+1)}
 piv([],0);return out}
 function sample(n,d){let B=[],K=[0];while(B.length<d){let v=1+rnd((1<<n)-1);if(K.includes(v))continue;B.push(v);K.push(...K.map(x=>x^v))}return B}
 function mixedRank(F,K){let rows=[];for(let a of K){let w=0n;for(let x=0;x<F.length;x++)if(F[x^a]^F[x]^F[a]^F[0])w|=bit(x);rows.push(w)}return rank(rows)}
 let tests=0,nonconstant=0,constantTop=0,saturatedChecks=0,isoChecks=0,profiles=[];
 for(let m=2;m<=6;m++)for(let r=2;r<=m;r++){
  let n=2*m,H=poly(m,r),F=n<=8?Uint8Array.from({length:1<<n},(_,x)=>H.reduce((a,b)=>a^Number((x&b)===b),0)):null;
  let count=0;
  for(let d=1;d<=Math.min(2*r,n);d++){
   let exhaustive=n<=6&&d<=4,planes=exhaustive?allPlanes(n,d):Array.from({length:60},()=>sample(n,d));
   for(let B of planes){
    let h=rank(B.map(a=>B.reduce((w,b,j)=>w|(om(a,b,m)?bit(j):0n),0n)))/2;
    let p=H;for(let b of B)p=diff(p,b);
    let top=d-h<=r&&d<=2*r;
    assert((p.includes(0)||p.length>0)||!top,"nonzero top");
    if(top){assert(topDegree(p)===2*r-d,"contraction degree");if(d<2*r)nonconstant++;else constantTop++}
    else assert(topDegree(p)<2*r-d||p.length===0,"vanishing top");
    if(top&&d<2*r&&F){assert(mixedRank(F,space(B))===(1<<d)-1,"saturated");saturatedChecks++}
    // isotropic subspace coordinate singles control
    tests++;count++;
   }
  }
  // explicit coordinate isotropic rank lower bound for every dimension <=m
  if(F)for(let d=1;d<=m;d++){let B=Array.from({length:d},(_,i)=>1<<(2*i)),cap=0;for(let s=1;s<1<<d;s++)if(pc(s)<=r)cap++;assert(mixedRank(F,space(B))>=cap,"isotropic binomial");isoChecks++}
  let basic=m+Math.floor(r/2),refined=Math.ceil((m+3*r-2)/2),degree=2*r-1;
  profiles.push({m,r,checks:count,basic,refined,degree,lower:Math.max(basic,refined,degree)});
 }
 return {seed:870040,tests,nonconstant,constantTop,saturatedChecks,isoChecks,profiles};
}
console.log(JSON.stringify(replay(),null,2));

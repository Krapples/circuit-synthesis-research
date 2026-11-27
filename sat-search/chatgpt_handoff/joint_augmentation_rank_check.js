"use strict";
// Exact augmentation-ideal rank regression, including GF(4) pencil specializations.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870038;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const bit=i=>1n<<BigInt(i);
 const xor=(a,b)=>{let S=new Set(a);for(let m of b)S.has(m)?S.delete(m):S.add(m);return [...S]};
 const mul=(a,b)=>{let S=new Set;for(let x of a)for(let y of b){let m=x|y;S.has(m)?S.delete(m):S.add(m)}return [...S]};
 const sum=(m,g)=>g.reduce((p,h,i)=>m>>i&1?xor(p,h):p,[]);
 function basis(vs){let p=new Map;for(let v of vs)while(v){let k=v&-v;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}return [...p.values()]}
 const rank=vs=>basis(vs).length;
 function rows(h,mode="full"){let M=new Map;for(let m of h)for(let i=m;;i=(i-1)&m){if(mode==="full"||mode==="mix"&&i&&i!==m)M.set(i,(M.get(i)||0n)|bit(m^i));if(!i)break}return [...M.values()]}
 function apply(v,ops){let out=0n;while(v){let b=v&-v,m=b.toString(2).length-1;v^=b;for(let a of ops)if((a&m)===a)out^=bit(m^a)}return out}
 function diff(h,s){let S=new Set;for(let m of h){let x=m&s;for(let j=x;j;j=(j-1)&x){let v=m^j;S.has(v)?S.delete(v):S.add(v)}}return [...S]}
 function op(n,unit=false){let S=[];for(let j=0;j<n;j++)if(rnd(2))S.push(1<<j);for(let j=0;j<10;j++)S=xor(S,[1+rnd((1<<n)-1)]);return unit?[0,...S]:S}
 function conv(a,b){let S=[];for(let x of a)for(let y of b)if(!(x&y))S=xor(S,[x|y]);return S}
 // GF(4) elimination on pairs of bitsets, omega^2=omega+1.
 function rank4(vs){let p=new Map;for(let [a,b] of vs){while(a||b){let k=(a|b)&-(a|b),x=!!(a&k),y=!!(b&k);if(!x&&y){[a,b]=[a^b,a]}else if(x&&y){[a,b]=[b,a^b]}if(p.has(k)){let [c,d]=p.get(k);a^=c;b^=d}else{p.set(k,[a,b]);break}}}return p.size}
 let cases=0,normalized=0,nonzeroL=0,positiveHomology=0,pencil4=0,pencil4Less=0,zeroL=0,maxByT={},maxQ=0,identity=0;
 for(let t=1;t<=6;t++)for(let z=0;z<80;z++){
  let g=[];for(let i=0;i<t;i++)g.push(mul(xor([1<<(2*i)],sum(rnd(1<<i),g)),xor([1<<(2*i+1)],sum(rnd(1<<i),g))));
  let W=basis(g.flatMap(h=>rows(h))),J=rank(g.flatMap(h=>rows(h,"mix")));
  let A=op(2*t),act=rank(W.map(w=>apply(w,A)));assert(act<=2**t,"arbitrary augmentation bound");assert(W.every(w=>apply(apply(w,A),A)===0n),"square zero");
  maxByT[t]=Math.max(maxByT[t]||0,act);cases++;
  let s=z%5===0?0:rnd(1<<(2*t)),L=[];for(let j=s;j;j=(j-1)&s)L.push(j);
  let LW=W.map(w=>apply(w,L)),l=rank(LW),B=basis([1n,...LW]),AW=W.map(w=>apply(w,A));
  let newG=[[3],...g.map(h=>xor(h.map(m=>m<<2),diff(h,s).map(m=>(m<<2)|3)))],newW=basis(newG.flatMap(h=>rows(h)));
  assert(rank(newG.flatMap(h=>rows(h,"mix")))===J+2*B.length,"joint update");identity++;
  // Arbitrary normalized operator A+D_a+D_b Q+D_aD_b R.
  let Q=op(2*t,!!rnd(2)),R=op(2*t,!!rnd(2)),T=[...A.map(a=>a<<2),1,...Q.map(a=>(a<<2)|2),...R.map(a=>(a<<2)|3)];
  let actual=rank(newW.map(w=>apply(w,T)));
  // Tagged elimination of A w modulo B gives L(A^-1 B).
  let piv=new Map,images=[];
  for(let b of B){while(b){let k=b&-b;if(piv.has(k))b^=piv.get(k)[0];else{piv.set(k,[b,0n]);break}}}
  for(let i=0;i<W.length;i++){let x=AW[i],y=LW[i];while(x){let k=x&-x;if(piv.has(k)){let [a,b]=piv.get(k);x^=a;y^=b}else{piv.set(k,[x,y]);break}}if(!x)images.push(y)}
  let pred=rank([...AW,...B])+rank([1n,...images]);assert(pred===actual,"normalized exact rank");
  // Multiply by arbitrary unit P; preserves image rank.
  let P=op(2*t,true),Tw=conv(P.map(a=>a<<2),T);
  assert(rank(newW.map(w=>apply(w,Tw)))===actual,"unit normalization");normalized++;
  if(l){
   nonzeroL++;
   // Tagged elimination computes A(ker L) and its image modulo im L.
   let p=new Map,Kimg=[];
   for(let i=0;i<W.length;i++){let x=LW[i],y=AW[i];while(x){let k=x&-x;if(p.has(k)){let [a,b]=p.get(k);x^=a;y^=b}else{p.set(k,[x,y]);break}}if(!x)Kimg.push(y)}
   let q=rank([...B,...Kimg])-l;
   assert(actual===2*l+q,"homology rank formula");if(q)positiveHomology++;maxQ=Math.max(maxQ,q);
   // GF(4) pencil specialization is a lower bound on rational-function generic rank,
   // not always guaranteed to reach l+q.
   let r4=rank4(LW.map((a,i)=>[a,AW[i]]));assert(r4<=2**t,"extension field augmentation bound");
   if(r4>=l+q)pencil4++;else pencil4Less++;
  }else{zeroL++;assert(actual<=act+2,"zero L")}
  assert(actual<=2**(t+1),"new generic rank cap");
 }
 return {seed:870038,cases,normalized,nonzeroL,zeroL,positiveHomology,maxQ,pencil4,pencil4Less,identity,maxByT};
}
console.log(JSON.stringify(replay(),null,2));

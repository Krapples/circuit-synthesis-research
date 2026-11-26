"use strict";
// Exact finite replay, run with node multi_baseline_transversal_check.js
function replay(){
 let seed=870030;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};const assert=(v,m)=>{if(!v)throw Error(m)};
 const pivot=v=>v.toString(2).length-1;
 function basis(vs){let p=new Map;for(let v of vs){while(v){let b=pivot(v);if(p.has(b))v^=p.get(b);else{p.set(b,v);break}}}return [...p.values()]}
 function intersect(A,B){
   let p=new Map,out=[];
   for(let v of B){while(v){let k=pivot(v);if(p.has(k))v^=p.get(k)[0];else{p.set(k,[v,0n]);break}}}
   for(let a of A){let v=a,w=a;while(v){let k=pivot(v);if(p.has(k)){let [b,z]=p.get(k);v^=b;w^=z}else{p.set(k,[v,w]);break}}if(!v&&w)out.push(w)}
   return basis(out)
 }
 const bit=i=>1n<<BigInt(i);
 let circuits=0,baselines=0,pairs=0,triangularChecks=0,spanChecks=0,strict=0,degreeStrict=0,partitionChecks=0;
 function check(d,k,g,out){
  const N=1<<d,Q=1<<k,full=(1n<<BigInt(N))-1n,off=1+d+k;
  const xs=Array.from({length:d},(_,i)=>{let w=0n;for(let x=0;x<N;x++)if(x>>i&1)w|=bit(x);return w});
  const xor=(mask,w)=>w.reduce((a,v,i)=>mask&bit(i)?a^v:a,0n);
  const rows=Array.from({length:Q},(_,q)=>{let w=[full,...xs,...Array.from({length:k},(_,i)=>q>>i&1?full:0n)],ops=[];for(const [u,v] of g){let a=xor(u,w),b=xor(v,w);ops.push([a,b]);w.push(a&b)}return {w,ops,f:xor(out,w)}});
  const kind=g.map((_,i)=>rows.every(r=>r.w[off+i]===rows[0].w[off+i])?"data":rows.every(r=>r.w[off+i]===0n||r.w[off+i]===full)?"query":"mixed");
  let ids=kind.flatMap((k,i)=>k==="mixed"?[i]:[]);
  const ingress=ids.flatMap(i=>g[i].map(mask=>xor(mask,rows[0].w.map((v,j)=>j===0||j>d&&j<off||j>=off&&kind[j-off]!=="data"?0n:v))));
  const deg=v=>{let a=Array.from({length:N},(_,x)=>Number(v>>BigInt(x)&1n));for(let i=0;i<d;i++)for(let x=0;x<N;x++)if(x>>i&1)a[x]^=a[x^(1<<i)];return Math.max(0,...a.map((v,i)=>v?i.toString(2).replace(/0/g,"").length:0))};
  const maxdeg=B=>Math.max(0,...B.map(deg));
  const W=basis(rows.map(r=>r.f^rows[0].f));
  let spaces=[],signatures=[];
  const sig=(vs,x)=>vs.map(v=>Number(v>>BigInt(x)&1n)).join("");
  const ingressSign=Array.from({length:N},(_,x)=>sig(ingress,x));
  for(let q=0;q<Q;q++){
   const row=rows[q];let S=[full],actual=ids.flatMap(i=>row.ops[i]),pred=[];
   let w=row.w.slice();for(let i=0;i<g.length;i++)if(kind[i]==="mixed")w[off+i]=0n;
   for(let i of ids){let a=xor(g[i][0],w),b=xor(g[i][1],w);pred.push(a,b);assert(a===row.ops[i][0]&&b===row.ops[i][1],"triangular forward");w[off+i]=a&b;triangularChecks++}
   let sigs=Array.from({length:N},(_,x)=>sig(actual,x));signatures.push(new Set(sigs).size);
   for(let x=0;x<N;x++)for(let y=0;y<x;y++){assert((sigs[x]===sigs[y])===(ingressSign[x]===ingressSign[y]),"partition");partitionChecks++}
   for(let j=0;j<actual.length;j+=2)S=basis([...S,...S.map(v=>v&actual[j]),...S.map(v=>v&actual[j+1])]);
   assert(basis([...S,...W]).length===S.length,"individual containment");spanChecks++;spaces.push(S);baselines++;
  }
  let common=spaces.reduce(intersect);assert(basis([...common,...W]).length===common.length,"joint containment");
  // Independent intersection check via |A intersect B| rank formula, including all pairwise intersections.
  for(let i=0;i<Q;i++)for(let j=0;j<i;j++){let I=intersect(spaces[i],spaces[j]);assert(I.length===spaces[i].length+spaces[j].length-basis([...spaces[i],...spaces[j]]).length,"intersection rank");assert(basis([...I,...spaces[i]]).length===spaces[i].length&&basis([...I,...spaces[j]]).length===spaces[j].length,"intersection inclusion");pairs++}
  let dims=spaces.map(s=>s.length),degs=spaces.map(maxdeg),r={d,k,mixed:ids.length,dims,degreeCaps:degs,intersection:common.length,intersectionDegree:maxdeg(common),actual:W.length,actualDegree:maxdeg(W),images:signatures};
  if(common.length<Math.min(...dims))strict++;if(maxdeg(common)<Math.min(...degs))degreeStrict++;circuits++;return r
 }
 for(let z=0;z<220;z++){
  let d=2+rnd(3),k=1+rnd(3),n=1+rnd(6),off=1+d+k;
  let g=Array.from({length:n},(_,i)=>[BigInt(rnd(1<<(off+i))),BigInt(rnd(1<<(off+i)))]);
  check(d,k,g,BigInt(rnd(1<<(off+n))))
 }
 // x=(a,b,c,d); q=(p,q,r); pure h=c*d, mixed g1=(a+p)(b+q), g2=r*(h+g1).
 let explicit=check(4,3,[[bit(3),bit(4)],[bit(1)^bit(5),bit(2)^bit(6)],[bit(7),bit(8)^bit(9)]],bit(10));
 assert(explicit.dims.every(x=>x===6)&&explicit.intersection===4&&explicit.actual===4,"explicit span");
 assert(explicit.degreeCaps.every(x=>x===3)&&explicit.intersectionDegree===2&&explicit.actualDegree===2,"explicit degree");
 assert(explicit.images.every(x=>x===8),"image");
 // Two disjoint copies of simpler h=c case, XOR output. All 64 query baselines.
 let d=6,k=6,off=13,g=[];
 for(let j=0;j<2;j++){let a=1+3*j,b=a+1,c=a+2,p=7+3*j,q=p+1,r=p+2;g.push([bit(a)^bit(p),bit(b)^bit(q)]);g.push([bit(r),bit(c)^bit(off+2*j)])}
 let tensor=check(d,k,g,bit(off+1)^bit(off+3));
 assert(tensor.dims.every(x=>x===36)&&tensor.intersection===16&&tensor.images.every(x=>x===64),"tensor");
 return {seed:870030,circuits,baselines,pairs,triangularChecks,spanChecks,partitionChecks,strict,degreeStrict,explicit,tensor:{...tensor,dims:[tensor.dims[0],"... all equal"],degreeCaps:[tensor.degreeCaps[0],"... all equal"],images:[tensor.images[0],"... all equal"]}}
}
console.log(JSON.stringify(replay(),null,2));

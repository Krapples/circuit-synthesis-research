"use strict";
// Exact last-gate Schur complement replay. Run node translation_last_gate_check.js.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870033;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const bit=i=>1n<<BigInt(i);
 const xor=(a,b)=>{let S=new Set(a);for(let v of b)S.has(v)?S.delete(v):S.add(v);return [...S]};
 const mul=(a,b)=>{let S=new Set;for(let u of a)for(let v of b){let w=u|v;S.has(w)?S.delete(w):S.add(w)}return [...S]};
 const sum=(m,g)=>g.reduce((v,h,i)=>m>>i&1?xor(v,h):v,[]);
 function rank(rows){let piv=new Map;for(let v of rows)while(v){let k=v&-v;if(piv.has(k))v^=piv.get(k);else{piv.set(k,v);break}}return piv.size}
 function ker(cols){
  let piv=new Map,out=[];for(let i=0;i<cols.length;i++){let v=cols[i],w=bit(i);while(v){let k=v&-v;if(piv.has(k)){let [a,b]=piv.get(k);v^=a;w^=b}else{piv.set(k,[v,w]);break}}if(!v)out.push(w)}
  return {rank:piv.size,basis:out};
 }
 const parity=v=>{let p=0;while(v){v&=v-1n;p^=1}return p};
 function mat(h,n,full){
  let N=1<<n,rows=Array(full?N:N-1).fill(0n);
  for(let m of h){
   if(full){for(let i=m;;i=(i-1)&m){rows[i]|=bit(m^i);if(!i)break}}
   else{for(let i=(m-1)&m;i;i=(i-1)&m)rows[i-1]|=bit((m^i)-1)}
  }return rows;
 }
 function coeff(h){return h.reduce((a,m)=>m?a|bit(m-1):a,0n)}
 function apply(A,w){let out=0n;for(let i=0;i<A.length;i++)if(w&bit(i))out^=A[i];return out}
 let checks=0,nonzero=0,largest=0,maxResidualCase=null,chain=[],branch=[];
 function check(n,U,V,W){
  assert(!U.includes(0)&&!V.includes(0)&&!W.includes(0),"zero anchored");
  let h=xor(mul(U,V),W),a=1<<n,b=1<<(n+1);
  let H=xor(xor(h,[a|b]),xor(V.map(x=>x|a),U.map(x=>x|b)));
  let C=mat(U,n,false),B=mat(V,n,false),A=mat(h,n,false),u=coeff(U),v=coeff(V),N=(1<<n)-1;
  for(let i=0;i<N;i++){if(u&bit(i))A[i]^=v;if(v&bit(i))A[i]^=u}
  let {rank:r,basis:K}=ker(B.map((z,i)=>z|(C[i]<<BigInt(N))));
  let R=K.map(k=>{let q=apply(A,k),row=0n;for(let i=0;i<K.length;i++)if(parity(q&K[i]))row|=bit(i);return row});
  let s=rank(R),actual=rank(mat(H,n+2,true)),mixed=rank(mat(H,n+2,false));
  assert(actual===4+2*r+s&&mixed===actual-2&&s%2===0,"Schur formula");
  checks++;if(s)nonzero++;if(s>largest){largest=s;maxResidualCase={n,U,V,W,r,s,actual}}
  return {n,r,s,actual,mixed};
 }
 for(let i=0;i<240;i++){
  let t=1+rnd(3),g=[];
  for(let j=0;j<t;j++)g.push(mul(xor([1<<(2*j)],sum(rnd(1<<j),g)),xor([1<<(2*j+1)],sum(rnd(1<<j),g))));
  check(2*t,sum(rnd(1<<t),g),sum(rnd(1<<t),g),sum(rnd(1<<t),g))
 }
 // Chain final gate: U=last old, V=W=0.
 let g=[3];for(let t=1;t<=4;t++){let r=check(2*t,g,[],[]);assert(r.s===0&&r.actual===2**(t+2),"chain");chain.push(r);g=xor(g.map(m=>m|(1<<(2*t+1))),[(1<<(2*t))|(1<<(2*t+1))])}
 // Two disjoint prior seed gates, final merge: positive residual needed.
 let b=check(4,[3],[12],[]);assert(b.r===4&&b.s===4&&b.actual===16,"fork");branch.push(b);
 // Explicit small witness 2x5, mixed rank from direct truth table.
 let m=2,l=5,d=m*l,k=m+l,rows=Array(1<<d).fill(0n);
 function f(x,q){for(let j=0;j<l;j++)if(q>>(m+j)&1){let ok=true;for(let i=0;i<m;i++)if((q>>i&1)&&!(x>>(i*l+j)&1))ok=false;if(ok)return 1}return 0}
 for(let x=0;x<1<<d;x++)for(let q=0;q<1<<k;q++)if(f(x,q)^f(x,0)^f(0,q)^f(0,0))rows[x]|=bit(q);
 let wr=rank(rows);assert(wr===93,"witness");
 return {seed:870033,checks,nonzeroResiduals:nonzero,largestResidual:largest,maxResidualCase,chain,branch,witness:{m,l,rank:wr,assignments:(1<<d)*(1<<k)}};
}
console.log(JSON.stringify(replay(),null,2));

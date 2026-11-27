"use strict";
// Exact parallel-fiber gate elimination, priority quotient and hybrid lower bound regression.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870041;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 const par=x=>pc(x)&1;
 const rank=vs=>{let p=new Map;for(let v of vs){while(v){let b=v&-v;if(p.has(b))v^=p.get(b);else{p.set(b,v);break}}}return p.size};
 const span=(B,v)=>rank([...B,v])===rank(B);
 function circuit(d,k,g,out){
  const N=1<<d,Q=1<<k,off=1+d+k,mask=(N-1)<<1;
  function evalAll(x,q){let w=1|(x<<1)|(q<<(1+d));for(let i=0;i<g.length;i++)if(par(w&g[i][0])&&par(w&g[i][1]))w|=1<<(off+i);return w}
  let T=out.map(o=>Array.from({length:Q},(_,q)=>Array.from({length:N},(_,x)=>par(evalAll(x,q)&o))));
  const raw=g.map(([a,b])=>[(a&mask)>>1,(b&mask)>>1]);
  let support=[0,...Array(d).fill(1),...Array(k).fill(0)],active=0;
  for(let i=0;i<g.length;i++){let s=0;for(let j=0;j<off+i;j++)if((g[i][0]|g[i][1])>>j&1)s|=support[j];support.push(s);active+=s}
  return {d,k,N,Q,g,out,off,evalAll,T,raw,active};
 }
 function demands(T,N,Q,d){
  let D=[],aff=0;
  for(let F of T){let base=null;for(let q=0;q<Q;q++){
   let a=0;for(let i=0;i<d;i++)if(F[q][0]^F[q][1<<i])a|=1<<i;
   if(F[q].every((f,x)=>f===(F[q][0]^par(a&x)))){aff++;if(base===null)base=a;else D.push(a^base)}
  }}
  let E=[];for(let a=0;a<N;a++){let ok=true;for(let F of T){let c=F[0][a]^F[0][0];for(let q=0;q<Q&&ok;q++)for(let x=0;x<N;x++)if((F[q][x]^F[q][x^a])!==c){ok=false;break}if(!ok)break}if(ok)E.push(a)}
  return {D,rho:rank(D),eta:d-Math.log2(E.length),aff};
 }
 let circuits=0,greedyRuns=0,gateChecks=0,fiberChecks=0,outputChecks=0,strictHybrid=0,strictCount=0,affineContexts=0,exact=0,strictLedger=0,controls=[];
 function check(C,tag=null){
  let {d,k,N,Q,g,out,off,evalAll,T,raw,active}=C;
  let {D,rho,eta,aff}=demands(T,N,Q,d),ell=rank(raw.flat()),lower=Math.ceil((rho+eta)/2),ledger=Math.ceil((rho+ell)/2);
  assert(rho<=eta&&eta<=ell&&ledger<=active,"hybrid inequalities");
  if(lower>Math.max(rho,Math.ceil(eta/2)))strictHybrid++;
  if(ledger>Math.max(rho,Math.ceil(ell/2)))strictLedger++;
  if(rho>Math.ceil(eta/2))strictCount++;
  if(active===lower)exact++;
  affineContexts+=aff;
  for(let mode=0;mode<3;mode++){
   let S=[],K=Array.from({length:N},(_,x)=>x),base=Array(Q).fill(0),outside=0;
   for(let i=0;i<g.length;i++){
    let options=raw[i].map((v,j)=>({v,j})).filter(({v})=>K.some(x=>par(x&v)));
    if(options.length){
     let op=options[mode===1?options.length-1:0];
     if(mode===2){let candidates=options.filter(({v})=>!span([...D,...S],v));if(candidates.length)op=candidates[0]}
     if(!span([...D,...S],op.v))outside++;
     let a=K.find(x=>par(x&op.v));
     for(let q=0;q<Q;q++)if(par(evalAll(base[q],q)&g[i][op.j]))base[q]^=a;
     K=K.filter(x=>!par(x&op.v));S.push(op.v);
    }
    assert(K.length===2**(d-S.length),"fiber dimension");
    for(let q=0;q<Q;q++){let w=evalAll(base[q],q);for(let x of K){let v=evalAll(base[q]^x,q);assert(((w^v)>>off&((1<<(i+1))-1))===0,"all reserved outputs query only");fiberChecks++}}
    gateChecks++;
   }
   for(let q=0;q<Q;q++)for(let j=0;j<out.length;j++)for(let x of K){assert((T[j][q][base[q]^x]^T[j][q][base[q]])===par((out[j]>>1)&(N-1)&x),"common slope");outputChecks++}
   assert(D.every(v=>span(S,v))&&S.length<=active,"terminal slope ledger");
   if(mode===2)assert(ell-rho<=2*outside&&outside===S.length-rho,"priority quotient");
   greedyRuns++;
  }
  circuits++;
  let r={d,k,gates:g.length,dataDependent:active,rho,eta,rawRank:ell,lower,ledger};
  if(tag)controls.push({tag,...r});
  return r;
 }
 // Random scalar and vector circuits.
 for(let z=0;z<220;z++){
  let d=1+rnd(5),k=1+rnd(3),n=1+rnd(6),off=1+d+k,g=[];
  for(let i=0;i<n;i++)g.push([rnd(1<<(off+i)),rnd(1<<(off+i))]);
  let out=Array.from({length:1+rnd(3)},()=>rnd(1<<(off+n)));
  check(circuit(d,k,g,out));
 }
 // Circuit builder. Every expression is affine in primaries and earlier gate outputs.
 function build(d,k){
  let g=[],off=1+d+k;
  const x=i=>1<<(1+i),q=i=>1<<(1+d+i),and=(a,b)=>{let v=1<<(off+g.length);g.push([a,b]);return v};
  function mux(M,start=0){let a=Array.from({length:M},(_,j)=>x(start+j));for(let i=0;a.length>1;i++){let b=[];for(let j=0;j<a.length;j+=2)b.push(a[j]^and(a[j]^a[j+1],q(i)));a=b}return a[0]}
  return {g,x,q,and,mux,done:o=>circuit(d,k,g,Array.isArray(o)?o:[o])}
 }
 for(let k=1;k<=3;k++){
  let M=1<<k,b=build(M,k),F=b.mux(M);let r=check(b.done(F),"lookup "+M);assert(r.lower===M-1&&r.rawRank===M-1&&r.gates===M-1,"lookup exact");
  b=build(M,k+1);F=b.and(b.mux(M),b.q(k));r=check(b.done(F),"enabled lookup "+M);assert(r.lower===M&&r.gates===M,"enabled lookup exact");
 }
 for(let k=1;k<=2;k++)for(let r=1;r<=2;r++){
  let M=1<<k,d=M+2*r+1,b=build(d,k+2),F=b.and(b.mux(M),b.q(k)),H=b.x(M);
  for(let i=0;i<r;i++)H^=b.and(b.x(M+1+2*i),b.x(M+2+2*i));
  F^=b.and(H,b.q(k+1));
  let v=check(b.done(F),"hybrid M="+M+" r="+r);assert(v.rho===M&&v.eta===d&&v.lower===M+r+1&&v.gates===v.lower,"hybrid exact");
 }
 // Shared-witness circuit, all row/column choices, singleton and empty affine residuals.
 for(let [m,l] of [[1,2],[2,1],[2,2],[2,3]]){
  let d=m*l,b=build(d,m+l),F=0;
  for(let j=0;j<l;j++){
   let c=b.q(m+j);
   for(let i=0;i<m;i++)c=b.and(c,1^b.and(b.q(i),1^b.x(i*l+j)));
   F=F^c^b.and(F,c);
  }
  let C=b.done(F);
  for(let q=0;q<C.Q;q++)for(let x=0;x<C.N;x++){
   let truth=0;for(let j=0;j<l;j++)if(q>>(m+j)&1){let ok=1;for(let i=0;i<m;i++)if((q>>i&1)&&!(x>>(i*l+j)&1))ok=0;truth|=ok}
   assert(C.T[0][q][x]===truth,"witness semantics")
  }
  let v=check(C,"shared witness "+m+"x"+l);assert(v.rho===d&&v.eta===d&&v.lower===d,"witness affine slopes");
 }
 return {seed:870041,circuits,greedyRuns,gateChecks,fiberChecks,outputChecks,affineContexts,strictHybrid,strictLedger,strictCount,exact,controls};
}
console.log(JSON.stringify(replay(),null,2));

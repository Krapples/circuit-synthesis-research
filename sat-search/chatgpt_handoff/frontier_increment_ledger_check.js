"use strict";
// Exact per-gate frontier accounting and selector/dictionary order controls.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};let seed=870056;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function build(d,q){let g=[],next=d+q+1;const and=(a,b)=>{assert((a>>1)!==(b>>1),"proper");let i=next++;g.push({i,a,b});return i*2},or=(a,b)=>and(a^1,b^1)^1,mux=(s,a,b)=>or(and(s^1,a),and(s,b));return {g,and,or,mux,x:i=>2*(i+1),q:i=>2*(d+i+1),done:o=>({d,q,g,o})}}
 function ledger(C){let id=l=>l>>1,live=new Set([id(C.o)]);for(let i=C.g.length-1;i>=0;i--)if(live.has(C.g[i].i)){live.add(id(C.g[i].a));live.add(id(C.g[i].b))}let G=C.g.filter(v=>live.has(v.i)),A=new Map,uses=new Map,seen=new Set,qseen=new Set;
  for(let i=1;i<=C.d+C.q;i++)A.set(i,i<=C.d&&live.has(i));
  for(let g of G){A.set(g.i,A.get(id(g.a))||A.get(id(g.b)));for(let i of [id(g.a),id(g.b)])uses.set(i,(uses.get(i)||0)+1)}
  uses.set(id(C.o),(uses.get(id(C.o))||0)+1);
  let d=Array.from({length:C.d},(_,i)=>i+1).filter(i=>live.has(i)).length,front=new Set(Array.from({length:C.d},(_,i)=>i+1).filter(i=>live.has(i))),B=0,Q=0,e=0,stages=0,branch=0,metadata=0,compress=0,expand=0,records=[{B,Q,e,c:d,q:0}];
  for(let g of G){if(!A.get(g.i))continue;let prev=front.size,bq=0,be=0;for(let i of [id(g.a),id(g.b)]){if(!A.get(i)){Q++;bq++;qseen.add(i);continue}assert(front.has(i),"available data");let n=uses.get(i)-1;uses.set(i,n);if(!n)front.delete(i);else {e++;be++}}
   front.add(g.i);B++;let c=front.size;assert(B===d-c+Q+e,"exact prefix");assert(1===prev-c+bq+be,"increment");assert(bq<=1,"one metadata per gate");if(c<prev)compress++;if(c>prev)expand++;branch+=be;metadata+=bq;records.push({B,Q,e,c,q:qseen.size});stages++;
  }
  if(d){assert(front.size===1&&front.has(id(C.o)),"final frontier")}
  for(let j=1;j<records.length;j++){let i=rnd(j),u=records[i],v=records[j];assert(v.B-u.B===u.c-v.c+v.Q-u.Q+v.e-u.e&&v.B-u.B>=u.c-v.c+v.q-u.q,"interval");}
  return {stages,branch,metadata,compress,expand,records}
 }
 let totals={circuits:0,stages:0,branch:0,metadata:0,compress:0,expand:0};function record(C){let z=ledger(C);totals.circuits++;for(let k of ["stages","branch","metadata","compress","expand"])totals[k]+=z[k];return z.records}
 for(let z=0;z<1200;z++){let d=1+rnd(6),q=1+rnd(6),b=build(d,q),pool=Array.from({length:d+q},(_,i)=>2*(i+1)),n=1+rnd(20);for(let i=0;i<n;i++){let a=pool[rnd(pool.length)],c=pool[rnd(pool.length)];if(a===c){i--;continue}pool.push(b.and(a^rnd(2),c^rnd(2)))}record(b.done(pool[pool.length-1]^rnd(2)))}
 let controls=[];
 for(let ell=1;ell<=3;ell++)for(let k=1;k<=3;k++){
  let m=2**k,P=2**ell;
  for(let style=0;style<2;style++){
   let b=build(m*ell,P+k),x=Array.from({length:m},(_,j)=>Array.from({length:ell},(_,i)=>b.x(j*ell+i))),h=Array.from({length:P},(_,i)=>b.q(i)),s=Array.from({length:k},(_,i)=>b.q(P+i));
   const select=(v,a)=>{for(let t of a){let y=[];for(let i=0;i<v.length;i+=2)y.push(b.mux(t,v[i],v[i+1]));v=y}return v[0]};
   let ports,pre,o;if(style===0){ports=Array.from({length:ell},(_,i)=>select(x.map(v=>v[i]),s));pre=b.g.length;o=select(h,ports)}
   else{ports=x.map(v=>select(h,v));pre=b.g.length;o=select(ports,s)}
   let C=b.done(o),rows=record(C),r=rows[pre];assert(r.c===(style===0?ell:m),"frontier width");
   assert(r.q===(style===0?k:P),"frontier metadata");assert(r.B===3*(style===0?ell*(m-1):m*(P-1)),"prefix gates");
   controls.push({ell,m,style:style===0?"selector-first":"dictionary-first",width:r.c,ingress:r.q,prefixGates:r.B,total:C.g.length});
  }
 }
 return {seed:870056,...totals,controls};
}
console.log(JSON.stringify(replay(),null,2));

"use strict";
// Stable original-ID binary-gate elimination and ancestry matching regression.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870045;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const lit=(i,p=0)=>2*i+p,id=l=>l>>1,inv=l=>l^1;
 const gate=(tt,a,b)=>tt>>((a<<1)|b)&1;
 const proper=t=>[0,1].some(b=>gate(t,0,b)!==gate(t,1,b))&&[0,1].some(a=>gate(t,a,0)!==gate(t,a,1));
 const ts=Array.from({length:16},(_,i)=>i).filter(proper);
 function make(d,q){let g=[],next=d+q+1;return {d,q,g,add:(t,a,b)=>{let i=next++;g.push({i,t,a,b});return lit(i)},x:i=>lit(1+i),qv:i=>lit(1+d+i),done:o=>({d,q,g:g.slice(),o})}}
 function ev(C,x,q){let w=[0];for(let i=0;i<C.d;i++)w.push(x>>i&1);for(let i=0;i<C.q;i++)w.push(q>>i&1);const read=l=>(w[id(l)]||0)^(l&1);for(let {i,t,a,b} of C.g)w[i]=gate(t,read(a),read(b));return {out:read(C.o),read,w}}
 function simplify(C,fix=new Map,force=new Map){
  let alias=new Map([[0,0],...Array.from({length:C.d+C.q},(_,i)=>[i+1,fix.has(i+1)?fix.get(i+1):lit(i+1)])]),g=[];
  const get=l=>{let v=alias.get(id(l));assert(v!==undefined,"topological alias");return v^(l&1)};
  for(let {i,t,a,b} of C.g){if(force.has(i)){alias.set(i,force.get(i));continue}
   a=get(a);b=get(b);let vars=[...new Set([id(a),id(b)].filter(Boolean))],vals=[];
   for(let x=0;x<1<<vars.length;x++){let read=l=>((id(l)?(x>>vars.indexOf(id(l))&1):0)^(l&1));vals.push(gate(t,read(a),read(b)))}
   let r=null;if(vals.every(x=>x===vals[0]))r=vals[0];
   else for(let j=0;j<vars.length;j++)for(let p=0;p<2;p++)if(vals.every((v,x)=>v===((x>>j&1)^p)))r=lit(vars[j],p);
   if(r===null){assert(vars.length===2,"proper residual gate");g.push({i,t,a,b});r=lit(i)}
   alias.set(i,r)
  }
  let o=get(C.o),live=new Set([id(o)]);for(let k=g.length-1;k>=0;k--)if(live.has(g[k].i)){live.add(id(g[k].a));live.add(id(g[k].b))}
  return {...C,g:g.filter(v=>live.has(v.i)),o}
 }
 function ancestors(C,active){let S=new Map;for(let i=0;i<C.d;i++)S.set(i+1,active>>i&1?1<<i:0);
  let A=new Map;for(let g of C.g){let s=(S.get(id(g.a))||0)|(S.get(id(g.b))||0);S.set(g.i,s);A.set(g.i,s)}return A}
 function readers(C,i){return C.g.filter(g=>id(g.a)===i||id(g.b)===i)}
 function match(C,groups,active){let A=ancestors(C,active),tokens=[];for(let G of groups){let exempt=G[rnd(G.length)];for(let j of G){tokens.push(j);if(j!==exempt)tokens.push(j)}}
  let owner=new Map;
  function augment(k,seen){for(let [g,s] of A)if((s>>tokens[k]&1)&&!seen.has(g)){seen.add(g);if(!owner.has(g)||augment(owner.get(g),seen)){owner.set(g,k);return true}}return false}
  assert(tokens.every((_,k)=>augment(k,new Set)),"ancestry matching");
  return tokens.length
 }
 function build(groups,style,extra=0){let d=groups.reduce((s,m)=>s+m,0),Q=groups.reduce((s,m)=>s*m,1),b=make(d,style===2?groups.reduce((s,m)=>s+m,0):groups.reduce((s,m)=>s+Math.ceil(Math.log2(m)),0)),parts=[],start=0,qstart=0;
  for(let m of groups){
   if(style===2){let a=[];for(let j=0;j<m;j++)a.push(b.add(8,b.x(start+j),b.qv(qstart+j)));let f=a[0];for(let j=1;j<a.length;j++)f=b.add(14,f,a[j]);parts.push(f);qstart+=m}
   else{let a=Array.from({length:m},(_,j)=>b.x(start+j));let k=0;while(a.length>1){let next=[];for(let j=0;j<a.length;j+=2){let q=b.qv(qstart+k);if(style===0){let L=b.add(8,a[j],inv(q)),R=b.add(8,a[j+1],q);next.push(b.add(14,L,R))}else next.push(b.add(6,a[j],b.add(8,b.add(6,a[j],a[j+1]),q)))}a=next;k++}parts.push(a[0]);qstart+=k}
   start+=m
  }
  let o=parts[0];for(let i=1;i<parts.length;i++)o=b.add(8,o,parts[i]);
  // Add live, redundant pairs: (f XOR h) XOR h.
  for(let i=0;i<extra;i++){let h=rnd(2)?b.x(rnd(d)):b.qv(rnd(b.q));o=b.add(6,b.add(6,o,h),h)}
  let contexts=[];for(let z=0;z<Q;z++){let t=z,idx=[],q=0,off=0;for(let m of groups){let j=t%m;t=Math.floor(t/m);idx.push(j);if(style===2){q|=1<<(off+j);off+=m}else{q|=j<<off;off+=Math.ceil(Math.log2(m))}}contexts.push({q,idx})}
  return {C:b.done(o),contexts,groups}
 }
 function target(z,x,groups){let start=0,v=1;for(let i=0;i<groups.length;i++){v&=x>>(start+z.idx[i])&1;start+=groups[i]}return v}
 let instances=0,elims=0,oneReader=0,manyReader=0,parity=0,canalizing=0,truthChecks=0,stableCharges=0,matchingTokens=0,subsetChecks=0,baseChecks=0,minSurplus=Infinity;
 function run(B,order){
  let {C:orig,contexts:Y,groups}=B,C=simplify(orig),d=C.d,active=(1<<d)-1,used=new Set,initial=ancestors(C,active),start=0,labels=groups.map(m=>{let a=Array.from({length:m},(_,i)=>start+i);start+=m;return a});
  let count=A=>[...A.values()].filter(Boolean).length,base=count(initial),f=groups.length;
  assert(base>=2*d-f,"initial bound");
  matchingTokens+=match(C,labels,active);
  for(let S=1;S<1<<d;S++){let full=labels.filter(G=>G.every(j=>S>>j&1)).length;let have=[...initial.values()].filter(v=>v&S).length;assert(have>=2*pc(S)-full,"subset Hall");subsetChecks++}
  function pc(x){let n=0;while(x){x&=x-1;n++}return n}
  function verify(C,Y,active){for(let z of Y)for(let x=0;x<1<<d;x++)if(!(x&~active)){assert(ev(C,x,z.q).out===target(z,x,groups),"target");truthChecks++}}
  verify(C,Y,active);
  for(let x of order){
   let rs=readers(C,x+1);assert(rs.length>0,"essential bit");let before=C,A=ancestors(C,active),fix=new Map,force=new Map,rule=null;
   let keep=Y.filter(z=>{let j=labels.findIndex(G=>G.includes(x));return labels[j][z.idx[j]]!==x});
   assert(keep.length&&keep.some(z=>z.idx.some((v,j)=>active>>labels[j][v]&1&&labels[j][v]!==x)),"valid deletion");
   if(rs.length>=2){manyReader++;fix.set(x+1,0);rule=()=>0}
   else{oneReader++;let g=rs[0],side=id(g.a)===x+1?0:1,readx=side?g.b:g.a,h=side?g.a:g.b;
    assert(id(C.o)!==g.i,"reader not output");
    // Independently check a path from a surviving queried bit to output avoiding g.
    let reachable=new Set;let other=keep[0].idx.map((v,j)=>labels[j][v]).find(v=>v!==x);
    reachable.add(other+1);for(let n of C.g)if(n.i!==g.i&&(reachable.has(id(n.a))||reachable.has(id(n.b))))reachable.add(n.i);
    assert(reachable.has(id(C.o)),"dominator bypass");
    let val=null;for(let a=0;a<2;a++){let v=a^(readx&1);if((side?gate(g.t,0,v):gate(g.t,v,0))===(side?gate(g.t,1,v):gate(g.t,v,1)))val=a}
    if(val!==null){canalizing++;fix.set(x+1,val);rule=()=>val}
    else{parity++;assert(g.t===6||g.t===9,"noncanalizing binary");force.set(g.i,0);fix.set(x+1,0);rule=(y,q)=>{let v=ev(before,y,q).read(h);for(let a=0;a<2;a++){let u=a^(readx&1);if((side?gate(g.t,v,u):gate(g.t,u,v))===0)return a}throw Error("parity")}}
   }
   C=simplify(C,fix,force);let live=new Set(C.g.map(g=>g.i)),removed=before.g.filter(g=>!live.has(g.i)&&(A.get(g.i)>>x&1));
   assert(removed.length>=2,"two distinct gate removal");
   for(let g of removed.slice(0,2)){assert(!used.has(g.i)&&initial.get(g.i)>>x&1,"stable ancestor charge");used.add(g.i);stableCharges++}
   active&=~(1<<x);Y=keep;
   for(let z of Y)for(let y=0;y<1<<d;y++)if(!(y&~active)){let a=rule(y,z.q);assert(ev(before,y|(a<<x),z.q).out===ev(C,y,z.q).out,"substitution identity");truthChecks++}
   verify(C,Y,active);elims++
  }
  // Leave one group with two choices, all others with one.
  let core=groups.length+1;assert(pc(active)===core&&count(ancestors(C,active))>=core+1,"base bound");baseChecks++;
  minSurplus=Math.min(minSurplus,base-(2*d-f));instances++
 }
 for(let groups of [[2],[4],[8],[2,2],[4,2],[4,4],[2,2,2],[2,4,2]]){
  for(let style=0;style<3;style++)for(let rep=0;rep<4;rep++){
   let B=build(groups,style,rep),off=0,labels=groups.map(m=>{let a=Array.from({length:m},(_,i)=>off+i);off+=m;return a});
   let pivot=rnd(groups.length),order=[];for(let i=0;i<labels.length;i++){let G=labels[i].slice();while(G.length>(i===pivot?2:1)){let j=rnd(G.length);order.push(G[j]);G.splice(j,1)}}
   for(let i=order.length-1;i>0;i--){let j=rnd(i+1);[order[i],order[j]]=[order[j],order[i]]}run(B,order)
  }
 }
 // Arbitrary proper gate truth-table obstruction: if g(x,h(y)) recovers y for both x values, g cannot depend on x.
 let truthObstructions=0;
 for(let t of ts)for(let side=0;side<2;side++)for(let h=0;h<4;h++){
  let sets=[0,1].map(y=>new Set([0,1].map(x=>side?gate(t,h>>y&1,x):gate(t,x,h>>y&1))));
  assert([...sets[0]].some(v=>sets[1].has(v)),"dominator obstruction");truthObstructions++
 }
 return {seed:870045,properBinaryTruthTables:ts.length,truthObstructions,instances,elims,oneReader,manyReader,parity,canalizing,truthChecks,stableCharges,matchingTokens,subsetChecks,baseChecks,minSurplus}
}
console.log(JSON.stringify(replay(),null,2));

"use strict";
// Strict one-junk rewrite on double-star circuits with shared OR providers.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};let seed=870070;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n},pc=x=>{let n=0;for(;x;x&=x-1)n++;return n};
 let instances=0,semantic=0,shared=0,exclusive=0,minSaved=Infinity,otherCovered=0,profile=[];
 for(let z=0;z<700;z++){
  // Double star on disjoint A and B with universal a,b, plus C4-free
  // private leaves of other centres. Only add edges with no C4.
  let l=3+rnd(2),r=3+rnd(2),n=l+r,A=(1<<l)-1,B=((1<<r)-1)<<l,a=0,b=l,N=Array(n).fill(0),edges=[];
  function edge(i,j){N[i]|=1<<j;N[j]|=1<<i;edges.push((1<<i)|(1<<j))}
  for(let j=l;j<n;j++)edge(a,j);for(let i=1;i<l;i++)edge(i,b);
  let gates=[],sets=Array.from({length:n},(_,i)=>1<<i),cache=new Map(sets.map((s,i)=>[s,i])),next=n;
  function add(op,u,v){let id=next++;gates.push({id,op,u,v});sets[id]=op==="or"?sets[u]|sets[v]:0;return id}
  function disj(s){if(cache.has(s))return cache.get(s);let bits=Array.from({length:n},(_,i)=>i).filter(i=>s>>i&1),p=1+rnd(bits.length-1),L=0;for(let i=0;i<p;i++){let j=i+rnd(bits.length-i);[bits[i],bits[j]]=[bits[j],bits[i]];L|=1<<bits[i]}let u=disj(L),v=disj(s^L),g=add("or",u,v);cache.set(s,g);return g}
  // Existing stars may cover some leaves, but leave a private noncentral
  // edge on each of the two exposed stars. Build them before junk operands.
  let ra=1<<b,rb=1<<a;for(let j=l+1;j<n-1;j++)if(rnd(2))ra|=1<<j;for(let i=1;i<l-1;i++)if(rnd(2))rb|=1<<i;
  let other=[];if(rnd(2))other.push(add("and",a,disj(ra)));else ra=0;if(rnd(2))other.push(add("and",b,disj(rb)));else rb=0;
  let aa=disj(A),bb=disj(B),cc=disj((1<<a)|(1<<b)),J=add("and",aa,bb),K=add("and",J,cc),out=other.concat(K).reduce((x,y)=>add("or",x,y)),old=gates.slice();
  const gateBy=new Map(old.map(g=>[g.id,g]));
  function cone(root,S){if(root<n||S.has(root))return;S.add(root);let g=gateBy.get(root);cone(g.u,S);cone(g.v,S)}
  let protectedSet=new Set;for(let v of other)cone(v,protectedSet);
  let Acone=new Set;cone(aa,Acone);assert(!protectedSet.has(aa)&&!protectedSet.has(cc),"exclusive roots");
  let changed=new Map,removed=new Set([J,K,cc]),removedA=0,sharedA=0;
  function rewrite(id){if(id===a)return -1;if(id<n)return id;if(protectedSet.has(id)){if(sets[id]&(1<<a)){sharedA++;return -1}return id}if(changed.has(id))return changed.get(id);
   let g=gateBy.get(id);assert(g.op==="or"&&Acone.has(id),"exclusive OR");let u=rewrite(g.u),v=rewrite(g.v),w;if(u===-1||v===-1||u===v){w=u===-1?v:u;removed.add(id);removedA++}else{w=id;g.u=u;g.v=v}changed.set(id,w);return w}
  let newA=rewrite(aa);assert(newA>=0&&removedA>=1,"one OR saved");
  let h1=add("and",a,bb),h2=add("and",b,newA),h3=add("or",h1,h2);for(let g of gates)if(g.id!==h1&&g.id!==h2&&g.id!==h3){if(g.u===K)g.u=h3;if(g.v===K)g.v=h3}if(out===K)out=h3;
  let live=new Set,by=new Map(gates.filter(g=>!removed.has(g.id)).map(g=>[g.id,g]));function visit(id){if(id<n||live.has(id))return;let g=by.get(id);assert(g,"no dangling");live.add(id);visit(g.u);visit(g.v)}visit(out);
  function evalNew(x){let w=Array.from({length:n},(_,i)=>x>>i&1),memo=new Map;function f(id){if(id<n)return w[id];if(memo.has(id))return memo.get(id);let g=by.get(id),u=f(g.u),v=f(g.v),a=g.op==="and"?u&v:u|v;memo.set(id,a);return a}return f(out)}
  for(let x=0;x<1<<n;x++){let want=edges.some(e=>(x&e)===e);assert(evalNew(x)===Number(want),"strict rewrite exact full cube");semantic++}
  assert(live.size<old.length,"strict saving");minSaved=Math.min(minSaved,old.length-live.size);instances++;exclusive+=removedA;shared+=sharedA;if(ra||rb)otherCovered++;
 }
 return {seed:870070,instances,semantic,shared,exclusive,minSaved,otherCovered}
}
console.log(JSON.stringify(replay(),null,2));

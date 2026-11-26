"use strict";
// Exact common mixed factor-space rank and last-gate update.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870034;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const xor=(a,b)=>{let s=new Set(a);for(let v of b)s.has(v)?s.delete(v):s.add(v);return [...s]};
 const mul=(a,b)=>{let s=new Set;for(let u of a)for(let v of b){let w=u|v;s.has(w)?s.delete(w):s.add(w)}return [...s]};
 const sum=(m,g)=>g.reduce((p,h,i)=>m>>i&1?xor(p,h):p,[]);
 const bit=i=>1n<<BigInt(i);
 const rows=h=>{let a=new Map;for(let m of h)for(let i=(m-1)&m;i;i=(i-1)&m)a.set(i,(a.get(i)||0n)|bit(m^i));return a};
 const rank=vs=>{let p=new Map;for(let v of vs){while(v){let k=v&-v;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}}return p.size};
 const common=g=>g.flatMap(h=>[...rows(h).values()]);
 function choices(i){let n=1<<i,seen=new Set,cs=[[0,0]];for(let a=1;a<n;a++){cs.push([0,a]);for(let b=a+1;b<n;b++){let k=[a,b,a^b].sort((x,y)=>x-y).join(",");if(!seen.has(k)){seen.add(k);cs.push([a,b])}}}assert(cs.length===n+(n-1)*(n-2)/6,"subspace count");return cs}
 function study(t,limit=0){
  let max=0,best=null,count=0,scalarMax=0,violations=0,attained=0;
  function test(g,dep){let r=rank(common(g));if(r>max){max=r;best={dep,r}}if(r>2**(t+1)-2)violations++;if(r===2**(t+1)-2)attained++;if(limit){let s=rank(rows(sum((1<<(t-1))|rnd(1<<(t-1)),g)).values());assert(s<=r,"scalar in common");scalarMax=Math.max(scalarMax,s)}count++}
  function dfs(g,dep){let i=g.length;if(i===t){test(g,dep);return}for(let [a,b] of choices(i))dfs([...g,mul(xor([1<<(2*i)],sum(a,g)),xor([1<<(2*i+1)],sum(b,g)))],[...dep,[a,b]])}
  if(!limit){dfs([],[]);assert(count===Array.from({length:t},(_,i)=>choices(i).length).reduce((a,b)=>a*b,1),"complete count")}
  else for(let k=0;k<limit;k++){let g=[],dep=[];for(let i=0;i<t;i++){let a=rnd(1<<i),b=rnd(1<<i);g.push(mul(xor([1<<(2*i)],sum(a,g)),xor([1<<(2*i+1)],sum(b,g))));dep.push([a,b])}test(g,dep)}
  assert(!violations&&max===2**(t+1)-2,"observed bound");
  return {t,count,max,scalarMax,violations,attained,best,exhaustive:!limit}
 }
 const studies=[study(1),study(2),study(3),study(4),study(5),study(6,5000),study(7,1000)];
 // exact update via sparse active column kernel, all other indices have zero B and A except active A support.
 let checks=0,positive=0,localFailures=0,maxDelta=0,maxExample=null;
 function check(g,a,b){
  let i=g.length,U=sum(a,g),V=sum(b,g),A=rows(mul(U,V)),C=rows(U),D=rows(V);
  let cu=U.reduce((m,x)=>m|bit(x),0n),cv=V.reduce((m,x)=>m|bit(x),0n);
  for(let j of U)A.set(j,(A.get(j)||0n)^cv);
  for(let j of V)A.set(j,(A.get(j)||0n)^cu);
  let old=common(g),R=rank(old),n=1<<(2*i),active=new Set([...A.keys(),...C.keys(),...D.keys()]);
  let p=new Map,images=[],r=0;
  for(let j of active){
   let v=(C.get(j)||0n)|((D.get(j)||0n)<<BigInt(n)),w=A.get(j)||0n;
   while(v){let k=v&-v;if(p.has(k)){let [z,y]=p.get(k);v^=z;w^=y}else{p.set(k,[v,w]);r++;break}}
   if(!v)images.push(w)
  }
  let delta=rank([...old,...images])-R;
  let next=mul(xor([1<<(2*i)],U),xor([1<<(2*i+1)],V)),newR=rank(common([...g,next]));
  assert(newR===2+R+r+delta,"joint update");assert(r<=R,"prefix containment");
  if(!a||!b||a===b)assert(delta===0,"rank one residual");
  if(delta>0)positive++;if(newR>2*R+2)localFailures++;
  if(delta>maxDelta){maxDelta=delta;maxExample={i,a,b,R,r,delta,newR}}
  checks++;return {R,r,delta,newR}
 }
 for(let z=0;z<300;z++){
  let t=1+rnd(5),g=[];for(let i=0;i<t;i++)g.push(mul(xor([1<<(2*i)],sum(rnd(1<<i),g)),xor([1<<(2*i+1)],sum(rnd(1<<i),g))));
  check(g,rnd(1<<t),rnd(1<<t))
 }
 let fork=check([[3],[12]],1,2);assert(fork.R===4&&fork.r===4&&fork.delta===4&&fork.newR===14,"fork");
 return {seed:870034,studies,checks,positive,localFailures,maxDelta,maxExample,fork}
}
console.log(JSON.stringify(replay(),null,2));

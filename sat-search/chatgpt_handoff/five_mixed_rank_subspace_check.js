"use strict";
// Exact canonical dependency-subspace enumeration. Run node five_mixed_rank_subspace_check.js.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const xor=(a,b)=>{let s=new Set(a);for(let v of b)s.has(v)?s.delete(v):s.add(v);return [...s]};
 const mul=(a,b)=>{let s=new Set;for(let u of a)for(let v of b){let w=u|v;s.has(w)?s.delete(w):s.add(w)}return [...s]};
 function choices(i){let out=[[0,0]],n=1<<i,seen=new Set;for(let a=1;a<n;a++){out.push([0,a]);for(let b=a+1;b<n;b++){let key=[a,b,a^b].sort((x,y)=>x-y).join(",");if(!seen.has(key)){seen.add(key);out.push([a,b])}}}assert(out.length===n+(n-1)*(n-2)/6,"subspace count");return out}
 function enumerate(t){
  let N=1<<(2*t),bits=Array.from({length:N},(_,i)=>1n<<BigInt(i)),sets=Array.from({length:t},(_,i)=>choices(i));
  let count=0,max=0,best=null,hist={},classes={},directChecks=0,skipped=0;
  function rank(rows){let p=new Map;for(let v of rows){while(v){let k=v&-v;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}}return p.size}
  function coeffRank(h){let rows=new Map;for(let m of h)for(let i=(m-1)&m;i;i=(i-1)&m)rows.set(i,(rows.get(i)||0n)|bits[m^i]);return rank(rows.values())}
  function direct(h){let f=Uint8Array.from({length:N},(_,x)=>h.reduce((r,m)=>r^Number((x&m)===m),0)),rows=[];for(let u=0;u<N;u++){let v=0n;for(let q=0;q<N;q++)if(f[u^q]^f[u]^f[q]^f[0])v|=bits[q];rows.push(v)}return rank(rows)}
  function dfs(g,dep){
   let i=g.length;
   if(i===t){
    let cl=dep.map(([a,b])=>a===0?b===0?0:1:2).join("");
    let combos=[[]];for(let h of g)combos.push(...combos.map(p=>xor(p,h)));
    for(let out=1<<(t-1);out<1<<t;out++){
     let h=combos[out],r=coeffRank(h);assert(r%2===0,"alternating");count++;hist[r]=(hist[r]||0)+1;classes[cl]=Math.max(classes[cl]||0,r);
     if(r>max){max=r;best={dep,out,r,anf:h.slice().sort((a,b)=>a-b)}}
     if(t<=3||count%4093===0||count===1){assert(direct(h)===r,"direct rank");directChecks++}
    }
    skipped+=1<<(t-1);return;
   }
   let c=[[]];for(let h of g)c.push(...c.map(p=>xor(p,h)));
   for(let [a,b] of sets[i])dfs([...g,mul(xor([1<<(2*i)],c[a]),xor([1<<(2*i+1)],c[b]))],[...dep,[a,b]]);
  }
  dfs([],[]);let expected=sets.reduce((a,v)=>a*v.length,1)*(1<<(t-1));assert(count===expected&&skipped===expected,"complete coverage");
  assert(max===2**(t+1)-2,"conjecture check");
  return {t,subspaceCounts:sets.map(v=>v.length),count,skipped,maximum:max,best,hist,classes,directChecks}
 }
 return [1,2,3,4,5].map(enumerate)
}
console.log(JSON.stringify(replay(),null,2));

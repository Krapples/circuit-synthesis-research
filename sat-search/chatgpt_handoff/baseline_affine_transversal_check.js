"use strict";
// Exact small Rado min-max replay, not an implementation of matroid intersection.
function affineReplay(){
 let seed=870029;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const rank=vs=>{let p=new Map;for(let v of vs){while(v){let b=31-Math.clz32(v);if(p.has(b))v^=p.get(b);else{p.set(b,v);break}}}return p.size};
 const assert=(b,m)=>{if(!b)throw Error(m)};
 let instances=0,choices=0,subsets=0,deficits=0;
 for(let z=0;z<180;z++){
  const d=2+rnd(5),t=1+rnd(6),pairs=Array.from({length:t},()=>[rnd(1<<d),rnd(1<<d)]);
  if(z%3===0)for(let i=0;i<t-1;i++)pairs[i]=[1,1];
  let best=0;
  function dfs(i,v){if(i===t){best=Math.max(best,rank(v));choices++;return}dfs(i+1,v);dfs(i+1,[...v,pairs[i][0]]);dfs(i+1,[...v,pairs[i][1]])}
  dfs(0,[]);let dual=t;
  for(let m=0;m<(1<<t);m++){let v=[],n=0;for(let i=0;i<t;i++)if(m>>i&1){v.push(...pairs[i]);n++}dual=Math.min(dual,t-n+rank(v));subsets++}
  assert(best===dual,"Rado equality");
  if(best<Math.min(t,rank(pairs.flat())))deficits++;
  instances++;
 }
 return {seed:870029,instances,choices,subsets,strictDeficitsAgainstGateCountAndGlobalRank:deficits};
}
console.log(JSON.stringify(affineReplay(),null,2));

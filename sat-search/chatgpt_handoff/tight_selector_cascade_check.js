"use strict";
// Truth-table identities, constant-seed cascade counts, and tight selector controls.
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};
 let seed=870047;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const val=(t,a,b)=>t>>((a<<1)|b)&1,parity=t=>t===6||t===9;
 const proper=t=>[0,1].some(b=>val(t,0,b)!==val(t,1,b))&&[0,1].some(a=>val(t,a,0)!==val(t,a,1));
 const ts=Array.from({length:16},(_,i)=>i).filter(proper);
 function reads(g,i){return g.a===i||g.b===i}
 function mask(t,side,c){return [0,1].map(v=>side?val(t,v,c):val(t,c,v))}
 function ctrl(t,side){for(let c=0;c<2;c++){let m=mask(t,side,c);if(m[0]===m[1])return {c,v:m[0]}}return null}
 let canal=0,par=0,compose=0,reassoc=0;
 for(let t of ts)for(let side=0;side<2;side++){
  let c=ctrl(t,side);assert(!!c===!parity(t),"truth table dichotomy");
  if(c){canal++;for(let u of ts)for(let order=0;order<2;order++){let table=0;for(let x=0;x<2;x++)for(let y=0;y<2;y++){let g=side?val(t,y,x):val(t,x,y),v=order?val(u,g,x):val(u,x,g);table|=v<<((x<<1)|y)}for(let x=0;x<2;x++)for(let y=0;y<2;y++){let g=side?val(t,y,x):val(t,x,y);assert(val(table,x,y)===(order?val(u,g,x):val(u,x,g)),"two reader compose");compose++}}}
  else{par++;for(let u of [6,9])for(let x=0;x<2;x++)for(let a=0;a<2;a++)for(let b=0;b<2;b++){assert(val(u,val(t,x,a),b)===val(t,x,val(u,a,b)),"parity reassociation");reassoc++}}
 }
 // Test cascade edge count in DAGs where constant seeds are pairwise incomparable.
 let cascades=0,seedCount=0,extra=0,strict=0,largest=0,discard=0;
 for(let z=0;z<1800;z++){
  let k=1+rnd(6),d=k+2+rnd(3),n=2+rnd(16),g=[],pool=Array.from({length:d},(_,i)=>i+1);
  for(let i=0;i<n;i++){let a=pool[rnd(pool.length)],b=pool[rnd(pool.length)];if(a===b){i--;continue}let v=d+i+1;g.push({v,a,b});pool.push(v)}
  let out=pool[pool.length-1],live=new Set([out]);for(let i=g.length-1;i>=0;i--)if(live.has(g[i].v)){live.add(g[i].a);live.add(g[i].b)}
  g=g.filter(x=>live.has(x.v));let seeds=new Set(Array.from({length:k},(_,i)=>i+1).filter(i=>live.has(i)));
  if(!seeds.size){discard++;continue}
  let C=new Set(seeds),U=new Set;
  for(let {v,a,b} of g){let c=Number(C.has(a))+Number(C.has(b));if(c===2)C.add(v);else if(c===1)U.add(v)}
  if(C.has(out)){discard++;continue}
  let n0=C.size-seeds.size,U0=U.size,e=g.reduce((s,h)=>s+Number(C.has(h.a))+Number(C.has(h.b)),0);
  assert(e===2*n0+U0&&e>=C.size&&n0+U0>=seeds.size,"cascade edge count");
  cascades++;seedCount+=seeds.size;extra+=n0+U0;if(n0+U0>seeds.size)strict++;largest=Math.max(largest,n0+U0-seeds.size)
 }
 // Valid selector topologies at exact data budget with arbitrary query-only decoding.
 function analyze(d,q,g,o){
  let live=new Set([o]);for(let i=g.length-1;i>=0;i--)if(live.has(g[i].i)){live.add(g[i].a);live.add(g[i].b)}
  g=g.filter(x=>live.has(x.i));let anc=new Map;for(let i=1;i<=d+q;i++)anc.set(i,i<=d?1:0);for(let v of g)anc.set(v.i,anc.get(v.a)|anc.get(v.b));
  let data=g.filter(v=>anc.get(v.i)),found=new Set;
  for(let w=0;w<1<<q;w++){
   let f=0;for(let x=0;x<1<<d;x++){let a=[0];for(let i=0;i<d;i++)a.push(x>>i&1);for(let i=0;i<q;i++)a.push(w>>i&1);for(let v of g)a[v.i]=val(v.t,a[v.a],a[v.b]);f|=a[o]<<x}
   for(let i=0;i<d;i++){let h=0;for(let x=0;x<1<<d;x++)h|=(x>>i&1)<<x;if(h===f)found.add(i)}
  }
  if(found.size!==d)return null;
  assert(data.length>=2*d-1,"valid selector lower");if(data.length!==2*d-1)return {tight:false};
  let one=0,two=0,branch=0;for(let i=1;i<=d;i++){let R=data.filter(v=>reads(v,i));assert(R.length===1||R.length===2,"tight readers");
   if(R.length===2){assert(R.every(v=>parity(v.t)),"double parity");two++}
   else{one++;let a=R[0],r=data.filter(v=>reads(v,a.i));assert(r.length===1&&!parity(a.t),"sole canal");
    let h=a.a===i?a.b:a.a;if(h<=d)throw Error("sole other raw data");
    if(anc.get(h)){assert(data.filter(v=>reads(v,h)).length>=2,"branch side operand");branch++}
    let c=ctrl(a.t,a.a===i?0:1);assert(c,"canal");
    let f=r[0],side=f.a===a.i?0:1,cc=ctrl(f.t,side);assert(!cc||cc.c!==c.v,"no controlling cascade")
   }
  }
  return {tight:true,one,two,branch}
 }
 let valid=0,tight=0,ones=0,twos=0,branches=0,planted=0,random=0;
 function record(r){if(r){valid++;if(r.tight){tight++;ones+=r.one;twos+=r.two;branches+=r.branch}}}
 for(let z=0;z<180;z++){
  let d=3+rnd(2),q=d,g=[],pool=[],next=d+q+1,phase=[];
  for(let i=0;i<d;i++){let p=rnd(2);phase.push(p);g.push({i:next,a:i+1,b:d+i+1,t:p?7:8});pool.push([next++,p])}
  while(pool.length>1){let a=pool.splice(rnd(pool.length),1)[0],b=pool.splice(rnd(pool.length),1)[0],p=pool.length?rnd(2):0,t=0;for(let i=0;i<2;i++)for(let j=0;j<2;j++)t|=(((i^a[1])|(j^b[1]))^p)<<((i<<1)|j);g.push({i:next,a:a[0],b:b[0],t});pool.push([next++,p])}
  let r=analyze(d,q,g,pool[0][0]);assert(r&&r.tight,"planted");record(r);planted++;
  // Local truth table mutations preserve or destroy selector property; only check when all residuals present.
  for(let j=0;j<12;j++){let c=g.map(x=>({...x}));c[rnd(c.length)].t=ts[rnd(ts.length)];record(analyze(d,q,c,pool[0][0]))}
 }
 for(let z=0;z<2500;z++){
  let d=3,q=3,g=[],pool=Array.from({length:d+q},(_,i)=>i+1);
  for(let i=0;i<5;i++){let a=pool[rnd(pool.length)],b=pool[rnd(pool.length)];if(a===b){i--;continue}let v=d+q+i+1;g.push({i:v,a,b,t:ts[rnd(ts.length)]});pool.push(v)}
  record(analyze(d,q,g,pool[pool.length-1]));random++;
 }
 return {seed:870047,canal,par,compose,reassoc,cascades,seedCount,extra,strict,largest,discard,planted,random,mutations:2160,valid,tight,ones,twos,branches}
}
console.log(JSON.stringify(replay(),null,2));

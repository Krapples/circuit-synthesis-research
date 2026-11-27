"use strict";
// Exact signed reader/merge-tree and decoder controls.
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};
 const val=(t,a,b)=>t>>((a<<1)|b)&1;
 const proper=t=>[0,1].some(b=>val(t,0,b)!==val(t,1,b))&&[0,1].some(a=>val(t,a,0)!==val(t,a,1));
 const ts=Array.from({length:16},(_,i)=>i).filter(proper),can=ts.filter(t=>t!==6&&t!==9);
 let seed=870049;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const ctl=(t,side)=>{for(let c=0;c<2;c++)if((side?val(t,0,c):val(t,c,0))===(side?val(t,1,c):val(t,c,1)))return c;return -1};
 // Saturated branch local obstruction: v parity in last data bit, sole canalizing reader of x.
 let saturatedCases=0;
 for(let p of [6,9])for(let t of can)for(let side=0;side<2;side++)for(let q=0;q<2;q++){
  assert([0,1].some(z=>{let v=val(p,z,q);return (side?val(t,v,0):val(t,0,v))===(side?val(t,v,1):val(t,1,v))}),"disabled data reader");saturatedCases++
 }
 // Reader/merge trees, each q port independently assignable. An allowed query
 // is any port vector giving exactly one raw data projection.
 function inspect(d,leaf,merges,root){
  let full=(1<<(1<<d))-1,proj=Array.from({length:d},(_,i)=>{let r=0;for(let x=0;x<1<<d;x++)r|=(x>>i&1)<<x;return r});
  const op=(t,a,b)=>((t&1?~a&~b:0)|(t&2?~a&b:0)|(t&4?a&~b:0)|(t&8?a&b:0))&full;
  let contexts=Array.from({length:d},()=>[]),n=d+merges.length;
  for(let q=0;q<1<<d;q++){
   let w=leaf.map((t,i)=>op(t,proj[i],q>>i&1?full:0));for(let m of merges)w.push(op(m.t,w[m.a],w[m.b]));
   let i=proj.indexOf(w[root]);if(i>=0)contexts[i].push(q)
  }
  if(contexts.some(a=>!a.length))return null;
  let c=ctl(leaf[0],0);assert(leaf.every(t=>ctl(t,0)===c),"common data control");
  let base=leaf.map(t=>val(t,c,0)),active=leaf.map(t=>ctl(t,1)^1);
  for(let i=0;i<d;i++)for(let q of contexts[i])for(let j=0;j<d;j++)assert(Number((q>>j&1)===active[j])===Number(i===j),"one hot decoder");
  for(let {t,a,b} of merges){let v=val(t,base[a],base[b]);assert(val(t,base[a]^1,base[b])===(v^1)&&val(t,base[a],base[b]^1)===(v^1),"signed OR/XOR merge");base.push(v)}
  assert(base[root]===c,"output phase");
  return {contexts:contexts.reduce((a,b)=>a+b.length,0),c}
 }
 let exhaustive=0,valid=0,onehotContexts=0,phase0=0,phase1=0;
 for(let t of can)for(let u of can)for(let v of can)for(let a of ts)for(let b of ts){
  let r=inspect(3,[t,u,v],[{t:a,a:0,b:1},{t:b,a:3,b:2}],4);exhaustive++;if(r){valid++;onehotContexts+=r.contexts;if(r.c)phase1++;else phase0++}
 }
 let sampled=0,planted=0,validSample=0,validMutants=0;
 for(let z=0;z<1800;z++){
  let d=4,leaf=Array.from({length:d},()=>can[rnd(can.length)]),pool=[0,1,2,3],merges=[];
  while(pool.length>1){let a=pool.splice(rnd(pool.length),1)[0],b=pool.splice(rnd(pool.length),1)[0];merges.push({a,b,t:ts[rnd(ts.length)]});pool.push(d+merges.length-1)}
  if(inspect(d,leaf,merges,pool[0]))validSample++;sampled++
 }
 // Random signed one-hot trees: use OR/XOR in deviation variables.
 for(let z=0;z<600;z++){
  let d=3+rnd(2),c=rnd(2),base=[],leaf=[];
  for(let i=0;i<d;i++){let p=rnd(2),e=rnd(2),t=0;for(let a=0;a<2;a++)for(let b=0;b<2;b++)t|=(p^((a^c)&Number(b===e)))<<((a<<1)|b);leaf.push(t);base.push(p)}
  let pool=Array.from({length:d},(_,i)=>i),merges=[];
  while(pool.length>1){let a=pool.splice(rnd(pool.length),1)[0],b=pool.splice(rnd(pool.length),1)[0],p=pool.length?rnd(2):c,tt=rnd(2)?6:14,t=0;
   for(let x=0;x<2;x++)for(let y=0;y<2;y++)t|=(p^val(tt,x^base[a],y^base[b]))<<((x<<1)|y);
   merges.push({a,b,t});base.push(p);pool.push(d+merges.length-1)}
  assert(inspect(d,leaf,merges,pool[0]),"planted");planted++;
  for(let j=0;j<4;j++){let l=leaf.slice(),m=merges.map(a=>({...a})),i=rnd(l.length+m.length);if(i<l.length)l[i]=can[rnd(can.length)];else m[i-l.length].t=ts[rnd(ts.length)];if(inspect(d,l,m,pool[0]))validMutants++}
 }
 // Actual binary address minterms: each one unique modulo complement and
 // unlike any primary (k>=2); support is all k bits.
 let decoderChecks=0,decoder=[];
 for(let k=2;k<=10;k++){
  let M=2**k,mask=(1n<<BigInt(M))-1n,seen=new Set,prim=Array.from({length:k},(_,i)=>{let h=0n;for(let q=0;q<M;q++)if(q>>i&1)h|=1n<<BigInt(q);return h});
  for(let i=0;i<M;i++){let h=1n<<BigInt(i),key=(h<(h^mask)?h:h^mask).toString();assert(!seen.has(key)&&prim.every(p=>p!==h&&(p^mask)!==h),"distinct minterm ports");seen.add(key);for(let j=0;j<k;j++){assert(((h>>BigInt(i)&1n)^(h>>BigInt(i^(1<<j))&1n))===1n,"essential address");decoderChecks++}}
  decoder.push({k,M,data:2*M-1,queryLower:M+k-2,totalAtTight:3*M+k-3,muxTree:3*M-3})
 }
 return {seed:870049,saturatedCases,exhaustive,valid,phase0,phase1,onehotContexts,sampled,validSample,planted,mutations:2400,validMutants,decoderChecks,decoder};
}
console.log(JSON.stringify(replay(),null,2));

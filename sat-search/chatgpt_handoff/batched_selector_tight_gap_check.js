"use strict";
// Exhaustive truth-table controls for the forced six-gate topology, slot equations, and upper construction.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};
 const val=(t,a,b)=>t>>((a<<1)|b)&1;
 const ts=Array.from({length:16},(_,i)=>i).filter(t=>[0,1].some(b=>val(t,0,b)!==val(t,1,b))&&[0,1].some(a=>val(t,a,0)!==val(t,a,1)));
 const can=ts.filter(t=>t!==6&&t!==9);
 const F=65535;
 const X=Array.from({length:4},(_,i)=>Array.from({length:16},(_,x)=>((x>>i)&1)<<x).reduce((a,b)=>a|b,0));
 function op(t,a,b){return ((t&1?~a&~b:0)|(t&2?~a&b:0)|(t&4?a&~b:0)|(t&8?a&b:0))&F}
 // The forced tight shape: v=merge(h2(x2,q0),h3(x3,q1)),
 // output=merge(g0(x0,v),g1(x1,v)). X0,X1 are saturated group.
 const targetSame=[X[0]&X[2],X[0]&X[3],X[1]&X[2],X[1]&X[3]];
 const targetCross=[X[0]&X[1],X[0]&X[3],X[2]&X[1],X[2]&X[3]];
 let assignments=0,contexts=0,maxSame=0,maxCross=0,sameHistogram=[0,0,0,0,0],crossHistogram=[0,0,0,0,0];
 for(let a of can)for(let b of can)for(let c of can)for(let d of can)for(let v of ts)for(let h of ts){
  let seen=new Set;
  for(let q=0;q<4;q++){
   let z=op(v,op(c,X[2],q&1?F:0),op(d,X[3],q&2?F:0));
   seen.add(op(h,op(a,X[0],z),op(b,X[1],z)));contexts++;
  }
  let s=targetSame.filter(x=>seen.has(x)).length,t=targetCross.filter(x=>seen.has(x)).length;
  sameHistogram[s]++;crossHistogram[t]++;maxSame=Math.max(s,maxSame);maxCross=Math.max(t,maxCross);
  assert(s<4&&t<4,"tight forced topology impossible");assignments++;
 }
 // Slot identities under equality, all two-entry groups.
 let slot=[];
 for(let r=2;r<=24;r++){
  let valid=[];
  for(let b=0;b<=2*r;b++)for(let Q=r;Q<=r+1;Q++)for(let e=0;e<=r+1;e++)for(let H=r-1;H<=e;H++)if(b+Q+e===r+1)valid.push({b,Q,e,H});
  assert(r===2?valid.length===1&&valid[0].b===0&&valid[0].Q===2&&valid[0].e===1&&valid[0].H===1:!valid.length,"tight slots");
  slot.push({r,valid:valid.length});
 }
 // Distinct residuals when restricting the interface to one bit.
 let residualChecks=0,layouts=[];
 for(let pair of [[0,1],[0,2]]){
  let comp=[0,1,2,3].filter(i=>!pair.includes(i)),rows=new Set;
  for(let c=0;c<4;c++)for(let i=0;i<2;i++)for(let j=2;j<4;j++){
   let y=0;for(let k=0;k<4;k++){let a=0;for(let p=0;p<2;p++){a|=(k>>p&1)<<pair[p];a|=(c>>p&1)<<comp[p]}y|=((a>>i&1)&(a>>j&1))<<k;residualChecks++}
   rows.add(y)
  }
  assert(rows.size>2,"one-bit interface");
  layouts.push({pair,residuals:[...rows].sort((a,b)=>a-b)})
 }
 // Seven gate upper for two two-entry groups, six free signed data gates + AND.
 let upperChecks=0;
 for(let x=0;x<16;x++)for(let q=0;q<4;q++){
  let a=q&1,b=q>>1,g0=(x&1)&(a^1),g1=(x>>1&1)&a,g2=g0|g1;
  let g3=(x>>2&1)&(b^1),g4=(x>>3&1)&b,g5=g3|g4,g6=g2&g5;
  assert(g6===((x>>a&1)&(x>>(2+b)&1)),"upper construction");upperChecks++
 }
 return {properTables:ts.length,canalizingTables:can.length,assignments,contexts,maxSame,maxCross,sameHistogram,crossHistogram,slot,residualChecks,layouts,upperChecks}
}
console.log(JSON.stringify(replay(),null,2));

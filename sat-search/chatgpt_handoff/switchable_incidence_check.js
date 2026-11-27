"use strict";
// Exact paired CNF grammar and independent DPLL replay of switchable incidence.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};
 let seed=870050;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function layout(m,l){
  let P=2**l,D=3*m,Q=1;while(Q<(D+2)*P+D+1)Q*=2;
  let w=Q.toString(2).length,base=Q+(D+2)*P,mode=base+D;
  const z=i=>base+i,ID=(t,x)=>Q+t*P+x;
  return {m,l,P,D,Q,w,mode,z,ID}
 }
 function encode(L,h,unitMode,tag,sign,payload){
  let bits=[],pos=[],modePos=-1;
  const lit=(v,s)=>{assert(v.toString(2).length===L.w,"width");bits.push(1,s);for(let j=0;j<L.w;j++)bits.push(1,(v>>j)&1);bits.push(0,1)};
  const clause=(A)=>{for(let [v,s] of A)lit(v,s);bits.push(0,0)};
  for(let p=0;p<L.P;p++)clause([[L.ID(0,p),h[p]]]);
  for(let p=0;p<L.P;p+=2){let a=L.ID(1,p),b=L.ID(1,p+1);clause([[a,1],[b,1]]);clause([[a,0],[b,0]])}
  modePos=bits.length+1;clause([[L.mode,unitMode]]);
  for(let j=0;j<L.m;j++){
   let g=3*j;clause([[L.z(g),1],[L.z(g+1),1],[L.z(g+2),1]]);
   for(let i=g;i<g+3;i++){
    clause([[L.mode,0],[L.z(i),1]]);
    lit(L.z(i),0);pos[i]=Array.from({length:L.l},(_,k)=>bits.length+3+2*k);
    lit(L.ID(tag[i],payload[i]),sign[i]);bits.push(0,0);
   }
  }
  let A=2*L.w+4;assert(bits.length===(3*L.P+15*L.m+1)*A+2*(2*L.P+7*L.m+1),"length formula");
  return {bits,pos,modePos}
 }
 function parse(bits){
  let C=[],c=[],i=0;
  while(i<bits.length){
   if(bits[i]===0){assert(bits[i+1]===0&&c.length>0,"clause end");C.push(c);c=[];i+=2;continue}
   let s=bits[i+1],v=0,p=1;i+=2;
   while(bits[i]===1){v+=p*bits[i+1];p*=2;i+=2}
   assert(bits[i]===0&&bits[i+1]===1&&p>1&&(v>=p/2),"literal end");i+=2;c.push([v,s])
  }
  assert(c.length===0,"complete");return C
 }
 function sat(C){ // Independent DPLL on parsed clauses; no gadget simplification.
  function go(C){
   while(true){
    if(C.some(c=>c.length===0))return false;if(!C.length)return true;
    let u=C.find(c=>c.length===1);if(!u)break;
    let [v,s]=u[0];C=C.filter(c=>!c.some(([a,b])=>a===v&&b===s)).map(c=>c.filter(([a])=>a!==v))
   }
   let [v]=C.reduce((a,b)=>a.length<=b.length?a:b)[0];
   return [0,1].some(s=>go([...C,[[v,s]]]))
  }
  return go(C)
 }
 function direct(L,h,mode,t,s,p){
  // Exact semantic model independent of the guards; enumerate used witness variables,
  // with tag1 complement pairs represented by one Boolean bit each.
  let keys=new Map;
  for(let i=0;i<L.D;i++){if(!t[i])continue;let k=t[i]===1?"w"+(p[i]>>1):t[i]+":"+p[i];if(!keys.has(k))keys.set(k,keys.size)}
  for(let x=0;x<2**keys.size;x++){
   let vals=p.map((v,i)=>{let k=t[i]===1?"w"+(v>>1):t[i]+":"+v;let a=!t[i]?h[v]:(x>>keys.get(k)&1)^(t[i]===1?v&1:0);return a===s[i]});
   if(mode?vals.every(Boolean):Array.from({length:L.m},(_,i)=>vals.slice(3*i,3*i+3).some(Boolean)).every(Boolean))return true
  }return false
 }
 let words=0,semanticChecks=0,positionChecks=0,stableLayouts=0,flips=0,hardChecks=0,selectors=0,essential=0,coreChecks=0,satCount=[0,0],mixedMetadata=0,maxLength=0;
 function check(L,h,mode,t,s,p,expected=null){
  let W=encode(L,h,mode,t,s,p),a=sat(parse(W.bits)),b=direct(L,h,mode,t,s,p);assert(a===b&&(expected===null||expected===a),"semantic");
  for(let i=0;i<L.D;i++)for(let j=0;j<L.l;j++){assert(W.bits[W.pos[i][j]]===(p[i]>>j&1),"position");positionChecks++}
  assert(W.bits[W.modePos]===mode,"mode position");maxLength=Math.max(maxLength,W.bits.length);words++;semanticChecks++;if(a)satCount[mode]++;
  return W
 }
 for(let m of [1,2,3,4])for(let l of [1,2,3]){
  let L=layout(m,l),ref=null;
  for(let r=0;r<60;r++){
   let h=Array.from({length:L.P},()=>rnd(2)),p=Array.from({length:L.D},()=>rnd(L.P)),t=Array.from({length:L.D},()=>rnd(5)),s=Array.from({length:L.D},()=>rnd(2)),mode=rnd(2);
   let W=check(L,h,mode,t,s,p);if(ref)assert(JSON.stringify(ref)===JSON.stringify(W.pos),"layout invariant");else ref=W.pos;stableLayouts++;mixedMetadata++;
   let i=rnd(L.D),j=rnd(l),p1=p.slice();p1[i]^=1<<j;let V=encode(L,h,mode,t,s,p1);
   assert(W.bits.every((b,k)=>b===V.bits[k]||k===W.pos[i][j])&&W.bits[W.pos[i][j]]!==V.bits[W.pos[i][j]],"single copy mutation");flips++;
  }
  // Fixed metadata hard incidence: all positive literals from tag1.
  let h=Array(L.P).fill(0),t=Array(L.D).fill(1),s=Array(L.D).fill(1);
  for(let r=0;r<60;r++){
   let p=Array.from({length:L.D},()=>rnd(L.P));let wanted=false;
   for(let x=0;x<2**(L.P/2);x++)if(Array.from({length:m},(_,i)=>p.slice(3*i,3*i+3).some(v=>(x>>(v>>1)&1)^(v&1))).every(Boolean)){wanted=true;break}
   check(L,h,0,t,s,p,wanted);hardChecks++;
  }
  // Every hard incidence input bit essential when >=2 groups.
  if(m>=2)for(let i=0;i<L.D;i++)for(let j=0;j<l;j++){
   let g=Math.floor(i/3),other=(g+1)%m,p=Array.from({length:L.D},(_,i)=>i%3===1?1:0);
   for(let a=0;a<3;a++){p[3*g+a]=0;p[3*other+a]=1}
   check(L,h,0,t,s,p,false);p[i]^=1<<j;check(L,h,0,t,s,p,true);essential++;
  }
  // unit mode: all slots arbitrary free patterns; activate one dictionary literal.
  for(let i=0;i<L.D;i++)for(let j=0;j<l;j++)for(let phase of [0,1]){
   let h=Array.from({length:L.P},(_,p)=>p>>j&1),t=Array.from({length:L.D},(_,a)=>a+2),s=Array(L.D).fill(1);t[i]=0;s[i]=phase;
   for(let b of [0,1]){let p=Array.from({length:L.D},()=>rnd(L.P));p[i]=(p[i]&~(1<<j))|(b<<j);check(L,h,1,t,s,p,b===phase);selectors++}
  }
  // Existential core on selected complete groups, unused groups independent
  // via fresh positive tag namespaces; mutate every outside payload freely.
  if(m>=2)for(let r=0;r<16;r++){
   let g=rnd(m),p=Array.from({length:L.D},()=>rnd(L.P)),t=Array.from({length:L.D},(_,i)=>Math.floor(i/3)===g?1:i+2),s=Array(L.D).fill(1);
   let W=check(L,Array(L.P).fill(0),0,t,s,p,true);for(let i=0;i<L.D;i++)if(Math.floor(i/3)!==g)p[i]=rnd(L.P);check(L,Array(L.P).fill(0),0,t,s,p,true);coreChecks++;
  }
 }
 // Explicit nontrivial negative hard core with bypassed groups.
 let L=layout(4,2),p=[0,0,0,1,1,1,2,3,0,2,1,3],t=Array.from({length:L.D},(_,i)=>i<6?1:i+2),s=Array(L.D).fill(1);
 for(let r=0;r<32;r++){for(let i=6;i<L.D;i++)p[i]=rnd(L.P);check(L,Array(L.P).fill(0),0,t,s,p,false);coreChecks++}
 return {seed:870050,words,semanticChecks,positionChecks,stableLayouts,flips,hardChecks,selectors,essential,coreChecks,mixedMetadata,satCount,maxLength}
}
console.log(JSON.stringify(replay(),null,2));

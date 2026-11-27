"use strict";
// Exact cell partition product and mixed selector ingress tradeoff.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};let seed=870055;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const clog=x=>x<=1?0:Math.ceil(Math.log2(x)-1e-10);
 let cases=0,cells=0,partitionChecks=0,outputChecks=0,thresholdChecks=0,strict=0,mixed=0,rawChecks=0,controls=[];
 function test(P,m,A,label){
  let H=1<<P,sets=new Map,qmax=0;
  for(let h=0;h<H;h++){let active=new Set;
   for(let j=0;j<m;j++){let a=A(h,j);active.add(a);if(!sets.has(a))sets.set(a,Array.from({length:m},()=>[]));sets.get(a)[j].push(h)}
   qmax=Math.max(qmax,active.size);
  }
  let q=clog(sets.size),qs=clog(qmax),capacity=0,records=[];
  for(let [a,S] of sets){
   let cls=[],r=[];
   for(let j=0;j<m;j++){
    let seen=new Map,v=[];for(let i=0;i<P;i++){let k=S[j].map(h=>h>>i&1).join("");if(!seen.has(k))seen.set(k,seen.size);v.push(seen.get(k))}
    cls.push(v);r.push(seen.size);assert(S[j].length<=2**seen.size,"cell size");partitionChecks++;
   }
   let prod=r.reduce((a,b)=>a*b,1);capacity=Math.max(capacity,prod);records.push({S,r});
   // Canonical mixed radix map realizes all outputs in this cell. Independently
   // verify its exact image and that no equal code has conflicting residual.
   let seen=new Map,images=new Set;
   for(let x=0;x<P**m;x++){
    let z=x,b=0,mul=1,values=[];for(let j=0;j<m;j++){let i=z%P;z=Math.floor(z/P);values.push(i);b+=mul*cls[j][i];mul*=r[j]}
    images.add(b);
    for(let j=0;j<m;j++)for(let h of S[j]){let k=b+":"+j+":"+h,v=h>>values[j]&1;if(seen.has(k))assert(seen.get(k)===v,"map decoder");else seen.set(k,v);outputChecks++}
   }
   assert(images.size===prod,"exact product classes");cells++;
  }
  let c=clog(capacity),old=Math.max(0,clog(1+m*(H-2)+1)-2**c),newFloor=0;
  for(let t=2;t<=P;t++){
   let high=Math.floor(c/Math.log2(t)+1e-10),L=m-2**qs*high;
   if(L>0){
    let low=0;for(let {S,r} of records)for(let j=0;j<m;j++)if(r[j]<t)low+=S[j].length;
    assert(low>=H*L&&low<=sets.size*m*2**(t-1),"threshold pair count");
    let v=Math.max(0,Math.ceil(P-t+1+Math.log2(L/m)-1e-10));assert(q>=v,"ingress floor");newFloor=Math.max(newFloor,v);thresholdChecks++;
   }
  }
  if(qs===0){assert(q>=P-Math.floor(2**(c/m)+1e-10),"selector-free ingress");newFloor=Math.max(newFloor,P-Math.floor(2**(c/m)+1e-10))}
  if(newFloor>old)strict++;if(qs>0)mixed++;cases++;
  return {label,P,m,q,qs,c,capacity,oldFloor:old,newFloor}
 }
 for(let P of [2,4,8])for(let m of [2,3]){
  controls.push(test(P,m,()=>0,"no ingress"));
  controls.push(test(P,m,(h,j)=>j,"selector first"));
  controls.push(test(P,m,h=>h,"dictionary first"));
  for(let k=0;k<=P;k++){
   let result=test(P,m,h=>h&((1<<k)-1),"raw bits "+k);
   let r=P-k+Math.min(2,k);assert(result.capacity===r**m,"raw exact width");rawChecks++;
  }
 }
 for(let z=0;z<140;z++){
  let P=z<100?4:8,m=2+rnd(P===4?3:2),a=1+rnd(5),b=1+rnd(3),table=Array.from({length:1<<P},()=>Array.from({length:m},()=>rnd(1<<b)));
  test(P,m,(h,j)=>((h&((1<<a)-1))<<b)|table[h][j],"mixed");
 }
 return {seed:870055,cases,cells,partitionChecks,outputChecks,thresholdChecks,strict,mixed,rawChecks,controls:controls.filter(x=>x.label==="no ingress"||x.label==="selector first"||x.label==="dictionary first"||x.label==="raw bits 2")}
}
console.log(JSON.stringify(replay(),null,2));

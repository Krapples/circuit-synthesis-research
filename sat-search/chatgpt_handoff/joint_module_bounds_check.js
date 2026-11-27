"use strict";
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};
 let seed=870036;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const xor=(a,b)=>{let S=new Set(a);for(let m of b)S.has(m)?S.delete(m):S.add(m);return [...S]};
 const mul=(a,b)=>{let S=new Set;for(let x of a)for(let y of b){let m=x|y;S.has(m)?S.delete(m):S.add(m)}return [...S]};
 const sum=(m,g)=>g.reduce((p,h,i)=>m>>i&1?xor(p,h):p,[]);
 const bit=i=>1n<<BigInt(i);
 function rows(h,mode){let M=new Map;for(let m of h)for(let i=m;;i=(i-1)&m){if(mode==="full"||mode==="diff"&&i||mode==="mix"&&i&&i!==m)M.set(i,(M.get(i)||0n)|bit(m^i));if(!i)break}return [...M.values()]}
 const rank=vs=>{let p=new Map;for(let v of vs){while(v){let k=v&-v;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}}return p.size};
 function diff(h,s){let a=new Set;for(let m of h){let x=m&s;for(let j=x;j;j=(j-1)&x){let v=m^j;a.has(v)?a.delete(v):a.add(v)}}return [...a]}
 function stats(g,s){let J=rank(g.flatMap(h=>rows(h,"mix"))),W=rank(g.flatMap(h=>rows(h,"full"))),D=rank(g.flatMap(h=>rows(h,"diff"))),B=rank([1n,...g.flatMap(h=>rows(diff(h,s),"full"))]);return {J,W,D,B,k:W-D}}
 const caps=[0,2,6,14,30,62];for(let t=6;t<=12;t++){let p=t-1,J=caps[p];caps.push(J+2*Math.floor((J+p+1)/2))}
 let samples=0,identity=0,zeroFresh=0,strictScalar=0,maxTop=0,topHist={},maxima={};
 for(let t=1;t<=7;t++)for(let z=0;z<120;z++){
  let g=[],dep=[];for(let i=0;i<t;i++){let a=rnd(1<<i),b=rnd(1<<i);dep.push([a,b]);g.push(mul(xor([1<<(2*i)],sum(a,g)),xor([1<<(2*i+1)],sum(b,g))))}
  let s=rnd(1<<(2*t)),v=stats(g,s);assert(v.D===v.J+1&&v.k<=t&&v.B<=Math.max(1,Math.floor(v.W/2)),"module bounds");assert(v.J<=caps[t],"universal recurrence cap");maxTop=Math.max(maxTop,v.k);topHist[v.k]=(topHist[v.k]||0)+1;maxima[t]=Math.max(maxima[t]||0,v.J);samples++;
  if(t<=4){let m=0;for(let i=1;i<1<<t;i++)m=Math.max(m,rank(rows(sum(i,g),"mix")));if(m<v.J)strictScalar++}
  if(t>=2){
   let f=g.slice(1).map(h=>h.filter(m=>!(m&3)).map(m=>m>>2)),shift=0;for(let i=1;i<t;i++){shift|=(dep[i][0]&1)<<(2*i-2);shift|=(dep[i][1]&1)<<(2*i-1)}
   let q=stats(f,shift);assert(v.J===q.J+2*q.B,"joint first gate");identity++;
   let dir=rnd(1<<(2*(t-1))),M=rank(f.flatMap(h=>rows(diff(h,dir),"full"))),LM=rank(f.flatMap(h=>rows(diff(diff(h,dir),shift),"full")));
   let actual=rank(g.flatMap(h=>rows(diff(h,dir<<2),"full")));assert(actual===M+2*LM&&2*LM<=M,"zero fresh directional");zeroFresh++;
  }
 }
 const g=[[3],[12,11],[48,19,35,3]],profile=stats(g,1),scalar=Array.from({length:8},(_,i)=>rank(rows(sum(i,g),"mix")));assert(profile.J===10&&Math.max(...scalar)===8,"joint scalar counterexample");
 return {seed:870036,samples,identity,zeroFresh,strictScalar,maxTop,topHist,maxima,caps,example:{g,profile,scalar}};
}
console.log(JSON.stringify(replay(),null,2));

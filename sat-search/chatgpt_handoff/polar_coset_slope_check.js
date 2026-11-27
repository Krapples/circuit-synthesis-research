"use strict";
// Exact coset-polar and complementary slope regression.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870044;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 const par=x=>pc(x)&1;
 function basis(vs){let p=new Map;for(let v of vs)while(v){let b=v&-v;if(p.has(b))v^=p.get(b);else{p.set(b,v);break}}return [...p.values()]}
 const rank=vs=>basis(vs).length;
 function spaces(n){let out=[];for(let d=0;d<=n;d++){function go(P,start){if(P.length===d){let mask=P.reduce((a,p)=>a|(1<<p),0),B=P.map(p=>1<<p);function fill(i){if(i===d){out.push(B.slice());return}let free=((1<<n)-1)^((1<<(P[i]+1))-1);free&=~mask;for(let s=free;;s=(s-1)&free){B[i]=(1<<P[i])|s;fill(i+1);if(!s)break}}fill(0);return}for(let p=start;p<=n-(d-P.length);p++)go(P.concat(p),p+1)}go([],0)}return out}
 function wedge(a,b,d){let p=0n;for(let i=0;i<d;i++)for(let j=i+1;j<d;j++)if(((a>>i&1)&(b>>j&1))^((a>>j&1)&(b>>i&1)))p|=1n<<BigInt(i*d+j);return p}
 let subspaces=0,eligible=0,rankChecks=0,slopeChecks=0,complementChecks=0,strict=0;
 for(let [m,n] of [[2,2],[2,3],[3,3]]){
  for(let B of spaces(m+n)){
   let d=B.length;if(d<=Math.max(m,n))continue;eligible++;
   let f=Array.from({length:m+n},(_,i)=>B.reduce((v,b,j)=>v|((b>>i&1)<<j),0)),U=f.slice(0,m),V=f.slice(m),u=rank(U.map(BigInt)),v=rank(V.map(BigInt)),h=u+v-d;
   let polars=U.flatMap(a=>V.map(b=>wedge(a,b,d))),nz=new Set(polars.map(String));
   let w=rank(polars),formula=u*v-h*(h+1)/2;
   assert(w===formula&&w>=d-1&&nz.size>=w,"wedge dimension");
   let support=[];for(let a of U)for(let b of V)if(wedge(a,b,d))support.push(BigInt(a),BigInt(b));
   assert(rank(support)===d,"full support");rankChecks++;
   for(let r=Math.ceil(d/2);r<d;r++)if(u>=d-r&&v>=d-r){assert(w>=r*(d-r),"balanced wedge bound");complementChecks++}
   // Explicitly vary the complementary query offset for each edge. Project onto ann U or ann V.
   for(let [X,Y] of [[U,V],[V,U]]){
    let K=Array.from({length:1<<d},(_,a)=>a).filter(a=>X.every(x=>!par(x&a))),W=basis(K.map(BigInt)).map(Number);
    let slopes=[];for(let a of X)for(let b of Y){
     let ca=rnd(2),cb=rnd(2);
     for(let z=0;z<1<<d;z++){
      let c=ca^par(a&z),e=cb^par(b&z),val=c&e,s=0;
      for(let j=0;j<W.length;j++)if(val^(c&(e^par(b&W[j]))))s|=1<<j;
      slopes.push(BigInt(s));
     }
    }
    assert(rank(slopes)===W.length,"kernel slope demand");slopeChecks++;
   }
   subspaces++;
  }
 }
 // Check arbitrary fixed lifted suffixes, even on a proper allowed subset of cosets.
 const xor=(a,b)=>{let s=new Set(a);for(let m of b)s.has(m)?s.delete(m):s.add(m);return [...s]};
 const mul=(a,b)=>{let s=new Set;for(let a0 of a)for(let b0 of b){let m=a0|b0;s.has(m)?s.delete(m):s.add(m)}return [...s]};
 const sum=(m,g)=>g.reduce((p,h,i)=>m>>i&1?xor(p,h):p,[]);
 const affine=(a,c,d)=>[...(c?[0]:[]),...Array.from({length:d},(_,i)=>1<<i).filter(v=>v&a)];
 let suffixes=0,offsets=0,quadratic=0,topChecks=0,cosetComparisons=0,strictCoset=0,nonconstantPolar=0;
 for(let z=0;z<480;z++){
  let r=1+rnd(4),d=1+rnd(Math.min(2*r+1,6)),a=Array.from({length:2*r},()=>rnd(1<<d)),dep=Array.from({length:r},(_,i)=>[rnd(1<<i),rnd(1<<i)]),out=rnd(1<<r);
  let l=rank(a.map(BigInt)),image=new Set;for(let k=0;k<1<<d;k++)image.add(a.reduce((v,x,i)=>v|(par(x&k)<<i),0));
  let reps=new Map,polarSet=new Set,quadCosets=new Set;
  for(let q=0;q<1<<(2*r);q++){
   let g=[];for(let i=0;i<r;i++)g.push(mul(xor(affine(a[2*i],q>>2*i&1,d),sum(dep[i][0],g)),xor(affine(a[2*i+1],q>>(2*i+1)&1,d),sum(dep[i][1],g))));
   let F=sum(out,g),D=F.reduce((v,m)=>Math.max(v,pc(m)),0),key=Math.min(...[...image].map(x=>x^q)),top=F.filter(m=>pc(m)===D&&D>=2).sort((a,b)=>a-b).join(","),P=F.filter(m=>pc(m)===2).sort((a,b)=>a-b).join(",");
   if(reps.has(key)){let old=reps.get(key);assert((D<=1&&old.D<=1)||(old.D===D&&old.top===top),"coset top degree");if(D<=2)assert(old.P===P,"coset polar");cosetComparisons++}else reps.set(key,{D,top,P});
   if(D<=2){quadratic++;polarSet.add(P);quadCosets.add(key);if(P)nonconstantPolar++}topChecks++;offsets++;
  }
  assert(reps.size===2**(2*r-l)&&polarSet.size<=quadCosets.size,"coset budget");
  if(polarSet.size<2**(2*r-l))strictCoset++;
  suffixes++;
 }
 let bounds=[];
 for(let k=1;k<=16;k++){
  let M=2**k,old=3*M/2,b=old;
  while(true){let r=b-M+1;if(2*r>=M+1&&BigInt(r)*BigInt(M+1-r)<=1n<<BigInt(2*r-M-1))break;b++}
  assert(b===old+k-1&&b<=2*M-1,"closed lower bound");
  if(b>old)strict++;
  bounds.push({k,M,old,lower:b,upper:2*M-1});
 }
 return {seed:870044,subspaces,eligible,rankChecks,slopeChecks,complementChecks,suffixes,offsets,quadratic,topChecks,cosetComparisons,strictCoset,nonconstantPolar,strict,bounds};
}
console.log(JSON.stringify(replay(),null,2));

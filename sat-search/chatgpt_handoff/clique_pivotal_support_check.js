"use strict";
// Clean-clique pivotal extension and local side-input truth-table controls.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870052;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function instance(N,K){
  let E=[],idx=Array.from({length:N},()=>Array(N).fill(-1));
  for(let i=0;i<N;i++)for(let j=i+1;j<N;j++){idx[i][j]=idx[j][i]=E.length;E.push([i,j])}
  let masks=[];function rec(U,start){if(U.length===K){let m=0n;for(let i=0;i<K;i++)for(let j=i+1;j<K;j++)m|=1n<<BigInt(idx[U[i]][U[j]]);masks.push(m);return}
   for(let i=start;i<=N-(K-U.length);i++)rec(U.concat(i),i+1)
  }rec([],0);
  return {N,K,E,idx,masks,clique:x=>masks.some(m=>(x&m)===m)}
 }
 let pivotal=0,largeSupport=0,upper=0,footprint=0,exhaustive=0,sampled=0,sideTruth=0;
 function check(B,e,S,x){
  let {N,K,E,idx,clique}=B,[u,v]=E[e],blocked=new Set(S.flatMap(i=>E[i]));let U=[u,v];
  for(let i=0;i<N&&U.length<K;i++)if(i!==u&&i!==v&&!blocked.has(i))U.push(i);
  assert(U.length===K,"clean clique vertices");
  let ones=0n;for(let j=0;j<S.length;j++)if(x>>j&1)ones|=1n<<BigInt(S[j]);
  let y=ones;for(let i=0;i<K;i++)for(let j=i+1;j<K;j++){let a=idx[U[i]][U[j]];if(a!==e)y|=1n<<BigInt(a)}
  assert(S.every((a,i)=>Number(y>>BigInt(a)&1n)===(x>>i&1)),"respect partial assignment");
  let f=clique(ones);assert(clique(y)===f&&clique(y|1n<<BigInt(e)),"clean clique relevance");
  footprint++;
  if(S.length<K*(K-1)/2){assert(!f&&!clique(y),"small support pivotal");pivotal++}
  else if(f)upper++;else largeSupport++;
 }
 let B=instance(7,3),D=B.E.length;
 for(let e=0;e<D;e++){
  let A=Array.from({length:D},(_,i)=>i).filter(i=>i!==e);
  for(let k=0;k<=2;k++){function rec(S,start){if(S.length===k){for(let x=0;x<1<<k;x++){check(B,e,S,x);exhaustive++}return}for(let j=start;j<=A.length-(k-S.length);j++)rec(S.concat(A[j]),j+1)}rec([],0)}
 }
 for(let [N,K] of [[8,3],[14,4],[25,5],[40,6]]){
  let B=instance(N,K),b=K*(K-1)/2; // N=40,K=6 has 3.8M clique masks; avoid expensive repeated enumeration below
  for(let z=0;z<(N>=25?12:200);z++){
   let e=rnd(B.E.length),S=[],k=rnd(b);while(S.length<k){let a=rnd(B.E.length);if(a!==e&&!S.includes(a))S.push(a)}check(B,e,S,rnd(1<<k));sampled++;
  }
  for(let z=0;z<10;z++){
   let e=rnd(B.E.length),[u,v]=B.E[e],U=Array.from({length:N},(_,i)=>i).filter(i=>i!==u&&i!==v).slice(0,K),S=[];
   for(let i=0;i<K;i++)for(let j=i+1;j<K;j++)S.push(B.idx[U[i]][U[j]]);
   check(B,e,S,(1<<S.length)-1); // all ones already force clique
   check(B,e,S,(1<<S.length)-2); // all but one, clean extension remains pivotal
  }
 }
 // Exhaust all 2-input nonconstant truth tables for side gate disabling.
 for(let t=0;t<16;t++){
  let val=(x,y)=>t>>((x<<1)|y)&1;
  if(![0,1].some(y=>val(0,y)!==val(1,y)))continue;
  if(![0,1].some(x=>val(x,0)!==val(x,1)))continue;
  let canal=[0,1].some(y=>val(0,y)===val(1,y));assert(canal===(t!==6&&t!==9),"side control");sideTruth++;
 }
 let profiles=[];for(let N of [100,1000,10000,100000]){let K=Math.ceil(Math.log2(N)),b=K*(K-1)/2,L=K+2*(b-1),D=N*(N-1)/2;if(L<=N)profiles.push({N,K,b,L,edgeInputs:D,multipleReadLower:Math.ceil(b*D/(L*(L-1)/2))})}
 return {seed:870052,exhaustive,sampled,pivotal,footprint,largeSupport,upper,sideTruth,profiles}
}
console.log(JSON.stringify(replay(),null,2));

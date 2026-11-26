// Exact read-once and one-fork cofactor tests for L-meta-16102.
// A successful one-fork test is a construction; failure gives a lower bound.
// Node.js, no dependencies.
function run(){
 const T=18445899635892944896n;
 const range=n=>Array.from({length:n},(_,i)=>i),bit=(t,x)=>Number(t>>BigInt(x)&1n),mask=n=>(1n<<BigInt(2**n))-1n;
 function ok(x,m){if(!x)throw Error(m||"assertion");}
 function inject(x,V){return V.reduce((a,v,i)=>a|((x>>i&1)<<v),0);}
 function project(t,V,base=0){let z=0n;for(let x=0;x<2**V.length;x++)if(bit(t,base|inject(x,V)))z|=1n<<BigInt(x);return z;}
 function essential(n,t){return range(n).filter(i=>range(2**n).some(x=>bit(t,x)!==bit(t,x^(1<<i))));}
 function variable(n,i){let z=0n;for(let x=0;x<2**n;x++)if(x>>i&1)z|=1n<<BigInt(x);return z;}
 const cache=new Map();
 function formulas(n,repeat){
  let key=n+":"+repeat;if(cache.has(key))return cache.get(key);
  let labels=range(n);if(repeat)labels.push(0);
  let F=(1<<labels.length)-1,D=Array(F+1);
  for(let m=1;m<=F;m++){
   if(!(m&(m-1))){let i=labels[31-Math.clz32(m)],x=variable(n,i);D[m]=new Set(repeat&&i===0?[x,x^mask(n)]:[x]);continue;}
   let S=new Set(),low=m&-m;
   for(let a=(m-1)&m;a;a=(a-1)&m)if(a&low){let b=m^a;for(let x of D[a])for(let y of D[b]){S.add(x&y);S.add(x|y);}}
   D[m]=S;
  }
  cache.set(key,D[F]);return D[F];
 }
 function ro(n,t){return n<=1||formulas(n,false).has(t);}
 function bound(n,t){
  let V=essential(n,t);t=project(t,V);n=V.length;
  if(n<=1)return {m:n,lower:0,kind:"constant/literal"};
  if(ro(n,t))return {m:n,lower:n-1,kind:"read-once"};
  for(let s=1;s<(1<<n)-1;s++){
   let U=range(n).filter(i=>s>>i&1),W=range(n).filter(i=>!(s>>i&1));
   let rows=range(2**U.length).map(x=>project(t,W,inject(x,U))),a=rows[0],b=rows[rows.length-1];
   if(a===b||rows.some(x=>x!==a&&x!==b))continue;
   let g=0n;for(let x=0;x<rows.length;x++)if(rows[x]===b)g|=1n<<BigInt(x);
   if(!ro(U.length,g))continue;
   let h=0n;for(let y=0;y<2**W.length;y++){if(bit(a,y))h|=1n<<BigInt(2*y);if(bit(b,y))h|=1n<<BigInt(2*y+1);}
   if(formulas(W.length+1,true).has(h))return {m:n,lower:n,kind:"one-fork"};
  }
  return {m:n,lower:n+1,kind:"no zero/one fork"};
 }
 let cofactorCount=0,unique=new Map(),strengthened=0,singles=[],sets=[];
 for(let S=1;S<64;S++){
  let U=range(6).filter(i=>S>>i&1),V=range(6).filter(i=>!(S>>i&1)),best=-1,witness=0,phases=[];
  for(let x=0;x<2**U.length;x++){
   let t=project(T,V,inject(x,U)),key=V.length+":"+t;
   if(!unique.has(key))unique.set(key,bound(V.length,t));
   let r=unique.get(key);cofactorCount++;if(r.lower>Math.max(0,r.m-1))strengthened++;
   phases.push({phase:x,table:t.toString(16),...r});
   if(r.lower>best){best=r.lower;witness=x;}
  }
  sets.push({mask:S,inputs:U,lower:best,witness,maxDirectBinaryReaders:8-best});
  if(U.length===1)singles.push({i:U[0],...sets[sets.length-1],phases});
 }
 ok(cofactorCount===728,"restriction count");ok(singles.every(x=>x.lower>=4),"support");
 // A few truth tables with independently obvious costs.
 ok(bound(3,0xe8n).lower===4,"majority needs >=4 binary gates");
 ok(bound(3,0x80n).lower===2,"AND3");
 ok(bound(3,0xa8n).lower===2,"x AND (y OR z)");
 return {table:T.toString(),cofactorCount,distinctRawCofactorTables:unique.size,strengthened,singles,sets,formulaSetSizes:[...cache].map(([key,v])=>({key,count:v.size}))};
}
if(typeof module!=="undefined"&&require.main===module)console.log(JSON.stringify(run(),null,2));

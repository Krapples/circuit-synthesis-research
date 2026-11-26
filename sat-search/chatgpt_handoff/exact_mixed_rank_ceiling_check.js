"use strict";
// Exact finite proof replay. Run node exact_mixed_rank_ceiling_check.js.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};
 function enumerate(t,ordered){
  const N=1<<(2*t),bits=Array.from({length:N},(_,i)=>1n<<BigInt(i));
  const z=Array.from({length:2*t},(_,j)=>bits.reduce((v,b,i)=>i>>j&1?v|b:v,0n));
  function rank(vs){let p=new Map;for(let v of vs){while(v){let h=v.toString(16),k=4*(h.length-1)+31-Math.clz32(parseInt(h[0],16));if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}}return p.size}
  const xor=(m,g)=>g.reduce((a,v,j)=>m>>j&1?a^v:a,0n);
  function coefficientRank(h){
   let a=Uint8Array.from(bits,b=>Number((h&b)!==0n));
   for(let j=0;j<2*t;j++)for(let i=0;i<N;i++)if(i>>j&1)a[i]^=a[i^(1<<j)];
   let rows=Array(N).fill(0n);
   for(let m=1;m<N;m++)if(a[m])for(let i=(m-1)&m;i;i=(i-1)&m)rows[i]|=bits[m^i];
   // Symmetric alternating matrix: diagonal zero; all ranks even.
   let r=rank(rows);assert(r%2===0,"alternating rank");
   return r;
  }
  function directRanks(h){
   let a=bits.map(b=>Number((h&b)!==0n)),rows=[],mixed=[];
   for(let u=0;u<N;u++){
    let v=0n,w=0n;for(let q=0;q<N;q++){
      if(a[u^q])v|=bits[q];
      if(a[u^q]^a[u]^a[q]^a[0])w|=bits[q];
    }
    rows.push(v);mixed.push(w);
   }
   return [rank(mixed),rank(rows)];
  }
  let max=0,best=null,hist={},classes={},count=0,cache=new Map,directChecks=0;
  function dfs(g,dep){
   let i=g.length;
   if(i===t){
    let cl=dep.map(([a,b])=>a===0&&b===0?0:a===0||b===0||a===b?1:2).join("");
    for(let out=0;out<1<<t;out++){
     let h=xor(out,g),r=cache.get(h);
     if(r===undefined){
      r=coefficientRank(h);cache.set(h,r);
      if(t<=3||cache.size%53===0||r>max){
       let [dr,full]=directRanks(h);
       assert(dr===r,"independent direct matrix");
       // Generic h is zero at zero; every nonzero h is nonconstant.
       assert(full===r+(h===0n?0:2),"full translation rank");
       directChecks++;
      }
     }
     count++;hist[r]=(hist[r]??0)+1;classes[cl]=Math.max(classes[cl]??0,r);
     if(r>max){max=r;best={dep,out,r,truth:h.toString(16)}}
    }return;
   }
   for(let a=0;a<1<<i;a++)for(let b=ordered?0:a;b<1<<i;b++)dfs([...g,(z[2*i]^xor(a,g))&(z[2*i+1]^xor(b,g))],[...dep,[a,b]]);
  }
  dfs([],[]);
  const expected=(1<<t)*(Array.from({length:t},(_,i)=>1<<i).reduce((a,n)=>a*(ordered?n*n:n*(n+1)/2),1));
  assert(count===expected,"complete enumeration");
  assert(max===2**(t+1)-2,"observed maximum");
  return {t,ordered,count,distinct:cache.size,directChecks,max,best,hist,classes};
 }
 const results=[enumerate(1,true),enumerate(2,true),enumerate(3,true),enumerate(4,false)];
 // Exact packed rectangular target rank by direct anchoring, not formula only.
 function witness(m,l){
  const N=1<<(m*l),Q=1<<(m+l),rows=Array(N).fill(0n),p=new Map;
  for(let x=0;x<N;x++)for(let q=0;q<Q;q++){
   const f=(x,q)=>{for(let j=0;j<l;j++)if(q>>(m+j)&1){let ok=true;for(let i=0;i<m;i++)if((q>>i&1)&&!(x>>(i*l+j)&1))ok=false;if(ok)return 1}return 0};
   if(f(x,q)^f(x,0)^f(0,q)^f(0,0))rows[x]|=1n<<BigInt(q);
  }
  for(let v of rows)while(v){let k=v.toString(2).length-1;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}
  let r=p.size;assert(r===((1<<m)-1)*((1<<l)-1),"witness rank");return {m,l,assignments:N*Q,rank:r};
 }
 return {results,witnesses:[witness(2,3),witness(2,4)]};
}
console.log(JSON.stringify(replay(),null,2));

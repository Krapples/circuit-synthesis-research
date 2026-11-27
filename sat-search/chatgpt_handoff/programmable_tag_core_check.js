"use strict";
// Check heterogeneous payload cores and graph/dictionary product residuals.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};
 const pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 function graphs(n){let out=new Set;function r(B,i){if(i===n){function s(k,E){if(k===B.length){out.add(E);return}let G=B[k];for(let mask=0;mask<1<<(G.length-1);mask++){if(G.length>1&&!mask)continue;let f=E;for(let a=0;a<G.length;a++)for(let b=a+1;b<G.length;b++)if((a?mask>>(a-1)&1:0)!==(b?mask>>(b-1)&1:0))f|=1n<<BigInt(G[a]*n+G[b]);s(k+1,f)}}s(0,0n);return}for(let g of B){g.push(i);r(B,i+1);g.pop()}B.push([i]);r(B,i+1);B.pop()}r([],0);return [...out]}
 let comparisons=0,profiles=0,independentFactors=0;
 for(let n=1;n<=4;n++)for(let mask=1;mask<1<<(2*n);mask++){
  let J=Array.from({length:n},(_,i)=>i).filter(i=>mask>>(2*i)&3),k=pc(mask),slots=J.map(i=>[0,1].filter(j=>mask>>(2*i+j)&1));
  let patterns=Array.from({length:1<<k},(_,x)=>{let off=0;return slots.map(s=>s.reduce((a,j)=>a|((x>>off++&1)<<j),0))});
  let G=graphs(J.length),seen=new Set;
  for(let E of G){let r=0n;for(let x=0;x<patterns.length;x++){let p=patterns[x],ok=true;for(let i=0;i<J.length;i++)for(let j=i+1;j<J.length;j++)if((E>>BigInt(i*J.length+j)&1n)&&p[i]===p[j])ok=false;if(ok)r|=1n<<BigInt(x);comparisons++}assert(!seen.has(r)&&r!==0n,"graph residual distinct nonzero");seen.add(r)}
  for(let c=0;c<J.length;c++){
   let rest=Array.from({length:J.length},(_,i)=>i).filter(i=>i!==c),R=graphs(rest.length),L=1<<slots[c].length,set=new Set;
   for(let E of R)for(let h=1;h<1<<L;h++){
    let r=0n;for(let x=0;x<patterns.length;x++){let p=patterns[x],ix=slots[c].reduce((a,j,k)=>a|((p[c]>>j&1)<<k),0),ok=!!(h>>ix&1);for(let i=0;i<rest.length;i++)for(let j=i+1;j<rest.length;j++)if((E>>BigInt(i*rest.length+j)&1n)&&p[rest[i]]===p[rest[j]])ok=false;if(ok)r|=1n<<BigInt(x);comparisons++}
    assert(r!==0n&&!set.has(r),"product residual distinct");set.add(r);independentFactors++
   }
   assert(set.size===R.length*((1<<L)-1),"product count")
  }
  profiles++;
 }
 // A valid abstract programmable unit-promise evaluator: each pair uses
 // a query-only conflict flag, each slot has a query-only dictionary table
 // and local enable; graph inputs can be arbitrary, not only bicliques.
 // Track original data-ancestor masks, and verify proposed lower bounds on
 // every nonempty S in small full evaluator topologies.
 let dagCases=0,subsetChecks=0,coreChecks=0,minSlack=Infinity;
 const ceilLog=n=>n<=1n?0:(n-1n).toString(2).length;
 for(let n=1;n<=5;n++)for(let ell=1;ell<=2;ell++){
  let d=n*ell,A=[],x=Array.from({length:d},(_,i)=>1n<<BigInt(i)),gate=(a,b)=>{let v=a|b;A.push(v);return v},q=0n;
  function merge(a){if(!a.length)return 0n;let r=a[0];for(let i=1;i<a.length;i++)r=gate(r,a[i]);return r}
  let factors=[];
  for(let i=0;i<n;i++){
   let a=Array(1<<ell).fill(q);
   for(let j=0;j<ell;j++){let b=[];for(let k=0;k<a.length;k+=2)b.push(gate(gate(a[k],x[i*ell+j]),gate(a[k+1],x[i*ell+j])));a=b}
   factors.push(gate(a[0],q))
  }
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let a=[];for(let k=0;k<ell;k++)a.push(gate(x[i*ell+k],x[j*ell+k]));factors.push(gate(merge(a),q))}
  merge(factors);
  let G=Array.from({length:n+1},(_,i)=>BigInt(graphs(i).length));
  for(let S=1;S<1<<d;S++){
   let s=pc(S),B=A.filter(v=>v&BigInt(S)).length,slots=Array.from({length:n},(_,i)=>pc(S>>(ell*i)&((1<<ell)-1))),active=slots.map((v,i)=>v?i:-1).filter(i=>i>=0);
   for(let J=1;J<1<<active.length;J++){
    let I=active.filter((_,i)=>J>>i&1),k=I.reduce((v,i)=>v+slots[i],0),R=G[I.length];
    for(let i of I){let N=G[I.length-1]*((1n<<BigInt(1<<slots[i]))-1n);if(N>R)R=N}
    let bound=2*s-k-1+ceilLog(R);assert(B>=bound,"ancestor bound");minSlack=Math.min(minSlack,B-bound);coreChecks++;
   }
   subsetChecks++
  }
  dagCases++;
 }
 return {profiles,comparisons,independentFactors,dagCases,subsetChecks,coreChecks,minSlack}
}
console.log(JSON.stringify(replay(),null,2));

"use strict";
// Conditional entropy of projected randomly permuted product factors.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};let seed=870064;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function perms(A){let out=[];function rec(p){if(p.length===A){out.push(p);return}for(let j=0;j<A;j++)if(!p.includes(j))rec(p.concat(j))}rec([]);return out}
 function permCols(A,P,p){let x=0;for(let i=0;i<A;i++)for(let j=0;j<A;j++)if(P>>(i*A+p[j])&1)x|=1<<(i*A+j);return x}
 function H(counts,n){let r=0;for(let a of counts.values()){let p=a/n;r-=p*Math.log2(p)}return r}
 let profiles=0,products=0,codes=0,rowChecks=0,strict=0,examples=[];
 for(let A of [2,3]){
  let ps=perms(A),N=A*A,num=1<<N;
  for(let z=0;z<(A===2?num:100);z++){
   let R=A===2?z:z===0?(1<<A)-1:z===1?num-1:rnd(num);
   let d=Array.from({length:A},(_,j)=>Array.from({length:A},(_,i)=>R>>(i*A+j)&1).reduce((a,b)=>a+b,0)).sort((a,b)=>b-a);
   let lower=d.reduce((a,b,j)=>a-Math.log2(1/(A-j)+(1-1/(A-j))*2**(-b)),0),e=0;
   for(let P=0;P<num;P++){let c=new Map;for(let p of ps){let x=permCols(A,P,p)&R;c.set(x,(c.get(x)||0)+1);codes++}e+=H(c,ps.length)/num;products++}
   assert(e+1e-10>=lower,"conditional permutation entropy");
   let signature=new Set(ps.map(p=>permCols(A,Array.from({length:A},(_,i)=>1<<(i*A+i)).reduce((a,b)=>a|b),p)&R));
   if(e>Math.log2(signature.size)+1e-10)strict++;
   if(R===(1<<A)-1){let cnt=new Map;for(let P=0;P<1<<A;P++){let k=0;for(let i=0;i<A;i++)k+=P>>i&1;cnt.set(k,(cnt.get(k)||0)+1)}assert(Math.abs(e-(A-H(cnt,1<<A)))<1e-10,"whole row exact entropy");rowChecks++;examples.push({A,conditionalEntropy:e,lower,permutationOnly:Math.log2(signature.size)})}
   profiles++;
  }
 }
 return {seed:870064,profiles,products,codes,rowChecks,strict,examples}
}
console.log(JSON.stringify(replay(),null,2));

"use strict";
// Permutation signatures, entropy, universal product fibers and ingress cells.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};
 let seed=870063;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function perms(A){let out=[];function rec(p){if(p.length===A){let m=0n;for(let i=0;i<A;i++)m|=1n<<BigInt(i*A+p[i]);out.push({p,m});return}for(let j=0;j<A;j++)if(!p.includes(j))rec(p.concat(j))}rec([]);return out}
 function pop(x){let n=0;while(x){x&=x-1n;n++}return n}
 function maxMatch(A,R){let to=Array(A).fill(-1);function aug(i,seen){for(let j=0;j<A;j++)if((R>>BigInt(i*A+j)&1n)&&!seen[j]){seen[j]=1;if(to[j]<0||aug(to[j],seen)){to[j]=i;return true}}return false}let d=0;for(let i=0;i<A;i++)d+=Number(aug(i,[]));return d}
 let profiles=0,sigs=0,entropy=0,matchChecks=0,coverChecks=0,minGap=Infinity,examples=[];
 for(let A=2;A<=7;A++){let P=perms(A),N=A*A,num=A<=3?2**N:240;
  for(let z=0;z<num;z++){let R=A<=3?BigInt(z):Array.from({length:N},(_,i)=>rnd(2)?1n<<BigInt(i):0n).reduce((a,b)=>a|b,0n);
   if(A>=4&&z===0)R=(1n<<BigInt(N))-1n;
   if(A>=4&&z===1)R=(1n<<BigInt(A))-1n;
   let counts=new Map;for(let {m} of P){let x=m&R;counts.set(x,(counts.get(x)||0)+1);sigs++}
   let H=0;for(let n of counts.values()){let p=n/P.length;H-=p*Math.log2(p)}
   let lower=pop(R)*Math.log2(P.length)/N;
   assert(H+1e-9>=lower&&Math.log2(counts.size)+1e-9>=H,"permutation entropy");
   let d=maxMatch(A,R);assert(counts.size>=2**Math.min(d,A-1),"matching signature");matchChecks++;
   let k=Math.ceil(Math.log2(counts.size)-1e-10);
   if(k<A-1){assert(d<=k,"matching cover bound");coverChecks++}
   minGap=Math.min(minGap,H-lower);entropy++;profiles++;
   if(A>=4&&z<=1)examples.push({A,r:pop(R),M:counts.size,H,lower,k,d});
  }
 }
 function product(A,X,Y){let z=0n;for(let i=0;i<A;i++)for(let k=0;k<A;k++)for(let j=0;j<A;j++)if((X>>BigInt(i*A+j)&1n)&&(Y>>BigInt(j*A+k)&1n))z|=1n<<BigInt(i*A+k);return z}
 function permFactors(A,P,p){let Y=0n,X=0n;for(let i=0;i<A;i++){X|=1n<<BigInt(i*A+p[i]);for(let k=0;k<A;k++)if(P>>BigInt(i*A+k)&1n)Y|=1n<<BigInt(p[i]*A+k)}return [X,Y]}
 let factors=0,fibers=0,cells=0,capacityChecks=0,strictControls=0;
 for(let A of [2,3]){let ps=perms(A),N=A*A,num=1<<N;for(let z=0;z<num;z++)for(let {p} of ps){let [X,Y]=permFactors(A,BigInt(z),p);assert(product(A,X,Y)===BigInt(z),"universal factors");factors++}
  for(let t=0;t<80;t++){let R=BigInt(rnd(num)),M=new Set(ps.map(({m})=>m&R)).size,q=rnd(N+1),K=1<<q,H=new Map;
   for(let z=0;z<num;z++){let a=rnd(K);if(!H.has(a))H.set(a,[]);H.get(a).push(z)}
   let max=0;for(let [a,queries] of H){let pattern=new Map,code=new Set;
    for(let P=0;P<num;P++){let pat=queries.map(z=>Number(!!(P&z))).join("");if(!pattern.has(pat))pattern.set(pat,P)}
    for(let [pat,P] of pattern)for(let {p} of ps){let [X,Y]=permFactors(A,BigInt(P),p);assert(product(A,X,Y)===BigInt(P),"cell product");code.add(pat+":"+(X&R));fibers++}
    assert(code.size===pattern.size*M,"multiplicative capacity");max=Math.max(max,code.size);cells++;
   }
   let c=Math.ceil(Math.log2(max)-1e-10),cap=Math.floor(2**c/M);
   assert(num<=K*(cap-1)+1,"global corrected capacity");capacityChecks++;
   if(M>1&&c+q>N)strictControls++;
  }
 }
 return {seed:870063,profiles,sigs,entropy,matchChecks,coverChecks,minGap,examples,factors,fibers,cells,capacityChecks,strictControls}
}
console.log(JSON.stringify(replay(),null,2));

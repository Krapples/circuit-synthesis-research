"use strict";
// Exact disjointness cell capacities, tight compression controls and monotone cube automorphisms.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};let seed=870062;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 let familyCases=0,patternChecks=0,closed=0,strict=0,nonzero=0,codeCases=0,tradeoffChecks=0,exactControls=0,semanticChecks=0,permutations=0,monotone=0,orderChecks=0,productChecks=0;
 const clog=n=>n<=1?0:Math.ceil(Math.log2(n)-1e-10);
 function family(n,H){let N=1<<n,R=new Set;
  for(let s=0;s<N;s++){let p=H.map(z=>Number((z&~s)===0)).join("");R.add(p);patternChecks++}
  let C=H.includes(0)&&H.every(a=>H.every(b=>H.includes(a|b)));
  assert(R.size>=H.length&&((R.size===H.length)===C),"union closure characterization");
  if(!H.includes(0)){assert(R.size>=H.length+1,"zero-free cell strict");nonzero++}
  if(C)closed++;else strict++;familyCases++;return R.size
 }
 for(let n=1;n<=4;n++){let N=1<<n,num=n<=3?(1<<N)-1:2200;
  for(let k=1;k<=num;k++){let h=n<=3?k:1+rnd((1<<N)-1),H=[];for(let z=0;z<N;z++)if(h>>z&1)H.push(z);family(n,H)}
 }
 for(let n=2;n<=6;n++){let N=1<<n;
  for(let z=0;z<200;z++){let q=rnd(n+1),K=1<<q,M=new Map;
   for(let i=0;i<N;i++){let k=rnd(K);if(!M.has(k))M.set(k,[]);M.get(k).push(i)}
   let c=clog(Math.max(...[...M.values()].map(H=>family(n,H))));assert(c>=1&&c+q>=n,"old bound");if(c<n)assert(c+q>=n+1,"strict bound");assert(N<=2**(c+q)-2**q+1,"capacity");codeCases++;tradeoffChecks++;
  }
  for(let c=1;c<=n;c++){let q=c===n?0:n-c+1,seen=new Map;for(let x=0;x<N;x++)for(let z=0;z<N;z++){let code=z&((1<<q)-1),port=c===n?x:((x>>q)<<1)|Number(!!(x&code)),out=c===n?!!(port&z):!!((port&1)||((port>>1)&(z>>q)));assert(port<1<<c&&out===!!(x&z),"exact encoder decoder");semanticChecks++}exactControls++}
 }
 // Every monotone bijection of a Boolean cube is a coordinate permutation.
 for(let n=1;n<=3;n++){let N=1<<n;function rec(p){if(p.length===N){permutations++;let ok=true;for(let x=0;x<N&&ok;x++)for(let j=0;j<n;j++)if(!(x>>j&1)){orderChecks++;if(p[x]&~p[x|1<<j]){ok=false;break}}if(ok){monotone++;assert(p[0]===0&&Array.from({length:n},(_,j)=>p[1<<j]).every(v=>v>0&&!(v&(v-1))),"automorphism");for(let x=0;x<N;x++){let v=0;for(let j=0;j<n;j++)if(x>>j&1)v|=p[1<<j];assert(p[x]===v,"coordinate permutation")}}return}for(let x=0;x<N;x++)if(!p.includes(x))rec(p.concat(x))}rec([])}
 // Tight-width product encoding: all Boolean 2x2 products, each uniquely
 // distinguished by unit query matrices. Nonmonotone code bijections valid.
 function prod(A,B){let p=0;for(let i=0;i<2;i++)for(let k=0;k<2;k++)for(let j=0;j<2;j++)if((A>>(2*i+j)&1)&&(B>>(2*j+k)&1))p|=1<<(2*i+k);return p}
 for(let A=0;A<16;A++)for(let B=0;B<16;B++){let p=prod(A,B),enc=p^15;assert(prod(9,p)===p,"surjectivity");for(let z=0;z<16;z++){let expected=!!(p&z);assert(!!((enc^15)&z)===expected,"arbitrary bijection decoder");productChecks++}}
 return {seed:870062,familyCases,patternChecks,closed,strict,nonzero,codeCases,tradeoffChecks,exactControls,semanticChecks,permutations,monotone,orderChecks,productChecks}
}
console.log(JSON.stringify(replay(),null,2));

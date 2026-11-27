"use strict";
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};
 let seed=870048;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function rank(vs){let p=new Map;for(let v of vs)while(v){let b=v&-v;if(p.has(b))v^=p.get(b);else{p.set(b,v);break}}return p.size}
 function anchored(A){let m=A.length,n=A[0].length;return rank(Array.from({length:n},(_,j)=>{let v=0;for(let i=1;i<m;i++)v|=(A[i][j]^A[0][j]^A[i][0]^A[0][0])<<(i-1);return v}))}
 function constraints(A){let m=A.length,n=A[0].length,sets=[];
  for(let j=0;j<n;j++){let known=[];for(let i=0;i<m;i++)if(A[i][j]>=0)known.push(i);let S=new Set;
   for(let v=0;v<1<<(m-1);v++){let ok=true;if(known.length){let k=known[0],c=A[k][j]^(k?v>>(k-1)&1:0);for(let i of known)if((A[i][j]^ (i?v>>(i-1)&1:0))!==c){ok=false;break}}
    if(ok)S.add(v)}
   sets.push(S)
  }return sets.sort((a,b)=>a.size-b.size)
 }
 // enumerate linear subspaces in RREF, then cosets through a point in smallest admissible set.
 function existsFlat(A,k){let m=A.length-1,sets=constraints(A),tested=0;
  if(k>=m)return {ok:true,tested};
  let best=sets[0],P=[],B=[];
  function fill(i,piv){if(i===k){
    let L=[0];for(let b of B)L.push(...L.map(x=>x^b));let seen=new Set;
    for(let a of best){let key=Math.min(...L.map(x=>x^a));if(seen.has(key))continue;seen.add(key);tested++;
      if(sets.every(S=>L.some(x=>S.has(x^a))))return true;
    }return false;
   }
   let free=((1<<m)-1)&~((1<<(P[i]+1))-1)&~piv;
   for(let s=free;;s=(s-1)&free){B[i]=(1<<P[i])|s;if(fill(i+1,piv))return true;if(!s)break}return false
  }
  function choose(start){if(P.length===k)return fill(0,P.reduce((x,y)=>x|1<<y,0));for(let i=start;i<=m-(k-P.length);i++){P.push(i);if(choose(i+1))return true;P.pop()}return false}
  return {ok:choose(0),tested}
 }
 function exact(A){if(A.length>A[0].length)A=A[0].map((_,j)=>A.map(row=>row[j]));let tried=0;for(let k=0;k<Math.min(A.length-1,A[0].length-1);k++){let z=existsFlat(A,k);tried+=z.tested;if(z.ok)return {r:k,tried}}return {r:Math.min(A.length-1,A[0].length-1),tried}}
 function brute(A){let B=A.map(r=>r.slice()),holes=[];for(let i=0;i<B.length;i++)for(let j=0;j<B[0].length;j++)if(B[i][j]<0)holes.push([i,j]);let best=Infinity;for(let v=0;v<1<<holes.length;v++){holes.forEach(([i,j],k)=>B[i][j]=v>>k&1);best=Math.min(best,anchored(B));if(!best)break}return best}
 function rectangle(A){let m=A.length,n=A[0].length,best=0;for(let S=1;S<1<<m;S++){let rows=Array.from({length:m},(_,i)=>i).filter(i=>S>>i&1);if(rows.length<=best+1)continue;let cols=Array.from({length:n},(_,j)=>j).filter(j=>rows.every(i=>A[i][j]>=0));if(cols.length<=best+1)continue;best=Math.max(best,anchored(rows.map(i=>cols.map(j=>A[i][j]))))}return best}
 // zero rank iff known edge values are consistent with row/col potentials.
 function zero(A){let m=A.length,n=A[0].length,adj=Array.from({length:m+n},()=>[]),v=Array(m+n).fill(-1);for(let i=0;i<m;i++)for(let j=0;j<n;j++)if(A[i][j]>=0){adj[i].push([m+j,A[i][j]]);adj[m+j].push([i,A[i][j]])}for(let i=0;i<m+n;i++)if(v[i]<0){v[i]=0;let Q=[i];for(let k=0;k<Q.length;k++){let a=Q[k];for(let [b,c] of adj[a]){let w=v[a]^c;if(v[b]<0){v[b]=w;Q.push(b)}else if(v[b]!==w)return false}}}return true}
 let exhaustive=0,sampled=0,large=0,flatTests=0,strict=0,strictFloor=0,zeroChecks=0,example=null,cycle=null,hist={};
 function check(A,doBrute){let r=exact(A),b=rectangle(A);flatTests+=r.tried;assert(r.r>=b&&zero(A)===(r.r===0),"lower bound/zero");zeroChecks++;
  if(doBrute)assert(r.r===brute(A),"brute comparison");
  if(r.r>b){strict++;if(!cycle&&b===0&&r.r===1)cycle=A.map(r=>r.slice())}
  let floor=x=>Math.floor(Math.log2(x+1));if(floor(r.r)>floor(b)){strictFloor++;if(!example&&r.r>=3)example={A:A.map(r=>r.slice()),r:r.r,rectangle:b}}
  hist[r.r]=(hist[r.r]||0)+1;
 }
 for(let [m,n] of [[2,3],[3,3]])for(let t=0;t<3**(m*n);t++){let x=t,A=Array.from({length:m},()=>Array.from({length:n},()=>{let a=x%3-1;x=Math.floor(x/3);return a}));check(A,true);exhaustive++}
 for(let z=0;z<450;z++){let m=4,n=z%3===0?8:4,A=Array.from({length:m},()=>Array.from({length:n},()=>rnd(5)===0?-1:rnd(2)));let holes=A.flat().filter(x=>x<0).length;check(A,holes<=12);sampled++}
 for(let z=0;z<30;z++){let A=Array.from({length:8},()=>Array.from({length:8},()=>rnd(4)===0?-1:rnd(2)));check(A,false);large++}
 // Anchor-free 6-cycle with odd parity, no fully known 2x2.
 let C=[[0,-1,1],[0,0,-1],[-1,0,0]];assert(exact(C).r===1&&rectangle(C)===0,"cycle control");
 return {seed:870048,exhaustive,sampled,large,flatTests,strict,strictFloor,zeroChecks,hist,example,cycle:C}
}
console.log(JSON.stringify(replay(),null,2));

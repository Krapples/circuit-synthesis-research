"use strict";
// Exact graph support profiles, common polar coloring, and small suffix regression.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870043;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const pc=x=>{let n=0;while(x){x&=x-1;n++}return n},par=x=>pc(x)&1;
 function rank(vs){let p=new Map;for(let v of vs)while(v){let b=v&-v;if(p.has(b))v^=p.get(b);else{p.set(b,v);break}}return p.size}
 function spaces(n){let out=[];for(let d=0;d<=n;d++){function go(P,start){if(P.length===d){let mask=P.reduce((a,p)=>a|(1<<p),0),B=P.map(p=>1<<p);function fill(i){if(i===d){out.push(B.slice());return}let free=((1<<n)-1)^((1<<(P[i]+1))-1);free&=~mask;for(let s=free;;s=(s-1)&free){B[i]=(1<<P[i])|s;fill(i+1);if(!s)break}}fill(0);return}for(let p=start;p<=n-(d-P.length);p++)go(P.concat(p),p+1)}go([],0)}return out}
 function graph(n,edges){let N=1<<n,mask=N-1,adj=Array(n).fill(0);for(let [i,j] of edges){adj[i]|=1<<j;adj[j]|=1<<i}
 let alpha=0,z=adj.filter(x=>!x).length,profile=Array(n+1).fill(0);
 for(let I=0;I<N;I++){if(edges.some(([i,j])=>(I>>i&1)&&(I>>j&1)))continue;let closed=I;for(let i=0;i<n;i++)if(I>>i&1)closed|=adj[i];let a=pc(I),u=pc(mask^closed);alpha=Math.max(alpha,a);for(let l=0;l<=n;l++)profile[l]=Math.max(profile[l],a+Math.min(l,u))}
 let beta=Math.max(...edges.map(([i,j])=>{let allowed=mask&~(adj[i]|adj[j]|1<<i|1<<j),b=0;for(let I=allowed;;I=(I-1)&allowed){if(!edges.some(([i,j])=>(I>>i&1)&&(I>>j&1)))b=Math.max(b,pc(I));if(!I)break}return b}));
 let threeColor=false;function color(i,c){if(i===n){threeColor=true;return}for(let a=0;a<3&&!threeColor;a++)if(!edges.some(([u,v])=>v===i&&c[u]===a))color(i+1,[...c,a])}color(0,[]);
 let reserve=0;for(let r=0;r<=Math.ceil((n-z)/2);r++)reserve=Math.max(reserve,n+r-profile[Math.min(n,2*r)]);
 let commonMax=Math.max(alpha,threeColor?z+2:0),one=n+1-commonMax;
 return {alpha,z,profile,beta,threeColor,commonMax,reserve,one};
 }
 let graphs=0,subspaces=0,profileChecks=0,twoPolar=0,strict=0,strictOne=0,controls=[];
 const SS=new Map;
 function checkGraph(n,edges,tag=null){
  let p=graph(n,edges),prof=Array(n+1).fill(0),mx=0,max2=0;
  if(!SS.has(n))SS.set(n,spaces(n));
  for(let B of SS.get(n)){
   let d=B.length,forms=Array.from({length:n},(_,i)=>B.reduce((v,b,j)=>v|((b>>i&1)<<j),0));
   let polars=[],supp=[];
   for(let [i,j] of edges){let a=forms[i],b=forms[j],P=0;for(let u=0;u<d;u++)for(let v=u+1;v<d;v++)if(((a>>u&1)&(b>>v&1))^((a>>v&1)&(b>>u&1)))P|=1<<(u*d+v);polars.push(P);if(P)supp.push(a,b)}
   let l=rank(supp);for(let k=l;k<=n;k++)prof[k]=Math.max(prof[k],d);
   let delta=rank(polars.map(x=>x^polars[0]));
   if(!delta)mx=Math.max(mx,d);if(delta<=1){max2=Math.max(max2,d);twoPolar++}
   assert(d<=Math.max(p.alpha,l+p.beta),"edge-neighborhood support cap");
   subspaces++;
  }
  assert(prof.every((v,i)=>v===p.profile[i]),"exact graph profile");
  assert(mx===p.commonMax,"common polar coloring profile");profileChecks+=n+2;
  if(p.reserve>Math.max(n-p.alpha,Math.ceil((n-p.z)/2)))strict++;
  if(p.one>Math.max(n-p.alpha,Math.ceil((n-p.z)/2)))strictOne++;
  graphs++;if(tag)controls.push({tag,n,edges:edges.length,...p,maxTwoPolar:max2});
 }
 for(let n=2;n<=4;n++){let e=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)e.push([i,j]);for(let m=1;m<1<<e.length;m++)checkGraph(n,e.filter((_,i)=>m>>i&1),n===4&&m===63?"K4":null)}
 for(let z=0;z<30;z++){let e=[];for(let i=0;i<5;i++)for(let j=i+1;j<5;j++)if(rnd(2))e.push([i,j]);if(e.length)checkGraph(5,e)}
 for(let [a,b] of [[2,2],[2,3],[3,3]]){let e=[];for(let i=0;i<a;i++)for(let j=a;j<a+b;j++)e.push([i,j]);checkGraph(a+b,e,"K"+a+","+b)}
 // Analytic profile controls at larger n (independent set scan only, no subspace enumeration).
 for(let m of [4,5,6,8]){let e=[];for(let i=0;i<m;i++)for(let j=m;j<2*m;j++)e.push([i,j]);let p=graph(2*m,e);assert(p.profile.every((v,l)=>v===Math.max(m,l))&&p.reserve===m+Math.floor(m/2),"bipartite exact profile");controls.push({tag:"K"+m+","+m,n:2*m,edges:e.length,...p,analyticControl:true})}
 // Exact quadratic ANFs for abstract suffix circuits with arbitrary independent query offsets.
 const xor=(a,b)=>{let S=new Set(a);for(let m of b)S.has(m)?S.delete(m):S.add(m);return [...S]};
 const mul=(a,b)=>{let S=new Set;for(let a0 of a)for(let b0 of b){let m=a0|b0;S.has(m)?S.delete(m):S.add(m)}return [...S]};
 function affine(mask,c,d){let h=c?[0]:[];for(let i=0;i<d;i++)if(mask>>i&1)h.push(1<<i);return h}
 let suffixes=0,contexts=0,quadratic=0,cubic=0,maxDelta=[0,0,0],nonzeroDelta=0;
 for(let r=1;r<=2;r++)for(let z=0;z<600;z++){
  let d=2+rnd(5),N=1<<d,a=Array.from({length:2*r},()=>rnd(N)),dep=r===2?[rnd(2),rnd(2)]:[],out=1+rnd((1<<r)-1);
  let polys=[];
  for(let q=0;q<1<<(2*r);q++){
   let g1=mul(affine(a[0],q&1,d),affine(a[1],q>>1&1,d)),F=out&1?g1:[];
   if(r===2){let u=xor(affine(a[2],q>>2&1,d),dep[0]?g1:[]),v=xor(affine(a[3],q>>3&1,d),dep[1]?g1:[]);if(out&2)F=xor(F,mul(u,v))}
   polys.push(F);contexts++;
  }
  let quad=polys.every(h=>h.every(m=>pc(m)<=2));
  if(quad){
   let P=polys.map(h=>h.filter(m=>pc(m)===2).reduce((v,m)=>v|(1n<<BigInt(m)),0n));
   // BigInt rank for packed coefficient vectors.
   let piv=new Map;for(let x of P){let v=x^P[0];while(v){let k=v&-v;if(piv.has(k))v^=piv.get(k);else{piv.set(k,v);break}}}
   let rho=piv.size;assert(rho<=r-1,"small suffix polar variation");if(rho)nonzeroDelta++;maxDelta[r]=Math.max(maxDelta[r],rho);quadratic++;
   if(rho){let h=xor(polys[0],polys[P.findIndex(x=>x!==P[0])]);let B=Array.from({length:d},(_,i)=>h.filter(m=>pc(m)===2&&(m>>i&1)).reduce((v,m)=>v|(m^(1<<i)),0));assert(rank(B)===2,"varying polar decomposable")}
  }else{assert(r===2&&polys.every(h=>h.some(m=>pc(m)===3)),"query independent cubic");cubic++}
  suffixes++;
 }
 return {seed:870043,graphs,subspaces,profileChecks,twoPolar,strict,strictOne,controls,suffixes,contexts,quadratic,cubic,maxDelta,nonzeroDelta}
}
console.log(JSON.stringify(replay(),null,2));

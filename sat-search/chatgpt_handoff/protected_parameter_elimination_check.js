"use strict";
// Protected query fibers, certificate flats and fair-system rank-two exchanges.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870065;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const bit=(x,i)=>(x>>>i)&1,par=x=>{let v=0;while(x){x&=x-1;v^=1}return v},pc=x=>{let v=0;while(x){x&=x-1;v++}return v};
 function rank(rows){let b=Array(32).fill(0),r=0;for(let v of rows){for(let j=31;j>=0&&v;j--)if(bit(v,j)){if(b[j])v^=b[j];else{b[j]=v;r++;break}}}return r}
 function anfDegree(f){let a=f.slice(),n=Math.log2(a.length),d=0;for(let i=0;i<n;i++)for(let x=0;x<a.length;x++)if(bit(x,i))a[x]^=a[x^(1<<i)];for(let i=0;i<a.length;i++)if(a[i])d=Math.max(d,pc(i));return d}
 let profiles=0,paired=0,truthChecks=0,strictDegree=0,minFlatChecks=0,maxDegree=0;
 for(let z=0;z<900;z++){
  let t=2+rnd(4),ell=1+rnd(3),D=t*ell,m=1+rnd(Math.min(D,9)),p=rnd(1+Math.floor(m/2)),q=t+ell;
  let cols=[];while(cols.length<m){let v=1+rnd((1<<D)-1);if(rank(cols.concat(v))>cols.length)cols.push(v)}
  let drift=Array.from({length:q},()=>rnd(1<<D)),offset=rnd(1<<D),order=Array.from({length:m},(_,i)=>i);
  for(let i=m-1;i>0;i--){let j=rnd(i+1);[order[i],order[j]]=[order[j],order[i]]}
  let fixed=new Set(order.slice(0,2*p).filter((_,i)=>i%2===0)),free=order.filter(i=>!fixed.has(i)),a=free.length,rows=Array.from({length:D},(_,i)=>free.reduce((r,j,k)=>r|(bit(cols[j],i)<<k),0));
  let best={j:0,slots:[],r:0};for(let j=0;j<ell;j++){let R=[],S=[];for(let i=0;i<t;i++){let v=rows[i*ell+j];if(rank(R.concat(v))>R.length){R.push(v);S.push(i)}}if(R.length>best.r)best={j,slots:S,r:R.length}}
  assert(best.r>=Math.ceil(a/ell),"degree floor");let s=best.slots.reduce((v,i)=>v|(1<<i),0),lambda=1<<best.j,y=s|(lambda<<t),b=offset;for(let i=0;i<q;i++)if(bit(y,i))b^=drift[i];
  let f=[];for(let u=0;u<1<<a;u++){let x=b;for(let i=0;i<a;i++)if(bit(u,i))x^=cols[free[i]];
   let yes=true;for(let i=0;i<t;i++)if(bit(s,i))yes&&=!!par((x>>>(i*ell))&lambda);
   f.push(Number(yes));truthChecks++;
  }
  let d=anfDegree(f);assert(d===best.r,"exact degree");assert(f.reduce((a,b)=>a+b,0)===(1<<(a-best.r)),"nonempty uniform fiber");
  if(a>2*ell){assert(d>=3,"terminal degree obstruction");strictDegree++}
  if(p)paired++;maxDegree=Math.max(maxDegree,d);profiles++;
  // Hard incidence: arbitrary satisfying affine map sample. Freeze one true
  // signed literal per clause at a known satisfying point, leaving a flat.
  if(t>=3){let groups=Math.floor(t/3),D0=3*groups*ell,witness=Array.from({length:1<<(ell-1)},()=>rnd(2)),x0=0;
   for(let g=0;g<groups;g++){let v=rnd(witness.length),index=2*v+(1^witness[v]);x0|=index<<(3*g*ell);for(let j=1;j<3;j++)x0|=rnd(1<<ell)<<((3*g+j)*ell)}
   let d0=Math.min(D0,m),C=[];while(C.length<d0){let v=1+rnd((1<<D0)-1);if(rank(C.concat(v))>C.length)C.push(v)}
   let mask=0;for(let g=0;g<groups;g++)mask|=((1<<ell)-1)<<(3*g*ell);let rs=rank(C.map(x=>x&mask)),cnt=0;
   for(let u=0;u<1<<d0;u++){let x=x0;for(let i=0;i<d0;i++)if(bit(u,i))x^=C[i];if((x&mask)!==(x0&mask))continue;cnt++;for(let g=0;g<groups;g++){let index=(x>>>(3*g*ell))&((1<<ell)-1);assert((witness[index>>1]^(index&1))===1,"frozen literal")}}
   assert(cnt===1<<(d0-rs)&&d0-rs>=d0-groups*ell,"certificate flat");minFlatChecks++;
  }
 }
 // Simultaneous protected parameter exchange through sparse XOR equations.
 let pivots=0,assignments=0,unique=0,potentialChecks=0,rejected=0,phaseChecks=0;
 for(let z=0;z<600;z++){
  let m=3+rnd(3),q=1+rnd(2),n=m+q,p=rnd(2),r=2+rnd(4),P=Array.from({length:n},(_,i)=>i),paired=new Set(p?[0,1]:[]),U=Array.from({length:m},(_,i)=>i).filter(i=>!paired.has(i));
  if(U.length<2){rejected++;continue}
  let E=[],lin=Array.from({length:n},(_,i)=>({v:1<<i,c:0}));
  for(let i=0;i<r;i++){let a=rnd(n+i),b=rnd(n+i);while(a===b)b=rnd(n+i);let c=rnd(2);E.push({i:n+i,a,b,c});lin.push({v:lin[a].v^lin[b].v,c:lin[a].c^lin[b].c^c})}
  let a=n+r-1,b=n+r-2,alpha=rnd(2),beta=rnd(2),gamma=rnd(2),pivot=null;
  for(let i of U)for(let j of U)if(i<j&&((bit(lin[a].v,i)&bit(lin[b].v,j))^(bit(lin[a].v,j)&bit(lin[b].v,i))))pivot=[i,j];
  if(!pivot){rejected++;continue}
  let [i,j]=pivot,oldAux=Array.from({length:r},(_,k)=>n+k),newAux=oldAux.filter(v=>v!==a&&v!==b).concat(i,j),newPar=P.filter(v=>v!==i&&v!==j).concat(a,b),other=rnd(n+r-2);
  let countUsed=(params,pairs,withG)=>params.filter(v=>v<m||v===a||v===b).filter(v=>!pairs.has(v)).filter(v=>E.some(e=>[e.i,e.a,e.b].includes(v))||(withG&&[a,b,other].includes(v))||(!withG&&v===other)).length;
  // Before exchange only old data variables are parameters; afterwards a,b
  // are paired. Existing protected metadata are never in the data weight.
  let I=countUsed(P,paired,true),newPairs=new Set([...paired,a,b]),I2=countUsed(newPar,newPairs,false);
  assert(I2<=I-2,"data weight");let W=r+2+4*p+6*I,W2=r+4*(p+1)+6*I2;assert(W2-W<=-10,"pair potential");potentialChecks++;
  for(let x=0;x<1<<n;x++){
   let w=Array.from({length:n},(_,k)=>bit(x,k));for(let e of E)w[e.i]=w[e.a]^w[e.b]^e.c;
   if(p&&w[0]&&w[1])continue;
   let code=newPar.map(v=>w[v]^(v===a?alpha:v===b?beta:0));if(code[code.length-1]&&code[code.length-2])continue;
   let sols=0,solution=null;for(let y=0;y<1<<r;y++){let v=[];for(let k=0;k<newPar.length;k++){let id=newPar[k];v[id]=code[k]^(id===a?alpha:id===b?beta:0)}for(let k=0;k<r;k++)v[newAux[k]]=bit(y,k);
    if(E.every(e=>(v[e.i]^v[e.a]^v[e.b])===e.c)){sols++;solution=v}
   }
   assert(sols===1&&solution.every((v,k)=>v===w[k]),"fair exchange");unique++;
   assert(Array.from({length:q},(_,k)=>solution[m+k]).every((v,k)=>v===bit(x,m+k)),"protected query");
   let G=((w[a]^alpha)&(w[b]^beta))^gamma,old=G^w[other],now=gamma^solution[other];assert(G===gamma&&old===now,"pair gate deletion");phaseChecks++;assignments++;
  }
  pivots++;
 }
 return {seed:870065,profiles,paired,truthChecks,strictDegree,maxDegree,minFlatChecks,pivots,assignments,unique,potentialChecks,rejected,phaseChecks}
}
console.log(JSON.stringify(replay(),null,2));

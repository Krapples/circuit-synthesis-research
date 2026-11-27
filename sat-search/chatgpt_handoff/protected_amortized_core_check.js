"use strict";
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};let seed=870068;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const bit=(x,i)=>(x>>>i)&1,par=x=>{let p=0;while(x){x&=x-1;p^=1}return p};
 function rank(rows){let b=[];for(let v of rows){for(let j=31;j>=0&&v;j--)if(bit(v,j)){if(b[j])v^=b[j];else{b[j]=v;break}}}return b.filter(Boolean).length}
 function hard(x,groups,l){let P=1<<l;for(let w=0;w<1<<(P/2);w++){let ok=true;for(let g of groups){let c=false;for(let j=0;j<3;j++){let a=(x>>>((3*g+j)*l))&(P-1);c||=!!(bit(w,a>>1)^(a&1))}ok&&=c}if(ok)return true}return false}
 function satFull(x,active,m,l){let P=1<<l;for(let w=0;w<1<<(P/2);w++){let ok=true;for(let g=0;g<m;g++){if(!active.includes(g))continue;let c=false;for(let j=0;j<3;j++){let a=(x>>>((3*g+j)*l))&(P-1);c||=!!(bit(w,a>>1)^(a&1))}ok&&=c}if(ok)return true}return false}
 let cases=0,assignments=0,cores=0,strict=0,empty=0,hardChecks=0,degreeChecks=0,pivotChecks=0,optimal=0;
 for(let z=0;z<500;z++){
 let m=2+rnd(3),l=1+rnd(2),D=3*m*l,r=rnd(Math.min(D,5)+1),q=3*m+l+1,rows=[];
 while(rows.length<r){let v=1+rnd((1<<D)-1);if(rank(rows.concat(v))>rows.length)rows.push(v)}
 let drift=rows.map(()=>rnd(1<<q)),b=rows.map(()=>rnd(2));
 let columns=Array.from({length:D},(_,i)=>rows.reduce((v,a,j)=>v|(bit(a,i)<<j),0));
 // Exact small group cover optimum, also compare simple coordinate basis.
 let piv=[],vs=[];for(let i=0;i<D;i++)if(rank(vs.concat(columns[i]))>vs.length){piv.push(i);vs.push(columns[i])}
 let greedy=new Set(piv.map(i=>Math.floor(i/(3*l))));assert(greedy.size<=r,"coordinate cover");
 let best=null;for(let s=0;s<1<<m;s++){let gs=Array.from({length:m},(_,i)=>i).filter(i=>bit(s,i));if(best&&gs.length>=best.length)continue;if(rank(columns.filter((_,i)=>bit(s,Math.floor(i/(3*l)))))===r)best=gs}
 assert(best&&best.length<=greedy.size,"optimal cover");if(best.length<greedy.size)strict++;optimal++;
 let active=Array.from({length:m},(_,i)=>i).filter(i=>!best.includes(i)),pivot=[],basis=[];for(let i=0;i<D;i++)if(best.includes(Math.floor(i/(3*l)))&&rank(basis.concat(columns[i]))>basis.length){pivot.push(i);basis.push(columns[i])}
 assert(pivot.length===r&&active.length>=Math.max(0,m-r),"core bound");pivotChecks++;
 let y=0;for(let i of active)for(let j=0;j<3;j++)y|=1<<(3*i+j); // p=0, lambda=0
 let rhs=b.reduce((v,a,j)=>v|((a^par(drift[j]&y))<<j),0);
 let free=Array.from({length:D},(_,i)=>i).filter(i=>!pivot.includes(i)),core=free.filter(i=>active.includes(Math.floor(i/(3*l))));
 if(!active.length)empty++;else cores++;
 for(let t=0;t<32;t++){let x=0;for(let i of free)x|=rnd(2)<<i;let residual=rhs;for(let i of free)if(bit(x,i))residual^=columns[i];let sol=-1;
 for(let v=0;v<1<<r;v++){let a=0;for(let j=0;j<r;j++)if(bit(v,j))a^=basis[j];if(a===residual){assert(sol===-1,"unique pivot");sol=v}}
 assert(sol>=0,"exists");for(let j=0;j<r;j++)x|=bit(sol,j)<<pivot[j];for(let j=0;j<r;j++)assert(par(rows[j]&x)===(b[j]^par(drift[j]&y)),"affine equation");
 let c=core.reduce((a,i)=>a|(bit(x,i)<<i),0);assert(hard(c,active,l)===satFull(x,active,m,l),"hard core");hardChecks++;assignments++;
 }
 // Hard core AND restriction: one pinned positive witness, each other
 // clause uses two negative literals and a programmable polarity.
 if(active.length>=2){let k=active.length-1,base=0;for(let j=1;j<active.length;j++)base|=(1<<(3*active[j]*l+l))|(1<<(3*active[j]*l+2*l));
 for(let u=0;u<1<<k;u++){let x=base;for(let j=0;j<k;j++)x|=bit(u,j)<<(3*active[j+1]*l);assert(hard(x,active,l)===(u===0),"hard mode AND complement");degreeChecks++}}
 cases++;
 }
 // Exact selector-only counterexample: output AND_i (not s_i or x_i).
 // Setting x_i=1 deletes its clause and one conjunction gate until last.
 let negative=0,negativeTruth=0;for(let D=2;D<=7;D++){let gates=2*D-1;for(let k=0;k<D-1;k++){assert(gates===2*(D-k)-1,"rank-one chain");for(let x=0;x<1<<(D-k);x++)for(let s=0;s<1<<(D-k);s++){let f=!(s&~x),g=!(s&~(x|1));assert(g===!((s>>1)&~(x>>1)),"restriction");negativeTruth++}gates-=2;negative++}}
 return {seed:870068,cases,assignments,cores,empty,strict,hardChecks,degreeChecks,pivotChecks,optimal,negative,negativeTruth}
}
console.log(JSON.stringify(replay(),null,2));

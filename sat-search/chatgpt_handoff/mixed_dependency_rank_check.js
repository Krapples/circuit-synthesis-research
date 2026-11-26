"use strict";
// Exact finite replay. Run node mixed_dependency_rank_check.js.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870032;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const bit=i=>1n<<BigInt(i);
 function basis(vs){let p=new Map;for(let v of vs){while(v){let j=v.toString(2).length-1;if(p.has(j))v^=p.get(j);else{p.set(j,v);break}}}return [...p.values()]}
 const rank=vs=>basis(vs).length,span=(B,v)=>rank([...B,v])===B.length;
 const products=(A,B)=>A.flatMap(a=>B.map(b=>a&b));
 const cap=(r,k)=>k===0?r+2:k===1?2*r+2:3*r+2+r*(r-1)/2;
 let circuits=0,gateChecks=0,rowTransfers=0,colTransfers=0,componentChecks=0,rankCounts=[0,0,0],strict=0;
 function check(d,k,g,out){
  const N=1<<d,Q=1<<k,off=1+d+k,fullX=(1n<<BigInt(N))-1n;
  const support=[0,...Array(d).fill(1),...Array(k).fill(2)],ids=[],preds=[];
  for(let i=0;i<g.length;i++){
   let [a,b]=g[i],s=0,am=0n,bm=0n;
   for(let j=0;j<off+i;j++)if((a|b)&bit(j)){s|=support[j];if(j>=off&&support[j]===3){if(a&bit(j))am|=bit(j-off);if(b&bit(j))bm|=bit(j-off)}}
   support.push(s);preds.push([am,bm]);if(s===3)ids.push(i)
  }
  const xor=(mask,w)=>{let v=0n;for(let j=0;j<w.length;j++)if(mask&bit(j))v^=w[j];return v};
  const data=Array.from({length:d},(_,j)=>{let v=0n;for(let x=0;x<N;x++)if(x>>j&1)v|=bit(x);return v});
  let rows=Array.from({length:Q},(_,q)=>{let w=[fullX,...data,...Array.from({length:k},(_,j)=>q>>j&1?fullX:0n)],ops=[];for(let [u,v] of g){let a=xor(u,w),b=xor(v,w);ops.push([a,b]);w.push(a&b)}return {w,ops,out:xor(out,w)}});
  const pure=(T,q)=>T[q]&1n?fullX:0n;
  const mixed=T=>T.map((v,q)=>v^T[0]^pure(T,q)^pure(T,0));
  const transpose=T=>Array.from({length:N},(_,x)=>{let v=0n;for(let q=0;q<Q;q++)if(T[q]&bit(x))v|=bit(q);return v});
  const R=T=>basis(mixed(T)),C=T=>basis(transpose(mixed(T)));
  const anchorData=T=>T[0]^pure(T,0),anchorQuery=T=>{let v=0n;for(let q=0;q<Q;q++)if((T[q]^T[0])&1n)v|=bit(q);return v};
  let U=[],V=[],bound=0,each=[],byGate=new Map;
  for(let i of ids){
   const [am,bm]=preds[i],rho=rank([am,bm]);rankCounts[rho]++;
   let T=rows.map(r=>r.ops[i][0]),S=rows.map(r=>r.ops[i][1]);
   if(am===bm&&am!==0n)S=S.map((v,q)=>v^T[q]^fullX);
   else if(am===0n&&bm!==0n){let tmp=T;T=S;S=tmp;}
   let P=anchorData(T),A=anchorData(S),B=anchorQuery(S),D=anchorQuery(T);
   let H=R(T),K=R(S),J=C(T),L=C(S);
   let G=rows.map(r=>r.w[off+i]),gu=R(G),gv=C(G);
   assert(gu.length===gv.length,"mixed rank");
   let ub,vb;
   if(rho<=1){
     assert(K.length===0&&L.length===0,"normalization");
     ub=basis([P,A,...H,...H.map(h=>h&A)]);
     vb=basis([D,B,...J,...J.map(h=>h&B)]);
   }else{
     ub=basis([P,A,...H,...K,...K.map(h=>h&P),...H.map(h=>h&A),...products(H,K)]);
     vb=basis([D,B,...J,...L,...L.map(h=>h&D),...J.map(h=>h&B),...products(J,L)]);
   }
   for(let v of gu){assert(span(ub,v),"row transfer");rowTransfers++}
   for(let v of gv){assert(span(vb,v),"column transfer");colTransfers++}
   assert(H.every(h=>span(U,h))&&K.every(h=>span(U,h))&&J.every(h=>span(V,h))&&L.every(h=>span(V,h)),"previous span");
   let newU=basis([...U,...gu]),newV=basis([...V,...gv]);
   assert(newU.length<=cap(U.length,rho)&&newV.length<=cap(V.length,rho),"prefix cap");
   U=newU;V=newV;bound=cap(bound,rho);
   each.push({rho,rank:gu.length,rowUnion:U.length,colUnion:V.length,bound});byGate.set(i,{rho});gateChecks++;
  }
  let actual=R(rows.map(r=>r.out)).length;
  assert(actual<=Math.min(U.length,V.length,bound),"output");
  let parent=new Map(ids.map(i=>[i,i]));
  const root=i=>parent.get(i)===i?i:root(parent.get(i));
  for(let i of ids)for(let j of ids)if(j<i&&((preds[i][0]|preds[i][1])&bit(j)))parent.set(root(i),root(j));
  const comps=new Map;
  for(let i of ids){let rt=root(i);if(!comps.has(rt))comps.set(rt,[]);comps.get(rt).push(i)}
  let cb=0;
  for(let I of comps.values()){let b=0;for(let i of I)b=cap(b,byGate.get(i).rho);cb+=b;componentChecks++}
  assert(actual<=cb,"component bound");
  if(cb<bound)strict++;
  circuits++;return {d,k,t:ids.length,actual,bound,componentBound:cb,each};
 }
 for(let z=0;z<320;z++){
   let d=1+rnd(4),k=1+rnd(4),n=1+rnd(7),off=1+d+k,g=[];
   for(let i=0;i<n;i++){
     let m=()=>BigInt(rnd(1<<(off+i)));
     if(z%3===0){let last=i?bit(off+i-1):0n;g.push([BigInt(rnd(1<<off))^last,BigInt(rnd(1<<off))])}
     else g.push([m(),m()])
   }
   check(d,k,g,BigInt(rnd(1<<(off+n))))
 }
 const chains=[];
 for(let t=1;t<=4;t++){
   const d=2*t,k=2*t,off=1+d+k,g=[];
   for(let i=0;i<t;i++){
     let a=bit(1+2*i),c=bit(2+2*i),b=bit(1+d+2*i),e=bit(2+d+2*i);
     g.push([a^b^(i?bit(off+i-1):0n),c^e])
   }
   let r=check(d,k,g,bit(off+t-1));assert(r.actual===2**(t+1)-2&&r.bound===r.actual,"tight chain");chains.push({t,rank:r.actual});
 }
 const norm=check(4,4,[[bit(1)^bit(5),bit(2)^bit(6)],[bit(9)^bit(3)^bit(7),bit(9)^bit(4)^bit(8)]],bit(10));
 assert(norm.each[1].rho===1&&norm.actual===6,"same-dependency control");
 let supports=[1,2,4,8,3,5,9],diagRank=rank(supports.map(m=>bit(m)));
 assert(diagRank===7&&diagRank<=8&&diagRank>6,"strict target");
 let m=2,l=3,N=1<<(m*l),Q=1<<(m+l);
 let T=Array.from({length:Q},(_,q)=>{let v=0n;for(let x=0;x<N;x++){let f=false;for(let j=0;j<l;j++)if(q>>(m+j)&1){let ok=true;for(let i=0;i<m;i++)if((q>>i&1)&&!(x>>(i*l+j)&1))ok=false;if(ok)f=true}if(f)v|=bit(x)}return v});
 let all=(1n<<BigInt(N))-1n;
 let mixed=T.map(v=>v^T[0]^((v^T[0])&1n?all:0n));
 let wr=rank(mixed),fr=rank(T.map(v=>v^T[0]));
 assert(wr===21&&fr===22&&wr>14&&fr<=27,"packed witness");
 return {seed:870032,circuits,gateChecks,rowTransfers,colTransfers,componentChecks,rankCounts,componentStrict:strict,chains,norm,diagonalTargetRank:diagRank,packed:{m,l,mixedRank:wr,fullRank:fr,rankOneCap:14}};
}
console.log(JSON.stringify(replay(),null,2));

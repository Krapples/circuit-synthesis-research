"use strict";
// Exact quadratic parallel-fiber compatibility and graph-selector regression.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870042;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 const bit=i=>1n<<BigInt(i);
 function rank(vs){let p=new Map;for(let v of vs)while(v){let b=v&-v;if(p.has(b))v^=p.get(b);else{p.set(b,v);break}}return p.size}
 function spaces(n){let out=[];for(let d=0;d<=n;d++){function go(P,start){if(P.length===d){let mask=P.reduce((a,p)=>a|(1<<p),0),B=P.map(p=>1<<p);function fill(i){if(i===d){let K=[0];for(let b of B)K.push(...K.map(x=>x^b));out.push({B:B.slice(),K,d});return}let free=((1<<n)-1)^((1<<(P[i]+1))-1);free&=~mask;for(let s=free;;s=(s-1)&free){B[i]=(1<<P[i])|s;fill(i+1);if(!s)break}}fill(0);return}for(let p=start;p<=n-(d-P.length);p++)go(P.concat(p),p+1)}go([],0)}return out}
 function model(n,polys){let N=1<<n,F=polys.map(fs=>fs.map(h=>Array.from({length:N},(_,x)=>h.reduce((v,m)=>v^Number((x&m)===m),0)))),P=F.map(fs=>fs.map(f=>Array.from({length:N},(_,a)=>Array.from({length:N},(_,b)=>f[a^b]^f[a]^f[b]^f[0]))));return {F,P,N,n,q:F.length,o:F[0].length}}
 function iso(C,B){return C.P.every(ps=>ps.every(p=>B.every(a=>B.every(b=>!p[a][b]))))}
 function exact(C,B){let set=null;for(let fs of C.F){let S=new Set;for(let c=0;c<C.N;c++){let s=0;for(let j=0;j<C.o;j++)for(let i=0;i<B.length;i++)if(fs[j][c^B[i]]^fs[j][c])s|=1<<(j*B.length+i);S.add(s)}set=set===null?S:new Set([...set].filter(x=>S.has(x)));if(!set.size)return false}return true}
 function linear(C,B){let d=B.length,m=C.o*d+C.q*C.n,rows=[];
  for(let q=0;q<C.q;q++)for(let j=0;j<C.o;j++)for(let i=0;i<d;i++){
   let v=bit(j*d+i),a=B[i];for(let k=0;k<C.n;k++)if(C.P[q][j][1<<k][a])v|=bit(C.o*d+q*C.n+k);
   if(C.F[q][j][a]^C.F[q][j][0])v|=bit(m);rows.push(v)
  }return rank(rows)===rank(rows.map(v=>v&(bit(m)-1n)))
 }
 let S4=spaces(4),comparisons=0,scalar=0,vector=0,strict=0,strictRadical=0,profiles={},example=null;
 function analyze(C,S){
  let A=Array.from({length:C.N},(_,i)=>i).filter(a=>C.P.every(ps=>ps.every(p=>p[a].every(v=>!v))));
  let E=A.filter(a=>C.F.every(fs=>fs.every((f,j)=>(f[a]^f[0])===(C.F[0][j][a]^C.F[0][j][0]))));
  let maxIso=0,maxRad=0,maxExact=0;
  for(let {B,K,d} of S){
   if(!iso(C,B))continue;
   maxIso=Math.max(maxIso,d);
   if(K.every(x=>!A.includes(x)||E.includes(x)))maxRad=Math.max(maxRad,d);
   let e=exact(C,B),l=linear(C,B);assert(e===l,"coset compatibility");
   if(e){assert(K.every(x=>!A.includes(x)||E.includes(x)),"common radical");maxExact=Math.max(maxExact,d)}
   comparisons++;
  }
  assert(maxExact<=maxRad&&maxRad<=maxIso,"nested maxima");
  return {maxIso,maxRad,maxExact,A:A.length,E:E.length};
 }
 for(let z=0;z<480;z++){let o=z<320?1:2,q=3+rnd(2),polys=Array.from({length:q},()=>Array.from({length:o},()=>{let h=[];for(let m=1;m<16;m++)if(pc(m)<=2&&rnd(2))h.push(m);if(!h.some(m=>pc(m)===2))h.push(3);return h}));
  let v=analyze(model(4,polys),S4);if(o===1)scalar++;else vector++;
  if(v.maxExact<v.maxIso)strict++;
  if(v.maxExact<v.maxRad){strictRadical++;if(!example&&o===1)example={polys,v}}
  let k=[o,v.maxIso,v.maxRad,v.maxExact].join(",");profiles[k]=(profiles[k]||0)+1;
 }
 assert(example,"strict example");
 // Remove unnecessary query contexts and terms while retaining no affine residuals and strict compatibility gap.
 let p=example.polys.map(fs=>fs.map(h=>h.slice())),changed=true;
 function gap(p){if(p.length<2||p.some(fs=>fs.some(h=>!h.some(m=>pc(m)===2))))return false;let v=analyze(model(4,p),S4);return v.maxExact<v.maxRad&&v.A===1}
 while(changed){changed=false;for(let q=0;q<p.length;q++){let c=p.filter((_,i)=>i!==q);if(gap(c)){p=c;changed=true;break}}if(changed)continue;
  outer:for(let q=0;q<p.length;q++)for(let i=0;i<p[q][0].length;i++){let c=p.map(fs=>fs.map(h=>h.slice()));c[q][0].splice(i,1);if(gap(c)){p=c;changed=true;break outer}}}
 example={polys:p,v:analyze(model(4,p),S4)};
 // Exact graph-selector common-isotropy / affine-fiber dimension.
 let graphCases=0,graphSubspaces=0,rook=[];
 function graph(n,edges,tag){let C=model(n,edges.map(([i,j,or])=>[[...(or?[1<<i,1<<j]:[]),(1<<i)|(1<<j)]]));if(!edges.length)return;
  let alpha=0;for(let x=0;x<1<<n;x++)if(edges.every(([i,j])=>!(x>>i&1)||!(x>>j&1)))alpha=Math.max(alpha,pc(x));
  let mi=0,mf=0;
  for(let {B,K,d} of spaces(n)){
   let active=0;for(let a of B)active|=a;
   // Each active endpoint defines a nonzero linear coordinate form on K.
   let form=Array.from({length:n},(_,i)=>B.reduce((v,b,j)=>v|((b>>i&1)<<j),0));
   let predicted=edges.every(([i,j])=>!form[i]||!form[j]||form[i]===form[j]);
   let actual=iso(C,B);assert(predicted===actual,"graph isotropy");
   if(actual){mi=Math.max(mi,d);let f=linear(C,B);assert(f===exact(C,B),"graph coset");if(f)mf=Math.max(mf,d);assert(d<=alpha,"independence cap")}
   graphSubspaces++;
  }
  assert(mi===alpha&&mf===alpha,"graph maximum");
  graphCases++;if(tag)rook.push({tag,n,edges:edges.length,alpha,maxIso:mi,maxFiber:mf,lower:n-alpha});
 }
 let edges=[];for(let i=0;i<4;i++)for(let j=i+1;j<4;j++)edges.push([i,j]);
 for(let m=1;m<64;m++)graph(4,edges.filter((_,i)=>m>>i&1).map(([i,j])=>[i,j,rnd(2)]));
 for(let z=0;z<12;z++){let e=[];for(let i=0;i<5;i++)for(let j=i+1;j<5;j++)if(rnd(2))e.push([i,j,rnd(2)]);if(e.length)graph(5,e)}
 for(let [m,l] of [[2,2],[2,3]]){let e=[];for(let i=0;i<m;i++)for(let j=0;j<l;j++){for(let k=i+1;k<m;k++)e.push([i*l+j,k*l+j,0]);for(let k=j+1;k<l;k++)e.push([i*l+j,i*l+k,1])}graph(m*l,e,m+"x"+l)}
 return {seed:870042,scalar,vector,comparisons,strict,strictRadical,profiles,example,graphCases,graphSubspaces,rook};
}
console.log(JSON.stringify(replay(),null,2));

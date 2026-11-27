"use strict";
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};
 let seed=870051;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function build(N,K){
  let V=0,C=[],edges=[],newv=()=>V++,f=newv(),s=Array.from({length:N},newv);
  const p=v=>2*v,neg=v=>2*v+1,cl=(...a)=>{while(a.length<3)a.push(p(f));C.push(a)};
  cl(neg(f),neg(f),neg(f));
  for(let i=0;i<N;i++)for(let j=i+1;j<N;j++){
   let a=newv(),slot=C.length*3;cl(p(a));edges.push({i,j,slot,a});cl(neg(s[i]),neg(s[j]),neg(a));
  }
  let prev=Array.from({length:K+1},(_,j)=>j===0?neg(f):p(f));
  for(let i=0;i<N;i++){
   let next=[neg(f)];for(let j=1;j<=K;j++){
    let y=p(newv()),a=prev[j],b=prev[j-1],x=p(s[i]);cl(a^1,y);cl(b^1,x^1,y);cl(y^1,a,b);cl(y^1,a,x);next.push(y);
   }prev=next;
  }cl(prev[K]);
  let m=2;while(m<Math.max(C.length,2*V))m*=2;
  while(C.length<m)C.push([p(f),neg(f),p(f)]);
  let ell=Math.log2(m),P=m,Q=1;while(Q<(3*m+2)*P+3*m+1)Q*=2;
  let w=Q.toString(2).length,base=Q+(3*m+2)*P,mode=base+3*m;
  function encode(x){
   let data=C.flat();for(let i=0;i<edges.length;i++)data[edges[i].slot]^=x>>i&1;
   let W=[],pos=[];
   const lit=(v,s)=>{assert(v.toString(2).length===w,"width");W.push(1,s);for(let j=0;j<w;j++)W.push(1,(v>>j)&1);W.push(0,1)};
   const clause=A=>{for(let [v,s] of A)lit(v,s);W.push(0,0)};
   for(let a=0;a<P;a++)clause([[Q+a,0]]);
   for(let a=0;a<P;a+=2){clause([[Q+P+a,1],[Q+P+a+1,1]]);clause([[Q+P+a,0],[Q+P+a+1,0]])}
   clause([[mode,0]]);
   for(let j=0;j<m;j++){let z=base+3*j;clause([[z,1],[z+1,1],[z+2,1]]);
    for(let a=0;a<3;a++){let i=3*j+a;clause([[mode,0],[z+a,1]]);lit(z+a,0);pos[i]=W.length+3;lit(Q+P+data[i],1);W.push(0,0)}
   }
   assert(W.length===(3*P+15*m+1)*(2*w+4)+2*(2*P+7*m+1),"length");return {W,pos:edges.map(e=>pos[e.slot]),data};
  }
  return {N,K,V,C,edges,m,ell,encode}
 }
 function parse(W){let C=[],a=[],i=0;while(i<W.length){if(!W[i]){assert(W[i+1]===0&&a.length,"end");C.push(a);a=[];i+=2;continue}let s=W[i+1],v=0,p=1;i+=2;while(W[i]){v+=p*W[i+1];p*=2;i+=2}assert(W[i+1]===1&&v>=p/2,"literal");i+=2;a.push([v,s])}assert(!a.length,"complete");return C}
 function sat(C){while(true){if(C.some(a=>!a.length))return false;if(!C.length)return true;let a=C.find(a=>a.length===1);if(!a)break;let [v,s]=a[0];C=C.filter(a=>!a.some(([u,t])=>u===v&&s===t)).map(a=>a.filter(([u])=>u!==v))}
  let [v]=C.reduce((a,b)=>a.length<=b.length?a:b)[0];return [0,1].some(s=>sat([...C,[[v,s]]]))}
 function clique(B,x){for(let S=0;S<1<<B.N;S++){let n=0;for(let t=S;t;t&=t-1)n++;if(n>=B.K&&B.edges.every(({i,j},e)=>!(S>>i&1)||!(S>>j&1)||(x>>e&1)))return true}return false}
 let words=0,mutations=0,physical=0,yes=0,maxLength=0,configs=[];
 for(let [N,K] of [[3,2],[3,3],[4,2],[4,3],[4,4],[5,3],[6,4]]){
  let B=build(N,K),E=B.edges.length,ref=B.encode(0),cases=N<=4?1<<E:24;
  for(let i=0;i<cases;i++){let x=N<=4?i:rnd(1<<E),W=B.encode(x);assert(sat(parse(W.W))===clique(B,x),"clique physical SAT");if(clique(B,x))yes++;words++;maxLength=Math.max(maxLength,W.W.length);
   for(let j=0;j<E;j++){assert(W.W[W.pos[j]]===(x>>j&1),"positive physical edge");physical++}
   let e=rnd(E),T=B.encode(x^(1<<e));assert(W.W.every((b,j)=>j===W.pos[e]?b!==T.W[j]:b===T.W[j]),"single copy");mutations++;
  }configs.push({N,K,m:B.m,ell:B.ell,length:ref.W.length,cases})
 }
 let dnfCases=0,maskChecks=0,coverChecks=0,termChecks=0;
 for(let z=0;z<160;z++){
  let n=3+rnd(4),N=1<<n,full=N-1,pc=x=>{let s=0;for(;x;x&=x-1)s++;return s};
  let raw=Array.from({length:1+rnd(8)},()=>1+rnd(full)),min=[...new Set(raw)].filter(a=>!raw.some(b=>a!==b&&(a&b)===b));
  let f=x=>min.some(a=>(x&a)===a),terms=[];
  for(let a of min){let b=rnd(N)&~a;for(let T=b;;T=(T-1)&b){terms.push([a|T,b^T]);if(!T)break}}
  let evalD=x=>terms.some(([a,b])=>(x&a)===a&&!(x&b));
  for(let x=0;x<N;x++)assert(evalD(x)===f(x),"signed DNF function");
  let cov=Array(N).fill(false);
  for(let Z=0;Z<N;Z++){
   let g=x=>terms.some(([a,b])=>!(a&Z)&&(b&Z)===b&&(x&a)===a);
   for(let x=0;x<N;x++){assert(!g(x)||f(x),"mask sound");cov[x]||=g(x);maskChecks++}
   for(let a of min)if(g(a))coverChecks++;
  }
  for(let x=0;x<N;x++)assert(cov[x]===f(x),"mask cover");
  for(let a of min){let w=Math.min(...terms.filter(([p,b])=>(a&p)===p&&!(a&b)).map(([p,b])=>pc(b)));assert(w>=0,"width");termChecks++}
  dnfCases++;
 }
 return {seed:870051,words,yes,physical,mutations,maxLength,configs,dnfCases,maskChecks,coverChecks,termChecks}
}
console.log(JSON.stringify(replay(),null,2));

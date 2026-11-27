"use strict";
// Vertex-capacitated dictionary ingress cuts and exact residual code controls.
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};let seed=870059;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function flow(N,arcs,src,dst){
  let n=2*N+2,S=2*N,T=S+1,g=Array.from({length:n},()=>[]);function add(a,b,c){let A={b,c,r:g[b].length},B={b:a,c:0,r:g[a].length};g[a].push(A);g[b].push(B)}
  for(let i=0;i<N;i++)add(2*i,2*i+1,1);for(let [a,b] of arcs)add(2*a+1,2*b,N+1);for(let a of src)add(S,2*a,N+1);for(let a of dst)add(2*a+1,T,N+1);
  let f=0;while(true){let p=Array(n).fill(null),q=[S];p[S]=[-1,-1];for(let j=0;j<q.length&&!p[T];j++)for(let k=0;k<g[q[j]].length;k++){let e=g[q[j]][k];if(e.c&&!p[e.b]){p[e.b]=[q[j],k];q.push(e.b)}}if(!p[T])return f;for(let b=T;b!==S;){let [a,k]=p[b],e=g[a][k];e.c--;g[b][e.r].c++;b=a}f++}
 }
 // Arbitrary signed AIG, data x and independent dictionary bits h, fixed all
 // other inputs if any. Code at ingress uniquely determines residual on x.
 let cases=0,checks=0,strict=0,injective=0,cutChecks=0;
 for(let z=0;z<1600;z++){
  let l=1+rnd(3),P=1<<l,N=l+P,anc=Array.from({length:N},(_,i)=>i<l),g=[],pool=Array.from({length:N},(_,i)=>i),n=3+rnd(18);
  for(let k=0;k<n;k++){let a=pool[rnd(pool.length)],b=pool[rnd(pool.length)];if(a===b){k--;continue}g.push({a,b,pa:rnd(2),pb:rnd(2)});anc.push(anc[a]||anc[b]);pool.push(N+k)}
  let out=N+n-1;if(!anc[out])continue;let live=new Set([out]);for(let j=n-1;j>=0;j--)if(live.has(N+j)){live.add(g[j].a);live.add(g[j].b)}
  let side=new Set,arcs=[];
  for(let j=0;j<n;j++)if(live.has(N+j)){let {a,b}=g[j];if(!anc[N+j])arcs.push([a,N+j],[b,N+j]);else if(anc[a]!==anc[b])side.add(anc[a]?b:a)}
  let src=Array.from({length:P},(_,i)=>l+i),f=flow(N+n,arcs,src,[...side]),res=new Set,codes=new Map;
  for(let h=0;h<1<<P;h++){let code=null,r=0;for(let x=0;x<1<<l;x++){let w=Array.from({length:N},(_,i)=>i<l?(x>>i&1):(h>>(i-l)&1));for(let v of g)w.push((w[v.a]^v.pa)&(w[v.b]^v.pb));let c=[...side].map(i=>w[i]).join("");if(code===null)code=c;else assert(code===c,"side independent");r|=w[out]<<x;checks++}if(codes.has(code))assert(codes.get(code)===r,"code reconstructs");else codes.set(code,r);res.add(r)}
  assert(res.size<=codes.size&&codes.size<=2**f&&f<=side.size,"mincut entropy");if(f<side.size)strict++;if(res.size===2**P){assert(f===P,"universal flow");injective++}cases++;cutChecks++;
 }
 // Deliberately padded side ports: many distinct gates all derive from h0
 // and fixed outside inputs. Unit vertex bottleneck remains one.
 let negative=0;for(let P of [2,4,8,16]){let src=Array.from({length:P},(_,i)=>i),arcs=[],dst=[];for(let i=0;i<2*P;i++){arcs.push([0,P+i]);dst.push(P+i)}assert(flow(3*P,arcs,src,dst)===1,"padding control");negative++}
 return {seed:870059,cases,checks,cutChecks,strict,injective,negative};
}
console.log(JSON.stringify(replay(),null,2));

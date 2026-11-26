// Constructive guard peeling and bounded-primary-read normalization.
function run(){
 const stats={tables:0,subset_tests:0,feasible_sets:0,constructed_peeling_circuits:0,peeling_evaluations:0,peeling_reader_checks:0,masked_circuits:0,masked_evaluations:0,masked_reader_checks:0,max_masked_gates:0,max_peeling_gates:0};
 let seed=870018;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(x,m="assertion failed"){if(!x)throw Error(m);}
 function pop(x){let n=0;while(x){n++;x&=x-1;}return n;}
 function builder(n){
  const mask=(1<<(1<<n))-1,V=[0],E=[],hash=new Map();
  for(let i=0;i<n;i++){let t=0;for(let x=0;x<1<<n;x++)if(x>>i&1)t|=1<<x;V.push(t);}
  const value=l=>V[l>>1]^(l&1?mask:0),prim=i=>2*(i+1);
  function AND(a,b){let v=value(a)&value(b),id=V.length;V.push(v);E.push([a,b]);return 2*id;}
  function OR(a,b){return AND(a^1,b^1)^1;}
  function normalize(out){
   let T=[0,...V.slice(1,n+1)],map=T.map((_,i)=>2*i),F=[],H=new Map();
   for(let i=0;i<T.length;i++){H.set(T[i],2*i);H.set(T[i]^mask,2*i+1);}
   for(let j=0;j<E.length;j++){
    let [a,b]=E[j],v=V[n+1+j],w=H.get(v);
    if(w===undefined){w=2*T.length;T.push(v);F.push([map[a>>1]^(a&1),map[b>>1]^(b&1)]);H.set(v,w);H.set(v^mask,w^1);}
    map.push(w);
   }
   let o=map[out>>1]^(out&1),G=new Set(),read=Array(n).fill(0),stack=[o>>1];
   while(stack.length){let i=stack.pop();if(!i)continue;if(i<=n){read[i-1]++;continue;}if(G.has(i))continue;G.add(i);stack.push(...F[i-n-1].map(v=>v>>1));}
   // Independently evaluate rewired gates.
   let W=T.slice(0,n+1);for(let [a,b] of F)W.push((W[a>>1]^(a&1?mask:0))&(W[b>>1]^(b&1?mask:0)));
   ok(W.every((v,i)=>v===T[i]),"normalization semantics");
   return {truth:W[o>>1]^(o&1?mask:0),size:G.size,read};
  }
  // Synthesize arbitrary function of the supplied literal vector; unspecified keys zero.
  function decoder(wires,ones){
   let out=0;
   for(let key of ones){let z=1;for(let i=0;i<wires.length;i++)z=AND(z,wires[i]^((key>>i&1)?0:1));out=OR(out,z);}
   return out;
  }
  return {n,mask,V,E,prim,AND,OR,value,normalize,decoder};
 }
 function plan(f,n){
  let all=(1<<n)-1,Z=Array.from({length:n},()=>[]),pairs=Array.from({length:n},()=>Array(n).fill(-1)),ess=0;
  const bit=x=>f>>x&1;
  for(let i=0;i<n;i++)for(let x=0;x<=all;x++)if(!(x>>i&1)){if(bit(x)===bit(x^(1<<i)))Z[i].push(x);else ess|=1<<i;}
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)for(let p=0;p<4;p++){
   let good=true;for(let x=0;x<=all&&good;x++)if(!(x&((1<<i)|(1<<j)))){
    let a=[];for(let q=0;q<4;q++)if(q!==p)a.push(bit(x|((q&1)<<i)|((q>>1)<<j)));
    good=a.every(v=>v===a[0]);
   }if(good)pairs[i][j]=p;
  }
  let memo=new Map([[0,[]]]);
  function peel(U){
   if(memo.has(U))return memo.get(U);
   let result=null;
   for(let i=0;i<n&&!result;i++)if(U>>i&1){
    let R=U^(1<<i),C=new Map();
    for(let x of Z[i]){let key=x&~R;C.set(key,(C.get(key)||0)+1);}
    if([...C.values()].some(v=>v===2**pop(R))){let tail=peel(R);if(tail)result=[[i],...tail];}
    for(let j=i+1;j<n&&!result;j++)if((R>>j&1)&&pairs[i][j]>=0){let tail=peel(R^(1<<j));if(tail)result=[[i,j,pairs[i][j]],...tail];}
   }memo.set(U,result);return result;
  }
  return {peel,ess};
 }
 function construct(f,n,U,order,physical){
  const B=physical?builder(n):null,all=(1<<n)-1,bit=x=>f>>x&1;
  let state=Array.from({length:1<<n},()=>0),wires=[],width=0,R=U;
  for(let i=0;i<n;i++)if(!(U>>i&1)){for(let x=0;x<=all;x++)state[x]|=(x>>i&1)<<width;if(B)wires.push(B.prim(i));width++;}
  function verify(){
   let seen=new Map();
   for(let x=0;x<=all;x++){let key=state[x]+":"+(x&R),v=bit(x);if(seen.has(key))ok(seen.get(key)===v,"lost residual");seen.set(key,v);}
  }
  verify();
  for(let g of order){
   let i=g[0],next=Array(1<<n),wire;
   if(g.length===1){
    let active=new Set();for(let x=0;x<=all;x++)if(bit(x)!==bit(x^(1<<i)))active.add(state[x]);
    ok(active.size>0&&active.size<new Set(state).size,"guard must vary");
    if(B)wire=B.AND(B.prim(i),B.decoder(wires,active));
    for(let x=0;x<=all;x++)next[x]=+(active.has(state[x])&&!!(x>>i&1));
    R^=1<<i;
   }else{
    let j=g[1],p=g[2];
    if(B)wire=B.AND(B.prim(i)^((p&1)?0:1),B.prim(j)^((p&2)?0:1));
    for(let x=0;x<=all;x++)next[x]=+(((x>>i&1)|((x>>j&1)<<1))===p);
    R^=(1<<i)|(1<<j);
   }
   if(B){for(let x=0;x<=all;x++)ok((B.value(wire)>>x&1)===next[x],"constructed reader");wires.push(wire);}
   for(let x=0;x<=all;x++)state[x]|=next[x]<<width;width++;verify();
  }
  ok(R===0);
  if(B){
   const ones=new Set(state.filter((v,x)=>bit(x))),o=B.decoder(wires,ones),a=B.normalize(o);
   ok(a.truth===f,"peeling output");for(let i=0;i<n;i++)if(U>>i&1){ok(a.read[i]===1,"single read");stats.peeling_reader_checks++;}
   stats.constructed_peeling_circuits++;stats.peeling_evaluations+=1<<n;stats.max_peeling_gates=Math.max(stats.max_peeling_gates,a.size);
  }
 }
 for(let f=0;f<65536;f++){
  let P=plan(f,4);if(P.ess!==15)continue;stats.tables++;
  for(let U=0;U<16;U++){
   let order=P.peel(U);stats.subset_tests++;if(!order)continue;stats.feasible_sets++;
   construct(f,4,U,order,(f%127===0)||((f===0x17e8||f===0x0016)&&U!==0));
  }
 }
 // Random signed AIG, then two-domain masking with parity anchor.
 for(let trial=0;trial<3000;trial++){
  let n=2+rnd(3),C=builder(n),s=1+rnd(18);
  for(let j=0;j<s;j++)C.AND(2*rnd(C.V.length)+rnd(2),2*rnd(C.V.length)+rnd(2));
  let out=2*(C.V.length-1)+rnd(2),f=C.value(out);
  if(plan(f,n).ess!==(1<<n)-1)continue;
  const B=builder(n),a=B.AND(B.prim(0),B.prim(1)^1),b=B.AND(B.prim(0)^1,B.prim(1)),d=B.AND(B.prim(0),B.prim(1)),p=B.OR(a,b);
  let rails=[];
  for(let phase=0;phase<2;phase++){
   let g=phase?p:p^1,W=[0,phase?a:d,phase?b:d];
   for(let i=2;i<n;i++)W.push(B.AND(g,B.prim(i)));
   function lit(l){return l&1?B.AND(g,W[l>>1]^1):W[l>>1];}
   for(let [u,v] of C.E)W.push(B.AND(lit(u),lit(v)));
   rails.push(lit(out));
  }
  let o=B.OR(...rails),raw=B.E.length,N=B.normalize(o);
  ok(raw<=6*s+2*n+3,"size cap");
  ok(N.truth===f,"masked output");
  for(let i=0;i<n;i++){ok(N.read[i]<=(i<2?3:2),"read cap");stats.masked_reader_checks++;}
  stats.masked_circuits++;stats.masked_evaluations+=1<<n;stats.max_masked_gates=Math.max(stats.max_masked_gates,N.size);
 }
 return stats;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

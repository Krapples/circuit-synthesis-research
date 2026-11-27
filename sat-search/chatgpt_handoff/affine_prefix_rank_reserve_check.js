"use strict";
// Exact prefix reserve checks and quartic two-plane rank controls.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870039;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const bit=i=>1n<<BigInt(i);
 const parity=x=>{let p=0;while(x){x&=x-1;p^=1}return p};
 function basis(vs){let p=new Map;for(let v of vs)while(v){let k=v&-v;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}return [...p.values()]}
 const rank=vs=>basis(vs).length;
 const polyXor=(a,b)=>{let S=new Set(a);for(let m of b)S.has(m)?S.delete(m):S.add(m);return [...S]};
 function diff(h,s){let S=new Set;for(let m of h){let x=m&s;for(let j=x;j;j=(j-1)&x){let v=m^j;S.has(v)?S.delete(v):S.add(v)}}return [...S]}
 function table(f,n){return Uint8Array.from({length:1<<n},(_,x)=>f(x))}
 function anchoredRows(F,K){let rows=[];for(let a of K){let v=0n;for(let x=0;x<F.length;x++)if(F[x^a]^F[x]^F[a]^F[0])v|=bit(x);rows.push(v)}return rows}
 function evalCircuit(n,g,out,x){let w=1|(x<<1);for(let i=0;i<g.length;i++)if(parity(w&g[i][0])&&parity(w&g[i][1]))w|=1<<(1+n+i);return parity(w&out)}
 let circuits=0,flags=0,jointChecks=0,constantGates=0,strictOverComplement=0,maxFlags=0;
 for(let z=0;z<240;z++){
  let n=2+rnd(6),t=1+rnd(6),g=[];
  for(let i=0;i<t;i++)g.push([rnd(1<<(1+n+i)),rnd(1<<(1+n+i))]);
  let out=rnd(1<<(1+n+t)),F=table(x=>evalCircuit(n,g,out,x),n),gs=g.map((_,i)=>table(x=>evalCircuit(n,g,1<<(1+n+i),x),n));
  let K=Array.from({length:1<<n},(_,x)=>x);
  for(let p=0;p<=t;p++){
   if(p){let [a,b]=g[p-1];K=K.filter(x=>!parity(a&(x<<1))&&!parity(b&(x<<1)))}
   let d=Math.log2(K.length);assert(d>=n-2*p,"codimension");
   let R=rank(anchoredRows(F,K)),J=rank([...anchoredRows(F,K),...gs.flatMap(H=>anchoredRows(H,K))]);
   let cap=2**(t-p+1)-2;assert(R<=J&&J<=cap,"joint reserve");
   for(let i=0;i<p;i++){assert(anchoredRows(gs[i],K).every(x=>x===0n),"pure prefix");constantGates++}
   // Compare with a complement chosen greedily; all q is canonical and at least as strong.
   let sub=K.slice(),C=[0];for(let x=1;x<1<<n;x++)if(!sub.includes(x)){sub.push(...sub.map(a=>a^x));C.push(...C.map(a=>a^x))}
   let compRows=K.map(a=>C.reduce((v,x,j)=>F[x^a]^F[x]^F[a]^F[0]?v|bit(j):v,0n));
   let rcomp=rank(compRows);assert(rcomp<=R,"complement pullback");if(rcomp<R)strictOverComplement++;
   flags++;jointChecks++;
  }circuits++;maxFlags=Math.max(maxFlags,t+1);
 }
 function omega(a,b,n){let p=0;for(let i=0;i<n;i+=2)p^=((a>>i&1)&(b>>(i+1)&1))^((a>>(i+1)&1)&(b>>i&1));return p}
 function quartic(n){let h=[];for(let i=0;i<n;i+=2)for(let j=i+2;j<n;j+=2)h.push((3<<i)|(3<<j));return h}
 let pairs=0,polarChecks=0,quarticCases=[];
 for(let n of [4,6,8,10,12]){
  let h=quartic(n),F=n<=8?table(x=>h.reduce((v,m)=>v^Number((x&m)===m),0),n):null,seen=new Set,checks=0;
  let nPairs=n<=8?Infinity:1200,done=false;
  for(let a=1;a<1<<n&&!done;a++)for(let b=a+1;b<1<<n;b++){
   if(checks>=nPairs){done=true;break}
   let c=a^b,key=[a,b,c].sort((u,v)=>u-v).join(",");if(seen.has(key))continue;seen.add(key);
   // For n>=10 use randomized independent pairs instead of lexicographic sample.
   if(n>8){a=a;break}
   let p=diff(diff(h,a),b);assert(p.some(m=>m&&(m&(m-1))),"nonzero quadratic derivative");
   let ps=new Set(p);
   for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let e=1<<i,f=1<<j;
    let w=(omega(a,b,n)&omega(e,f,n))^(omega(a,e,n)&omega(b,f,n))^(omega(a,f,n)&omega(b,e,n));
    assert(ps.has(e|f)===!!w,"polar formula");polarChecks++}
   assert(rank(anchoredRows(F,[0,a,b,c]))===3,"two-flat mixed rank");checks++;pairs++;
  }
  if(n>8){seen.clear();while(checks<1200){let a=1+rnd((1<<n)-1),b=1+rnd((1<<n)-1);if(a===b)continue;let key=[a,b,a^b].sort((u,v)=>u-v).join(",");if(seen.has(key))continue;seen.add(key);let p=diff(diff(h,a),b),ps=new Set(p);assert(p.some(m=>m&&(m&(m-1))),"nonzero sampled derivative");for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let e=1<<i,f=1<<j,w=(omega(a,b,n)&omega(e,f,n))^(omega(a,e,n)&omega(b,f,n))^(omega(a,f,n)&omega(b,e,n));assert(ps.has(e|f)===!!w,"sample polar");polarChecks++}checks++;pairs++}}
  if(n<=8)assert(checks===((1<<n)-1)*((1<<n)-2)/6,"all two planes");
  let coeff=new Map;for(let m of h)for(let a=(m-1)&m;a;a=(a-1)&m)coeff.set(a,(coeff.get(a)||0n)|bit(m^a));let fullRank=rank(coeff.values());
  let aggregate=Math.ceil(Math.log2(fullRank+2))-1;
  quarticCases.push({n,planes:checks,complete:n<=8,fullRank,aggregate,ingress:n/2,newLower:n/2+1});
 }
 return {seed:870039,circuits,flags,jointChecks,constantGates,strictOverComplement,maxFlags,pairs,polarChecks,quarticCases};
}
console.log(JSON.stringify(replay(),null,2));

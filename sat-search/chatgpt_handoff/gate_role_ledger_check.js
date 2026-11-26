// Multi-context ingress ledger: profile relaxation and stable-ID restrictions.
// Run: node gate_role_ledger_check.js
function run(){
 let seed=870016;
 function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(x,m="assertion failed"){if(!x)throw Error(m);}
 function pop(x){let p=0;while(x){p++;x&=x-1;}return p;}
 function canon(x,mask){return Math.min(x,x^mask);}
 // Exact minima through cap; unknowns get cap+1 (valid lower bound).
 function smallCosts(n,cap){
  let mask=(1<<(1<<n))-1,base=[];
  for(let i=0;i<n;i++){let v=0;for(let x=0;x<1<<n;x++)if(x>>i&1)v|=1<<x;base.push(canon(v,mask));}
  base.sort((a,b)=>a-b);let L=Array(mask+1).fill(cap+1),states=new Map([[base.join(","),base]]);
  for(let d=0;d<=cap;d++){
   let next=new Map();
   for(let A of states.values()){
    for(let v of [0,...A])L[v]=L[v^mask]=Math.min(L[v],d);
    if(d===cap)continue;
    for(let i=0;i<A.length;i++)for(let j=i+1;j<A.length;j++)for(let p=0;p<4;p++){
     let v=canon((A[i]^(p&1?mask:0))&(A[j]^(p&2?mask:0)),mask);
     if(!v||A.includes(v))continue;let B=[...A,v].sort((a,b)=>a-b);next.set(B.join(","),B);
    }
   }states=next;
  }return L;
 }
 let costs=[[0,0],smallCosts(1,1),smallCosts(2,3),smallCosts(3,4)];
 function cofactor(f,n,S,z){
  let t=0,ix=[];for(let i=0;i<n;i++)if(S>>i&1)ix.push(i);
  for(let x=0;x<1<<ix.length;x++){let v=z;for(let j=0;j<ix.length;j++)if(x>>j&1)v|=1<<ix[j];if(f>>v&1)t|=1<<x;}return t;
 }
 function demand(f,n,S){let d=0;for(let z=0;z<1<<n;z++)if(!(z&S))d=Math.max(d,costs[pop(S)][cofactor(f,n,S,z)]);return d;}
 function ess(f,n){let s=0;for(let i=0;i<n;i++)for(let x=0;x<1<<n;x++)if(((f>>x)^(f>>(x^(1<<i))))&1){s|=1<<i;break;}return s;}
 const n=4,all=15,pairs=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)pairs.push((1<<i)|(1<<j));
 let profiles=[];
 function gen(pos,left,A){
  if(pos===10){
   let a1=A.slice(0,4),a2=A.slice(4),s1=a1.reduce((a,b)=>a+b,0),s2=a2.reduce((a,b)=>a+b,0);
   if(!s2)return;
   for(let i=0;i<4;i++)if(a1[i]+a2.reduce((s,v,j)=>s+((pairs[j]>>i&1)?v:0),0)<1)return;
   let v=Array(15).fill(0);
   for(let S=1;S<15;S++)v[S]=a1.reduce((s,x,i)=>s+(S>>i&1?x:0),0)+a2.reduce((s,x,i)=>s+((pairs[i]&S)===pairs[i]?x:0),0);
   profiles.push({base:s1+s2,min0:s2-1,v});return;
  }
  for(let i=0;i<=left;i++){A.push(i);gen(pos+1,left-i,A);A.pop();}
 }gen(0,8,[]);
 let stats={full_support_tables:0,demand_profiles:0,ingress_profiles:profiles.length,
   strict_improvements:0,ledger_weaker:0,equal_bounds:0,random_aigs:0,restriction_checks:0,port_checks:0};
 let cache=new Map();
 for(let f=0;f<65536;f++)if(ess(f,n)===all){
  stats.full_support_tables++;
  let L=Array.from({length:15},(_,S)=>S?demand(f,n,S):0),key=L.join(","),v=cache.get(key);
  if(!v){
   let base=Math.max(...L.slice(1).map((x,i)=>x+4-pop(i+1))),bound=Infinity;
   for(let p of profiles){
    if(p.base+p.min0>=bound)continue;let a0=p.min0;
    for(let S=1;S<15;S++)a0=Math.max(a0,L[S]-p.v[S]);
    bound=Math.min(bound,p.base+a0);
   }
   for(let S=1;S<15;S++)ok(L[S]<=base-3+pop(S&12)+((S&3)===3?1:0),"explicit profile");
   ok(bound<=base,"no improvement");v={base,bound};cache.set(key,v);
  }
  if(v.bound>v.base)stats.strict_improvements++;
  else if(v.bound<v.base)stats.ledger_weaker++;
  else stats.equal_bounds++;
 }
 stats.demand_profiles=cache.size;
 function aig(n,g){let E=[];for(let i=0;i<g;i++)E.push([2*rnd(n+i)+rnd(2),2*rnd(n+i)+rnd(2)]);return E;}
 function evalA(E,n,x){let v=Array.from({length:n},(_,i)=>x>>i&1);for(let [a,b] of E)v.push((v[a>>1]^(a&1))&(v[b>>1]^(b&1)));return v;}
 function live(E,n){let S=new Set(),stack=[n+E.length-1];while(stack.length){let v=stack.pop();if(v<n||S.has(v))continue;S.add(v);stack.push(...E[v-n].map(a=>a>>1));}return S;}
 for(let trial=0;trial<500;trial++){
  let n=3+rnd(4),r=2+rnd(Math.min(4,n)-1),block=Array.from({length:n},(_,i)=>i%r),E=aig(n,4+rnd(24)),G=live(E,n),sup=block.map(i=>1<<i);
  for(let [a,b] of E)sup.push(sup[a>>1]|sup[b>>1]);
  let local=Array(r).fill(0),a0=0,a1=Array(r).fill(0),a2=new Map(),ports=Array.from({length:r},()=>new Set());
  for(let g of G){
   let s=sup[g],v=E[g-n].map(a=>a>>1);
   if(pop(s)===1){local[31-Math.clz32(s)]++;continue;}
   let p=v.filter(i=>pop(sup[i])===1);for(let i of p)ports[31-Math.clz32(sup[i])].add(i);
   if(!p.length)a0++;
   if(p.length===1)a1[31-Math.clz32(sup[p[0]])]++;
   if(p.length===2){let mask=sup[p[0]]|sup[p[1]];ok(pop(mask)===2);a2.set(mask,(a2.get(mask)||0)+1);}
  }
  let m=a0+a1.reduce((a,b)=>a+b,0)+[...a2.values()].reduce((a,b)=>a+b,0);
  if(m)ok(a0>=[...a2.values()].reduce((a,b)=>a+b,0)-1,"merge count");
  let vals=Array.from({length:1<<n},(_,x)=>evalA(E,n,x)),f=vals.map(v=>v.at(-1));
  for(let b=0;b<r;b++){
   let mask=block.reduce((m,v,i)=>v===b?m|(1<<i):m,0),rows=new Set();
   for(let x=0;x<1<<n;x++)if(!(x&~mask)){
    let row="";for(let y=0;y<1<<n;y++)if(!(y&mask))row+=f[x|y];rows.add(row);
   }
   if(m)ok(rows.size<=2**ports[b].size,"port count");stats.port_checks++;
  }
  for(let S=1;S<1<<r;S++){
   let cap=a0+local.reduce((v,x,i)=>v+(S>>i&1?x:0),0)+a1.reduce((v,x,i)=>v+(S>>i&1?x:0),0)+[...a2].reduce((v,[mask,x])=>v+((mask&S)===mask?x:0),0);
   let keep=block.reduce((v,b,i)=>v+(S>>b&1?1<<i:0),0);
   for(let z=0;z<1<<n;z++)if(!(z&keep)){
    let w=block.map((b,i)=>S>>b&1?2*(i+1):(z>>i&1)),nodes=[],hash=new Map();
    function AND(a,b,g){
     if(a===0||b===0||a===(b^1))return 0;if(a===1)return b;if(b===1||a===b)return a;
     if(a>b)[a,b]=[b,a];let key=a+","+b;if(hash.has(key))return hash.get(key);
     let v=2*(n+1+nodes.length);nodes.push({a,b,g});hash.set(key,v);return v;
    }
    for(let i=0;i<E.length;i++){let [a,b]=E[i];w.push(G.has(n+i)?AND(w[a>>1]^(a&1),w[b>>1]^(b&1),n+i):0);}
    let stack=[w.at(-1)>>1],seen=new Set();
    while(stack.length){
     let i=stack.pop();if(i<=n||seen.has(i))continue;seen.add(i);
     let p=nodes[i-n-1];stack.push(p.a>>1,p.b>>1);ok(G.has(p.g),"stable ID");
     for(let a of E[p.g-n])if(pop(sup[a>>1])===1)ok((sup[a>>1]&S)!==0,"fixed pure operand");
    }
    ok(seen.size<=cap,"ledger cap");
    // Also compare the restricted symbolic circuit on every remaining input.
    for(let x=0;x<1<<n;x++)if(!(x&~keep)){
     let v=[0,...Array.from({length:n},(_,i)=>x>>i&1)];
     for(let {a,b} of nodes)v.push((v[a>>1]^(a&1))&(v[b>>1]^(b&1)));
     let out=w.at(-1);ok((v[out>>1]^(out&1))===f[x|z],"restricted evaluation");
    }
    stats.restriction_checks++;
   }
  }stats.random_aigs++;
 }return stats;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

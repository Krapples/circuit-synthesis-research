// Joint history-expanded capacity: exact small response vectors and lifted cuts.
function run(){
 let seed=870025;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(v,m="assertion failed"){if(!v)throw Error(m);}
 function sub(m){let a=[];for(let x=m;;x=(x-1)&m){a.push(x);if(!x)return a;}}
 function builder(n,S){
  let E=[],side=S.slice(),xorNodes=new Map();
  function and(a,b,s){let v=2*(n+E.length);E.push([a,b]);side.push(s);return v;}
  function or(a,b,s){return and(a^1,b^1,s)^1;}
  function xor(a,b,s){let l=and(a,b^1,s),r=and(a^1,b,s),v=or(l,r,s);xorNodes.set(v>>1,{a,b,phase:v&1});return v;}
  function mux(q,a,b,s){return or(and(q,b,s),and(q^1,a,s),s);}
  return {n,E,side,xorNodes,and,or,xor,mux};
 }
 function structure(C,S){
  let N=C.side.length,D=Array.from({length:N},()=>new Set()),R=Array.from({length:N},()=>new Set()),F=new Set(),Q=new Set();
  for(let i of S)D[i].add(i);
  for(let j=0;j<C.E.length;j++)for(let l of C.E[j]){
   let u=l>>1,v=C.n+j;if(C.side[u]===0&&C.side[v]===1)F.add(u);
   if(C.side[v]===0){if(C.side[u]===1){R[v].add(u);Q.add(u);}else{for(let x of D[u])D[v].add(x);for(let x of R[u])R[v].add(x);}}
  }
  return {D,R,F:[...F].sort((a,b)=>a-b),Q:[...Q].sort((a,b)=>a-b)};
 }
 // Original live gates are represented by their own IDs. Constants use -2,-1.
 // Aliases and structural hash reuse only earlier original A gates.
 function specialize(C,P,h,affine=false){
  let N=C.side.length,L=Array(N).fill(-2),E=new Map(),hash=new Map(),H=new Map(P.Q.map((v,i)=>[v,(h>>i)&1]));
  function lit(l){let v=l>>1;return (C.side[v]===0?L[v]:-2+(H.get(v)||0))^(l&1);}
  let A=Array(N).fill(null),AH=new Map([[0n,-2],[1n,-1]]);
  function alit(l){let v=l>>1,a=C.side[v]===0?A[v]:BigInt(H.get(v)||0);return a===null?null:a^BigInt(l&1);}
  function affineAnd(u,w){let a=alit(u),b=alit(w);if(a===0n||b===0n)return 0n;if(a===1n)return b;if(b===1n)return a;if(a!==null&&b!==null){if(a===b)return a;if((a^b)===1n)return 0n;}return null;}
  function form(u,w){
   if((u&1)&&(w&1)&&(u>>1)>=C.n&&(w>>1)>=C.n&&C.side[u>>1]===0&&C.side[w>>1]===0){
    let [p,q]=C.E[(u>>1)-C.n],B=C.E[(w>>1)-C.n];
    if((B[0]===(p^1)&&B[1]===(q^1))||(B[1]===(p^1)&&B[0]===(q^1))){let a=alit(p),b=alit(q);if(a!==null&&b!==null)return a^b;}
   }return affineAnd(u,w);
  }
  function AND(a,b,v){
   if(a===-2||b===-2)return -2;if(a===-1)return b;if(b===-1)return a;if(a===b)return a;if(a===(b^1))return -2;
   if(a>b)[a,b]=[b,a];let key=a+","+b;if(hash.has(key))return hash.get(key);
   E.set(v,[a,b]);hash.set(key,2*v);return 2*v;
  }
  for(let v=0;v<C.n;v++)if(C.side[v]===0){L[v]=2*v;if(affine){A[v]=1n<<BigInt(v+1);AH.set(A[v],L[v]);AH.set(A[v]^1n,L[v]^1);}}
  for(let j=0;j<C.E.length;j++){let v=C.n+j;if(C.side[v]!==0)continue;let [u,w]=C.E[j];
   let a=affine?form(u,w):null;A[v]=a;
   if(a!==null&&AH.has(a))L[v]=AH.get(a);else{L[v]=AND(lit(u),lit(w),v);if(a!==null){AH.set(a,L[v]);AH.set(a^1n,L[v]^1);}}
  }
  return {L,E,H};
 }
 function evalLocal(C,P,h,x){
  let N=C.side.length,V=Array(N).fill(0),H=new Map(P.Q.map((v,i)=>[v,(h>>i)&1]));
  for(let i=0;i<C.n;i++)if(C.side[i]===0)V[i]=x>>i&1;
  function lit(l){let v=l>>1;return (C.side[v]===0?V[v]:H.get(v)||0)^(l&1);}
  for(let j=0;j<C.E.length;j++)if(C.side[C.n+j]===0)V[C.n+j]=lit(C.E[j][0])&lit(C.E[j][1]);
  return V;
 }
 function evalCopy(C,T,x){
  let V=Array(C.side.length).fill(0);
  for(let i=0;i<C.n;i++)if(C.side[i]===0)V[i]=x>>i&1;
  function lit(l){return l<0?l+2:V[l>>1]^(l&1);}
  for(let [v,[a,b]] of T.E)V[v]=lit(a)&lit(b);
  return T.L.map(l=>lit(l));
 }
 function network(N){
  let E=Array.from({length:N},()=>[]);
  function edge(u,v,c){let a={v,c,rev:E[v].length},b={v:u,c:0,rev:E[u].length};E[u].push(a);E[v].push(b);}
  function flow(s,t){let f=0;
   for(;;){let P=Array(N).fill(null),Q=[s];P[s]=[-1,-1];
    for(let j=0;j<Q.length;j++){let u=Q[j];for(let i=0;i<E[u].length;i++){let e=E[u][i];if(e.c>1e-8&&!P[e.v]){P[e.v]=[u,i];Q.push(e.v);}}}
    if(!P[t])return f;
    let d=Infinity;for(let v=t;v!==s;){let [u,i]=P[v];d=Math.min(d,E[u][i].c);v=u;}
    for(let v=t;v!==s;){let [u,i]=P[v],e=E[u][i];e.c-=d;E[v][e.rev].c+=d;v=u;}f+=d;
   }
  }return {edge,flow};
 }
 function lifted(C,data,Ts,K,shared){
  let N=C.side.length,H=Ts.length,source=2*N*H+data.length,sink=source+1,G=network(sink+1),inf=(shared?data.length:data.length*H)+1;
  let live=Ts.map(T=>{let L=new Set(),todo=K.map(v=>T.L[v]).filter(l=>l>=0).map(l=>l>>1);
   while(todo.length){let v=todo.pop();if(L.has(v))continue;L.add(v);if(T.E.has(v))todo.push(...T.E.get(v).map(l=>l>>1));}return L;});
  let mult=Array(N).fill(0);
  for(let j=0;j<H;j++)for(let v of live[j])if(v>=C.n)mult[v]++;
  for(let i=0;i<data.length;i++)G.edge(source,2*N*H+i,shared?1:inf);
  let dist=Array(data.length).fill(Infinity);
  for(let j=0;j<H;j++){
   let T=Ts[j],off=2*N*j,L=live[j],sinkSet=new Set(K.map(v=>T.L[v]).filter(l=>l>=0).map(l=>l>>1));
   for(let v of L){
    G.edge(off+2*v,off+2*v+1,1);
    if(T.E.has(v))for(let l of T.E.get(v))G.edge(off+2*(l>>1)+1,off+2*v,inf);
    if(sinkSet.has(v))G.edge(off+2*v+1,sink,inf);
   }
   let d=Array(N).fill(Infinity);for(let v of sinkSet)d[v]=v<C.n?0:1/mult[v];
   for(let v=N-1;v>=C.n;v--)if(L.has(v)&&Number.isFinite(d[v])&&T.E.has(v))for(let l of T.E.get(v)){
    let u=l>>1;d[u]=Math.min(d[u],d[v]+(u<C.n?0:1/mult[u]));
   }
   for(let i=0;i<data.length;i++)if(L.has(data[i])){G.edge(2*N*H+i,off+2*data[i],inf);dist[i]=Math.min(dist[i],d[data[i]]);}
  }
  return {flow:G.flow(source,sink),charge:dist.reduce((a,b)=>a+b,0),liveGates:mult.filter(x=>x>0).length};
 }
 function oldFlow(C,data,P,cap){
  let N=C.side.length,s=2*N,t=s+1,G=network(t+1),inf=data.length+1;
  for(let v=0;v<N;v++)if(C.side[v]===0){G.edge(2*v,2*v+1,cap[v]);if(v>=C.n)for(let l of C.E[v-C.n])if(C.side[l>>1]===0)G.edge(2*(l>>1)+1,2*v,inf);}
  for(let v of data)G.edge(s,2*v,inf);for(let v of P.F)G.edge(2*v+1,t,inf);return G.flow(s,t);
 }
 function full(C,x){let V=Array.from({length:C.n},(_,i)=>x>>i&1);for(let [a,b] of C.E)V.push((V[a>>1]^(a&1))&(V[b>>1]^(b&1)));return V;}
 let S={randomCircuits:0,lookupCircuits:0,formalHistoryCases:0,copyEvaluations:0,affineCopyEvaluations:0,affineStrictCuts:0,jointCutChecks:0,actualReconstructions:0,strictJointVsLocal:0,strictLiftedVsOld:0,strictSharedSourceVsSummed:0,fullChargeChecks:0,examples:[],affineExamples:[]};
 function verify(C,out){
  let n=C.n,N=C.side.length,data=Array.from({length:n},(_,i)=>i).filter(i=>C.side[i]===0),bob=Array.from({length:n},(_,i)=>i).filter(i=>C.side[i]===1),P=structure(C,data);
  if(!data.length||!bob.length||data.length>5||P.Q.length>5||C.side[out>>1]!==1)return false;
  let X=sub(data.reduce((s,v)=>s|1<<v,0)),Y=sub(bob.reduce((s,v)=>s|1<<v,0)),H=2**P.Q.length,Ts=Array.from({length:H},(_,h)=>specialize(C,P,h)),As=Array.from({length:H},(_,h)=>specialize(C,P,h,true));
  let W=X.map(x=>Ts.map((T,h)=>{let a=evalLocal(C,P,h,x),b=evalCopy(C,T,x);for(let v=0;v<N;v++)if(C.side[v]===0)ok(a[v]===b[v],"copy");let c=evalCopy(C,As[h],x);for(let v=0;v<N;v++)if(C.side[v]===0)ok(a[v]===c[v],"affine copy");S.affineCopyEvaluations++;S.copyEvaluations++;return a;}));
  S.formalHistoryCases+=H;
  let fullW=X.map(x=>Y.map(y=>full(C,x|y))),res=fullW.map(row=>row.map(V=>V[out>>1]^(out&1)).join("")),need=Math.log2(new Set(res).size);
  let cap=Array.from({length:N},(_,v)=>C.side[v]===0?Math.log2(new Set(W.map(row=>row.map(V=>V[v]).join(""))).size):0);
  let old=oldFlow(C,data,P,cap),A=C.side.map((s,v)=>s===0?v:-1).filter(v=>v>=0);
  function cut(K){let ks=new Set(K),r=Array(N).fill(false);for(let v of data)r[v]=!ks.has(v);for(let j=0;j<C.E.length;j++){let v=n+j;if(C.side[v]===0&&!ks.has(v))r[v]=C.E[j].some(l=>C.side[l>>1]===0&&r[l>>1]);}return P.F.every(v=>!r[v]);}
  let cuts=[data,P.F];for(let t=0;t<8;t++){let K=A.filter(()=>rnd(3)===0);if(cut(K))cuts.push(K);}
  for(let K of cuts){
   let L=lifted(C,data,Ts,K,true),AF=lifted(C,data,As,K,true),sum=lifted(C,data,Ts,K,false),codes=W.map(row=>row.map(V=>K.map(v=>V[v]).join("")).join("|")),joint=Math.log2(new Set(codes).size),local=K.reduce((s,v)=>s+cap[v],0);
   ok(need<=joint+1e-8&&joint<=local+1e-8&&joint<=L.flow+1e-8&&L.flow<=sum.flow+1e-8,"joint inequality");
   ok(joint<=AF.flow+1e-8,"affine flow");if(AF.flow<L.flow-1e-8)S.affineStrictCuts++;
   if(joint<local-1e-8)S.strictJointVsLocal++;if(L.flow<sum.flow-1e-8)S.strictSharedSourceVsSummed++;
   if(K===P.F&&L.flow<old-1e-8)S.strictLiftedVsOld++;
   if(need===data.length&&K===P.F){ok(L.charge<=L.liveGates+1e-8,"lifted charge");S.fullChargeChecks++;}
   // Simulate original circuit with dummy A data and joint vector at K.
   // At an override, only its actual earlier local reverse history is needed.
   let KS=new Set(K);
   for(let i=0;i<X.length;i++)for(let j=0;j<Y.length;j++){
    let V=Array.from({length:n},(_,v)=>Y[j]>>v&1);
    function at(v){if(!KS.has(v))return;let h=0;for(let t=0;t<P.Q.length;t++)if(P.R[v].has(P.Q[t]))h|=V[P.Q[t]]<<t;V[v]=W[i][h][v];}
    for(let v=0;v<n;v++)at(v);
    for(let g=0;g<C.E.length;g++){let [a,b]=C.E[g];V.push((V[a>>1]^(a&1))&(V[b>>1]^(b&1)));at(n+g);}
    ok((V[out>>1]^(out&1))===(fullW[i][j][out>>1]^(out&1)),"reconstruct");S.actualReconstructions++;
   }
   S.jointCutChecks++;
  }return true;
 }
 for(let t=0;t<300;t++){let n=3+rnd(4),C=builder(n,Array.from({length:n},()=>rnd(2))),g=3+rnd(9),o;for(let j=0;j<g;j++)o=C.and(2*rnd(n+j)+rnd(2),2*rnd(n+j)+rnd(2),j===g-1?1:rnd(2));if(verify(C,o))S.randomCircuits++;}
 for(let k=1;k<=2;k++)for(let t=0;t<18;t++){let M=2**k,C=builder(M+k,Array.from({length:M+k},(_,i)=>+(i>=M))),V=Array.from({length:M},(_,i)=>2*i);for(let j=0;j<k;j++){let W=[];for(let i=0;i<V.length;i+=2)W.push(C.mux(2*(M+j),V[i],V[i+1],rnd(2)));V=W;}if(verify(C,C.and(V[0],V[0],1)))S.lookupCircuits++;}
 // Family: r table muxes, f_i = p_i XOR (nonzero(q) AND parity_{j!=i} p_j).
 // Exact local response capacities saturate via varying table i alone.
 function example(k,r){
  let M=2**k,d=r*M,bits=Math.log2(r),n=d+k+bits,C=builder(n,Array.from({length:n},(_,i)=>+(i>=d))),p=[];
  for(let i=0;i<r;i++){let V=Array.from({length:M},(_,j)=>2*(i*M+j));for(let q=0;q<k;q++){let W=[];for(let j=0;j<V.length;j+=2)W.push(C.mux(2*(d+q),V[j],V[j+1],0));V=W;}p.push(V[0]);}
  let nonzero=Array.from({length:k},(_,j)=>2*(d+j)).reduce((a,b)=>C.or(a,b,0));
  let f=p.map((v,i)=>{let z=p.filter((_,j)=>j!==i).reduce((a,b)=>C.xor(a,b,0));return C.xor(v,C.and(nonzero,z,0),0);});
  let V=f.slice();for(let j=0;j<bits;j++){let W=[];for(let i=0;i<V.length;i+=2)W.push(C.mux(2*(d+k+j),V[i],V[i+1],1));V=W;}
  let out=V[0],P=structure(C,Array.from({length:d},(_,i)=>i)),N=C.side.length,Ts=Array.from({length:M},(_,h)=>specialize(C,P,h));
  ok(P.Q.length===k&&P.F.length===r,"interface");
  // Obtain rigorous LOWER bounds on each exact response capacity from
  // varying a single table with all other tables zero. Enumerate all
  // 2^M assignments for M<=8; enough to certify full older mincut.
  let cap=Array(N).fill(0);
  for(let i=0;i<r;i++){
   let seen=Array.from({length:N},()=>new Set());
   for(let x=0;x<2**M;x++){
    // Use arrays, not bit masks, for >32 primaries.
    let row=Array.from({length:M},(_,h)=>{
     let A=Array(N).fill(0);for(let j=0;j<M;j++)A[i*M+j]=x>>j&1;for(let j=0;j<k;j++)A[d+j]=h>>j&1;
     for(let z=0;z<C.E.length;z++){let [a,b]=C.E[z];A[n+z]=(A[a>>1]^(a&1))&(A[b>>1]^(b&1));}return A;
    });
    for(let v=0;v<N;v++)if(C.side[v]===0)seen[v].add(row.map(A=>A[v]).join(""));
   }
   for(let v=0;v<N;v++)cap[v]=Math.max(cap[v],Math.log2(seen[v].size));
  }
  let data=Array.from({length:d},(_,i)=>i),old=oldFlow(C,data,P,cap);ok(old===d,"all per-vertex exact capacities pass");
  // Evaluate actual joint response vectors on zero and every data basis bit.
  // Symbolically verify affine form by evaluating XOR macro provenance after
  // specializing q; arbitrary AND nodes accepted only if constant/equal.
  function affine(h){
   let A=Array(N).fill(null);for(let i=0;i<d;i++)A[i]=1n<<BigInt(i+1);
   for(let j=0;j<k;j++)A[d+j]=BigInt(h>>j&1);
   function lit(l){let v=A[l>>1];return v===null?null:v^BigInt(l&1);}
   for(let j=0;j<C.E.length;j++){
    let v=n+j;if(C.side[v]!==0)continue;
    if(C.xorNodes.has(v)){let z=C.xorNodes.get(v),a=lit(z.a),b=lit(z.b);if(a!==null&&b!==null){A[v]=a^b^BigInt(z.phase);continue;}}
    let [u,w]=C.E[j],a=lit(u),b=lit(w);
    if(a===0n||b===0n)A[v]=0n;else if(a===1n)A[v]=b;else if(b===1n)A[v]=a;else if(a!==null&&b!==null){if(a===b)A[v]=a;else if((a^b)===1n)A[v]=0n;}
   }
   // OR of mux masked branches has one branch zero, so specialization works.
   return f.map(l=>{let a=lit(l);ok(a!==null,"affine output");return a;});
  }
  let rows=[],basis=new Map();
  for(let h=0;h<M;h++)for(let a of affine(h)){
   ok((a&1n)===0n,"zero constant");let v=a>>1n;rows.push(v);
   while(v){let j=v.toString(2).length-1;if(!basis.has(j)){basis.set(j,v);break;}v^=basis.get(j);}
  }
  ok(basis.size===r+M-1&&basis.size<d,"joint affine rank");
  let L=lifted(C,data,Ts,P.F,true),AF=lifted(C,data,Array.from({length:M},(_,h)=>specialize(C,P,h,true)),P.F,true);ok(AF.flow===basis.size,"affine structural lifted cut");
  // Structural hash alone catches the two-port case; for r>2 use the
  // independently certified affine rank instead of pretending hash is complete.
  if(r===2)ok(L.flow===r+M-1,"joint structural lifted cut");
  S.examples.push({k,r,data:d,oldExactCapacityFlow:old,liftedFlow:L.flow,affineLiftedFlow:AF.flow,jointAffineRank:basis.size,gates:C.E.length});
  // Actual exhaustive residuals in small cases and random basis comparisons.
  let checks=0;
  for(let t=0;t<80;t++){
   let x=Array.from({length:d},()=>rnd(2)),h=rnd(M),b=rnd(r),A=x.concat(Array.from({length:k},(_,j)=>h>>j&1),Array.from({length:bits},(_,j)=>b>>j&1));
   for(let [a,c] of C.E)A.push((A[a>>1]^(a&1))&(A[c>>1]^(c&1)));
   let expected=h===0?x[b*M]:x.reduce((s,v,i)=>s^(i%M===h?v:0),0);
   ok((A[out>>1]^(out&1))===expected,"actual family");checks++;
  }
  S.affineExamples.push({k,r,assignmentChecks:checks});
 }
 for(let k=1;k<=3;k++)for(let r of [2,4,8])example(k,r);
 return S;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

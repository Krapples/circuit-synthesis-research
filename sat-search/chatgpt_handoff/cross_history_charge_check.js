// Cross-history equivalence quotient and capacitated gate-charge optimization.
function run(){
 let seed=870026;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
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

 function quotient(C,P,Ts){
  let N=C.side.length,H=Ts.length,n=C.n,A=Ts.map(()=>Array(N).fill(null)),L=Ts.map(()=>Array(N).fill(-2)),nodes=Array.from({length:n},(_,i)=>({orig:i,ins:[]})),hash=new Map(),af=new Map([[0n,-2],[1n,-1]]);
  for(let v=0;v<n;v++)if(C.side[v]===0){let a=1n<<BigInt(v+1);af.set(a,2*v);af.set(a^1n,2*v+1);for(let h=0;h<H;h++){L[h][v]=2*v;A[h][v]=a;}}
  function read(h,l){let v=l>>1;return (C.side[v]===1?-2+(Ts[h].H.get(v)||0):L[h][v])^(l&1);}
  function alit(h,l){let v=l>>1,a=C.side[v]===1?BigInt(Ts[h].H.get(v)||0):A[h][v];return a===null?null:a^BigInt(l&1);}
  for(let v=n;v<N;v++)if(C.side[v]===0)for(let h=0;h<H;h++){
   let [u,w]=C.E[v-n],a=alit(h,u),b=alit(h,w),z=null;
   if(a===0n||b===0n)z=0n;else if(a===1n)z=b;else if(b===1n)z=a;else if(a!==null&&b!==null){if(a===b)z=a;else if((a^b)===1n)z=0n;}
   // XOR provenance is provided by the explicit three-AND constructor.
   if(C.xorNodes.has(v)){let p=C.xorNodes.get(v),a=alit(h,p.a),b=alit(h,p.b);if(a!==null&&b!==null)z=a^b^BigInt(p.phase);}
   let x=read(h,u),y=read(h,w),l;
   if(z!==null&&af.has(z))l=af.get(z);
   else if(x===-2||y===-2||x===(y^1))l=-2;
   else if(x===-1||x===y)l=y;else if(y===-1)l=x;
   else{if(x>y)[x,y]=[y,x];let key=x+","+y;if(hash.has(key))l=hash.get(key);else{l=2*nodes.length;nodes.push({orig:v,ins:[x,y]});hash.set(key,l);}}
   L[h][v]=l;A[h][v]=z;if(z!==null){if(af.has(z))ok(af.get(z)===l,"alias");af.set(z,l);af.set(z^1n,l^1);}
  }return {nodes,L};
 }
 function graph(C,P,Ts,merge){
  let data=Array.from({length:C.n},(_,i)=>i).filter(i=>C.side[i]===0),nodes,outs=[];
  if(merge){let Q=quotient(C,P,Ts);nodes=Q.nodes;outs=Q.L.flatMap(L=>P.F.map(v=>L[v])).filter(l=>l>=0).map(l=>l>>1);}
  else{
   nodes=Array.from({length:C.n},(_,i)=>({orig:i,ins:[]}));
   for(let T of Ts){let map=new Map(data.map(v=>[v,v]));for(let [v,E] of T.E){map.set(v,nodes.length);nodes.push({orig:v,ins:E.map(l=>2*map.get(l>>1)+(l&1))});}outs.push(...P.F.map(v=>T.L[v]).filter(l=>l>=0).map(l=>map.get(l>>1)));}
  }
  let live=new Set(),todo=outs.slice();while(todo.length){let v=todo.pop();if(live.has(v))continue;live.add(v);todo.push(...nodes[v].ins.map(l=>l>>1));}
  let groups=new Map(),ix=new Map(),copies=[];
  for(let v of live)if(nodes[v].orig>=C.n){let a=nodes[v].orig;if(!groups.has(a))groups.set(a,[]);groups.get(a).push(copies.length);ix.set(v,copies.length);copies.push(v);}
  return {data,nodes,outs:[...new Set(outs)],live,groups,ix,copies};
 }
 function mincost(G,w,unit=true){
  let N=G.nodes.length,s=2*N,t=s+1,A=Array.from({length:t+1},()=>[]),refs=[];
  function edge(u,v,c,k=0){let a={v,c,k,r:A[v].length},b={v:u,c:0,k:-k,r:A[u].length};A[u].push(a);A[v].push(b);return a;}
  let inf=G.data.length+1;
  for(let v of G.live){let i=G.ix.get(v),e=edge(2*v,2*v+1,unit?1:inf,i===undefined?0:w[i]);if(i!==undefined)refs[i]=e;for(let l of G.nodes[v].ins)edge(2*(l>>1)+1,2*v,inf);}
  for(let i of G.data)if(G.live.has(i))edge(s,2*i,1);for(let v of G.outs)edge(2*v+1,t,inf);
  let f=0;
  while(f<G.data.length){
   let d=Array(t+1).fill(Infinity),p=Array(t+1).fill(null),q=[s],inQ=Array(t+1).fill(false);d[s]=0;inQ[s]=true;
   for(let j=0;j<q.length;j++){let u=q[j];inQ[u]=false;for(let i=0;i<A[u].length;i++){let e=A[u][i];if(e.c>0&&d[e.v]>d[u]+e.k+1e-10){d[e.v]=d[u]+e.k;p[e.v]=[u,i];if(!inQ[e.v]){inQ[e.v]=true;q.push(e.v);}}}}
   if(!p[t])break;
   for(let v=t;v!==s;){let [u,i]=p[v],e=A[u][i];e.c--;A[v][e.r].c++;v=u;}f++;
  }
  let load=refs.map(e=>(unit?1:inf)-e.c);return {f,load,cost:load.reduce((s,x,i)=>s+x*w[i],0)};
 }
 // Numerical LP: max t subject to budgets and t <= cost of each discovered flow.
 function lp(A,b,c){
  let m=A.length,n=c.length,W=A.map((a,i)=>a.concat(Array.from({length:m},(_,j)=>+(i===j)),[b[i]]));
  W.push(c.map(x=>-x).concat(Array(m+1).fill(0)));let B=Array.from({length:m},(_,i)=>n+i),rhs=n+m;
  for(let step=0;step<20000;step++){
   let j=W[m].slice(0,rhs).findIndex(x=>x< -1e-9);if(j<0){let x=Array(n).fill(0);for(let i=0;i<m;i++)if(B[i]<n)x[B[i]]=W[i][rhs];return {x,val:W[m][rhs]};}
   let i=-1,r=Infinity;for(let k=0;k<m;k++)if(W[k][j]>1e-9){let z=W[k][rhs]/W[k][j];if(z<r-1e-9||(Math.abs(z-r)<1e-9&&(i<0||B[k]<B[i]))){i=k;r=z;}}
   ok(i>=0,"LP unbounded");let z=W[i][j];W[i]=W[i].map(x=>x/z);
   for(let k=0;k<=m;k++)if(k!==i){let a=W[k][j];if(Math.abs(a)>1e-12)for(let h=0;h<=rhs;h++)W[k][h]-=a*W[i][h];}B[i]=j;
  }throw Error("simplex limit");
 }
 function optimize(G){
  let n=G.copies.length,w0=Array(n).fill(0);for(let I of G.groups.values())for(let i of I)w0[i]=1/I.length;
  let base=mincost(G,w0),free=mincost(G,w0,false);if(base.f!==G.data.length)return {flow:base.f};
  if(!n)return {flow:base.f,shortest:0,uniform:0,opt:0,iterations:0};
  let A=[],b=[],c=Array(n+1).fill(0);c[n]=1;
  for(let I of G.groups.values()){let a=Array(n+1).fill(0);for(let i of I)a[i]=1;A.push(a);b.push(1);}
  function add(load){A.push(load.map(v=>-v).concat([1]));b.push(0);}add(base.load);
  for(let t=1;t<=300;t++){
   let sol=lp(A,b,c),w=sol.x.slice(0,n).map(v=>Math.max(0,v));for(let I of G.groups.values()){let s=I.reduce((z,i)=>z+w[i],0);if(s>1)for(let i of I)w[i]/=s;}
   let q=mincost(G,w);ok(q.f===base.f,"full flow");
   if(sol.val-q.cost<=1e-7){ok(q.cost+1e-7>=base.cost&&base.cost+1e-7>=free.cost&&q.cost<=G.groups.size+1e-7,"charge order");return {flow:q.f,shortest:free.cost,uniform:base.cost,opt:q.cost,upper:sol.val,iterations:t};}
   add(q.load);
  }throw Error("constraint generation limit");
 }
 function select(C,L,start){let V=L.slice(),q=start;while(V.length>1){let W=[];for(let i=0;i<V.length;i+=2)W.push(i+1<V.length?C.mux(2*q,V[i],V[i+1],1):V[i]);V=W;q++;}return C.side[V[0]>>1]===0?C.and(V[0],V[0],1):V[0];}
 function statsFor(C,opt=true){
  let data=Array.from({length:C.n},(_,i)=>i).filter(i=>C.side[i]===0),P=structure(C,data),Ts=Array.from({length:2**P.Q.length},(_,h)=>specialize(C,P,h,true)),G=graph(C,P,Ts,false),Q=graph(C,P,Ts,true);
  return {P,Ts,G,Q,flow:mincost(G,Array(G.copies.length).fill(0)).f,quotient:mincost(Q,Array(Q.copies.length).fill(0)).f,charge:opt?optimize(G):null,quotientCharge:opt?optimize(Q):null};
 }
 let S={chain:[],dilution:[],crossHistory:[],randomCircuits:0,quotientEvaluations:0,strictQuotientCuts:0,injectiveRandom:0,randomOptimizations:0,strictOptimization:0,strictCongestion:0,maxIterations:0,orbitChecks:0};
 for(let L of [2,4,8,16,32]){
  let d=L+2,k=Math.ceil(Math.log2(d)),C=builder(d+k,Array.from({length:d+k},(_,i)=>+(i>=d))),g=C.xor(0,2,0),h=0;
  for(let i=0;i<L;i++)h=C.xor(h,2*(i+2),0);
  select(C,[g,h,...Array.from({length:L},(_,i)=>2*(i+2))],d);let R=statsFor(C);
  ok(R.flow===d&&R.charge.shortest===4&&R.charge.uniform===2*L+2&&Math.abs(R.charge.opt-(2*L+2))<1e-7,"chain gap");
  S.chain.push({L,data:d,shortest:R.charge.shortest,capacitated:R.charge.uniform,optimized:R.charge.opt});
 }
 for(let k=1;k<=5;k++){
  let d=3,n=d+k+2,C=builder(n,Array.from({length:n},(_,i)=>+(i>=d))),q=Array.from({length:k},(_,i)=>2*(d+i)).reduce((a,b)=>C.or(a,b,0)),g=C.xor(C.mux(q,0,4,0),2,0);select(C,[g,2,4],d+k);let R=statsFor(C);
  ok(R.flow===d&&Math.abs(R.charge.uniform-2/2**k)<1e-7&&Math.abs(R.charge.opt-2)<1e-7,"dilution gap");
  S.dilution.push({histories:2**k,uniform:R.charge.uniform,optimized:R.charge.opt,quotientUniform:R.quotientCharge.uniform,iterations:R.charge.iterations});
 }
 for(let k=1;k<=3;k++){
  let r=2**k,M=r,d=r*M,n=d+2*k,C=builder(n,Array.from({length:n},(_,i)=>+(i>=d))),F=[];
  function muxTable(j,shift){let V=Array.from({length:M},(_,i)=>2*(j*M+i));for(let t=0;t<k;t++){let W=[];for(let i=0;i<V.length;i+=2)W.push(C.mux(2*(d+t)^((shift>>t)&1),V[i],V[i+1],0));V=W;}return V[0];}
  for(let i=0;i<r;i++){let p=muxTable(i,0);for(let j=0;j<r;j++)if(j!==i)p=C.xor(p,muxTable(j,i^j),0);F.push(p);}
  let out=select(C,F,d+k),R=statsFor(C,false);ok(R.flow===d&&R.quotient===r,"cross history gap");
  let P=R.P,N=C.side.length,cap=Array(N).fill(0);
  for(let i=0;i<r;i++){
   let seen=Array.from({length:N},()=>new Set());
   for(let x=0;x<2**M;x++){
    let row=Array.from({length:M},(_,q)=>{
     let V=Array(N).fill(0);for(let j=0;j<M;j++)V[i*M+j]=x>>j&1;for(let t=0;t<k;t++)V[d+t]=q>>t&1;
     for(let j=0;j<C.E.length;j++){let [a,b]=C.E[j];V[n+j]=(V[a>>1]^(a&1))&(V[b>>1]^(b&1));}return V;
    });
    for(let v=0;v<N;v++)if(C.side[v]===0)seen[v].add(row.map(V=>V[v]).join(""));
   }for(let v=0;v<N;v++)cap[v]=Math.max(cap[v],Math.log2(seen[v].size));
  }
  let old=oldFlow(C,Array.from({length:d},(_,i)=>i),P,cap);ok(old===d,"old full");
  for(let t=0;t<80;t++){let V=Array.from({length:d},()=>rnd(2)),q=rnd(M),i=rnd(r),want=0;for(let j=0;j<r;j++)want^=V[j*M+(q^i^j)];
   V.push(...Array.from({length:k},(_,j)=>q>>j&1),...Array.from({length:k},(_,j)=>i>>j&1));for(let [a,b] of C.E)V.push((V[a>>1]^(a&1))&(V[b>>1]^(b&1)));ok((V[out>>1]^(out&1))===want,"orbit semantics");S.orbitChecks++;}
  S.crossHistory.push({k,data:d,oldIndividualFlow:old,disjointHistoryFlow:R.flow,quotientFlow:R.quotient,gates:C.E.length});
 }
 for(let t=0;t<220;t++){
  let n=3+rnd(4),C=builder(n,Array.from({length:n},()=>rnd(2))),g=3+rnd(9);
  for(let j=0;j<g;j++)C.and(2*rnd(n+j)+rnd(2),2*rnd(n+j)+rnd(2),j===g-1?1:rnd(2));
  let data=Array.from({length:n},(_,i)=>i).filter(i=>C.side[i]===0),P=structure(C,data);if(!data.length||data.length===n||P.Q.length>5)continue;
  let Ts=Array.from({length:2**P.Q.length},(_,h)=>specialize(C,P,h,true)),Q=quotient(C,P,Ts),G=graph(C,P,Ts,false),K=graph(C,P,Ts,true),a=mincost(G,Array(G.copies.length).fill(0)).f,b=mincost(K,Array(K.copies.length).fill(0)).f;
  let X=sub(data.reduce((s,v)=>s|1<<v,0)),codes=new Set();
  for(let x of X){let V=Array(Q.nodes.length).fill(0);for(let i of data)V[i]=x>>i&1;function lit(l){return l<0?l+2:V[l>>1]^(l&1);}
   for(let j=n;j<Q.nodes.length;j++){let [a,b]=Q.nodes[j].ins;V[j]=lit(a)&lit(b);}
   let code=[];for(let h=0;h<Ts.length;h++){let W=evalLocal(C,P,h,x);for(let v=0;v<C.side.length;v++)if(C.side[v]===0)ok(lit(Q.L[h][v])===W[v],"quotient semantics");code.push(P.F.map(v=>W[v]).join(""));S.quotientEvaluations++;}codes.add(code.join("|"));
  }
  ok(Math.log2(codes.size)<=b+1e-8,"quotient cut");if(b<a)S.strictQuotientCuts++;
  if(codes.size===2**data.length){S.injectiveRandom++;let R=optimize(K);ok(R.flow===data.length,"injective quotient");S.randomOptimizations++;if(R.opt>R.uniform+1e-7)S.strictOptimization++;if(R.uniform>R.shortest+1e-7)S.strictCongestion++;S.maxIterations=Math.max(S.maxIterations,R.iterations);}
  S.randomCircuits++;
 }
 return S;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

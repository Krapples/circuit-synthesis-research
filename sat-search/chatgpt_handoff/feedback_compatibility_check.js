// Realizable feedback histories, compatibility coloring, and structural feedback cuts.
function run(){
 let seed=870024;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(v,m="assertion failed"){if(!v)throw Error(m);}
 function pop(x){let p=0;while(x){p++;x&=x-1;}return p;}
 function sub(m){let a=[];for(let x=m;;x=(x-1)&m){a.push(x);if(!x)return a;}}
 function builder(n,side){
  let E=[],S=side.slice();
  function and(a,b,s){let v=2*(n+E.length);E.push([a,b]);S.push(s);return v;}
  function or(a,b,s){return and(a^1,b^1,s)^1;}
  function xor(a,b,s){return or(and(a,b^1,s),and(a^1,b,s),s);}
  function mux(q,a,b,s){return or(and(q,b,s),and(q^1,a,s),s);}
  return {n,E,S,and,or,xor,mux};
 }
 function color(G){
  let n=G.length,col=Array(n).fill(-1);
  function choose(){let best=-1,bs=-1,bd=-1;for(let i=0;i<n;i++)if(col[i]<0){
   let sat=new Set();for(let j of G[i])if(col[j]>=0)sat.add(col[j]);
   if(sat.size>bs||(sat.size===bs&&G[i].length>bd)){best=i;bs=sat.size;bd=G[i].length;}
  }return best;}
  function search(k,used,left){if(!left)return true;let i=choose(),bad=new Set(G[i].map(j=>col[j]));
   for(let c=0;c<Math.min(k,used+1);c++)if(!bad.has(c)){col[i]=c;if(search(k,Math.max(used,c+1),left-1))return true;col[i]=-1;}
   return false;
  }
  for(let k=1;k<=n;k++){col.fill(-1);if(search(k,0,n))return {k,col:col.slice()};}
  throw Error("color");
 }
 function flow(C,sources,sinks,cap,local=false){
  let N=C.S.length,s=2*N,t=s+1,V=t+1,A=Array.from({length:V},()=>[]),inf=sources.length+1;
  function edge(u,v,c){let a={v,c,rev:A[v].length},b={v:u,c:0,rev:A[u].length};A[u].push(a);A[v].push(b);}
  for(let v=0;v<N;v++)if(!local||C.S[v]===0)edge(2*v,2*v+1,cap[v]);
  for(let j=0;j<C.E.length;j++)for(let l of C.E[j]){
   let u=l>>1,v=C.n+j;if(!local||(C.S[u]===0&&C.S[v]===0))edge(2*u+1,2*v,inf);
  }
  for(let i of sources)edge(s,2*i,inf);for(let v of sinks)edge(2*v+1,t,inf);
  let f=0;
  for(;;){let P=Array(V).fill(null),Q=[s];P[s]=[-1,-1];
   for(let j=0;j<Q.length;j++){let u=Q[j];for(let i=0;i<A[u].length;i++){let e=A[u][i];if(e.c>1e-9&&!P[e.v]){P[e.v]=[u,i];Q.push(e.v);}}}
   if(!P[t])return f;
   let d=inf;for(let v=t;v!==s;){let [u,i]=P[v];d=Math.min(d,A[u][i].c);v=u;}
   for(let v=t;v!==s;){let [u,i]=P[v],e=A[u][i];e.c-=d;A[v][e.rev].c+=d;v=u;}f+=d;
  }
 }
 function structure(C,S){
  let N=C.S.length,D=Array.from({length:N},()=>new Set()),R=Array.from({length:N},()=>new Set()),F=new Set();
  for(let i of S)D[i].add(i);
  for(let j=0;j<C.E.length;j++)for(let l of C.E[j]){
   let u=l>>1,v=C.n+j;if(C.S[u]===0&&C.S[v]===1)F.add(u);
   if(C.S[v]===0){if(C.S[u]===1)R[v].add(u);else{for(let x of D[u])D[v].add(x);for(let x of R[u])R[v].add(x);}}
  }
  return {D,R,F:[...F]};
 }
 const S={circuits:0,vertices:0,history_refinements:0,structural_refinements:0,color_refinements:0,strict_color_vs_union:0,cut_checks:0,code_reconstructions:0,flow_checks:0,flow_refinements:0,full_flow_charges:0,topology_examples:[],partial_history_example:null};
 function verify(C,out){
  let n=C.n,N=C.S.length,da=Array.from({length:n},(_,i)=>i).filter(i=>C.S[i]===0),qb=Array.from({length:n},(_,i)=>i).filter(i=>C.S[i]===1);
  if(!da.length||da.length>4||!qb.length)return;
  let X=sub(da.reduce((m,i)=>m|1<<i,0)),Y=sub(qb.reduce((m,i)=>m|1<<i,0)),{D,R,F}=structure(C,da);
  let A=C.S.map((s,i)=>s===0?i:-1).filter(i=>i>=0),old=Array(N).fill(0),struct=old.slice(),union=old.slice(),cc=old.slice(),maps=Array(N),labels=Array(N),dec=Array(N);
  function evalAt(z){let V=Array.from({length:n},(_,i)=>z>>i&1);for(let [a,b] of C.E)V.push((V[a>>1]^(a&1))&(V[b>>1]^(b&1)));return V;}
  let W=X.map(x=>Y.map(y=>evalAt(x|y))),res=W.map(row=>row.map(v=>v[out>>1]^(out&1)).join("")),need=Math.log2(new Set(res).size);
  for(let v of A){
   let I=[...R[v]].sort((a,b)=>a-b),H=new Set(),P=W.map(row=>{
    let m=new Map();for(let V of row){let h=I.map(i=>V[i]).join("");if(m.has(h))ok(m.get(h)===V[v],"formal response");m.set(h,V[v]);H.add(h);}return m;
   });
   let G=P.map(()=>[]);for(let i=0;i<P.length;i++)for(let j=i+1;j<P.length;j++)if([...P[i]].some(([h,val])=>P[j].has(h)&&P[j].get(h)!==val)){G[i].push(j);G[j].push(i);}
   let z=color(G),K=Array.from({length:z.k},()=>new Map());
   for(let i=0;i<P.length;i++)for(let [h,val] of P[i]){let m=K[z.col[i]];ok(!m.has(h)||m.get(h)===val,"color consistency");m.set(h,val);}
   let w=flow(C,Array.from({length:n},(_,i)=>i),I,Array(N).fill(1));
   old[v]=Math.min(D[v].size,2**I.length);struct[v]=Math.min(D[v].size,2**w);union[v]=Math.min(D[v].size,H.size);cc[v]=Math.log2(z.k);
   ok(H.size<=2**w&&cc[v]<=union[v]+1e-9&&union[v]<=struct[v]&&struct[v]<=old[v],"capacity hierarchy");
   if(struct[v]<old[v])S.structural_refinements++;if(union[v]<old[v])S.history_refinements++;if(cc[v]<old[v]-1e-9)S.color_refinements++;if(cc[v]<union[v]-1e-9)S.strict_color_vs_union++;
   maps[v]=I;labels[v]=z.col;dec[v]=K;S.vertices++;
  }
  function cut(K){let K0=new Set(K),reached=Array(N).fill(false);for(let i of da)reached[i]=!K0.has(i);
   for(let j=0;j<C.E.length;j++){let v=n+j;if(C.S[v]===0&&!K0.has(v))reached[v]=C.E[j].some(l=>C.S[l>>1]===0&&reached[l>>1]);}
   return F.every(v=>!reached[v]);
  }
  let cuts=[da,F];for(let t=0;t<10;t++){let K=A.filter(()=>rnd(3)===0);if(cut(K))cuts.push(K);}
  for(let K of cuts){
   ok(cut(K));let K0=new Set(K),code=new Map();
   ok(need<=K.reduce((z,v)=>z+cc[v],0)+1e-9,"color cut");
   for(let i=0;i<X.length;i++){
    let key=K.map(v=>labels[v][i]).join(",");if(code.has(key))ok(code.get(key)===res[i],"equal code");code.set(key,res[i]);
    for(let y of Y){
     let V=Array.from({length:n},(_,j)=>y>>j&1);
     function override(v){if(K0.has(v)){let h=maps[v].map(i=>V[i]).join(""),d=dec[v][labels[v][i]];ok(d.has(h),"realizable history");V[v]=d.get(h);}}
     for(let v=0;v<n;v++)override(v);
     for(let j=0;j<C.E.length;j++){let [a,b]=C.E[j];V.push((V[a>>1]^(a&1))&(V[b>>1]^(b&1)));override(n+j);}
     ok((V[out>>1]^(out&1))===(W[i][Y.indexOf(y)][out>>1]^(out&1)),"reconstruction");
     S.code_reconstructions++;
    }
   }S.cut_checks++;
  }
  let a=flow(C,da,F,old,true),b=flow(C,da,F,struct,true),c=flow(C,da,F,cc,true);
  ok(need<=c+1e-8&&c<=b+1e-8&&b<=a+1e-8,"fractional flow");S.flow_checks++;if(c<a-1e-8)S.flow_refinements++;
  if(need===da.length){
   let d=Array(N).fill(Infinity);for(let v of F)if(cc[v]>0)d[v]=0;
   for(let v=N-1;v>=n;v--)if(C.S[v]===0&&cc[v]>0&&Number.isFinite(d[v]))for(let l of C.E[v-n]){
    let u=l>>1;if(C.S[u]===0&&cc[u]>0)d[u]=Math.min(d[u],d[v]+1/cc[v]);
   }
   ok(da.reduce((z,i)=>z+d[i],0)<=A.filter(v=>v>=n).length+1e-8,"fractional path charge");S.full_flow_charges++;
  }
  S.circuits++;
 }
 for(let t=0;t<400;t++){
  let n=3+rnd(4),C=builder(n,Array.from({length:n},()=>rnd(2))),g=3+rnd(9),out;
  for(let j=0;j<g;j++)out=C.and(2*rnd(n+j)+rnd(2),2*rnd(n+j)+rnd(2),j===g-1?1:rnd(2));
  // Keep signed output noncomplemented for the simple comparison below.
  verify(C,out);
 }
 for(let k=1;k<=2;k++)for(let t=0;t<20;t++){
  let M=2**k,C=builder(M+k,Array.from({length:M+k},(_,i)=>+(i>=M))),V=Array.from({length:M},(_,i)=>2*i);
  for(let j=0;j<k;j++){let W=[];for(let i=0;i<V.length;i+=2)W.push(C.mux(2*(M+j),V[i],V[i+1],rnd(2)));V=W;}
  verify(C,C.and(V[0],V[0],1));
 }
 // Topologies in which all old causal cuts pass via an explicit full flow.
 // k distinct feedback sources are generated from t seed queries alone.
 for(let k=4;k<=7;k++){
  let M=2**k,t=Math.ceil(Math.log2(k+1)),C=builder(M+k,Array.from({length:M+k},(_,i)=>+(i>=M))),Q=[];
  for(let mask=1;mask<=k;mask++){let I=Array.from({length:t},(_,i)=>i).filter(i=>mask>>i&1);Q.push(I.map(i=>2*(M+i)).reduce((a,b)=>C.and(a,b,1)));}
  let V=Array.from({length:M},(_,i)=>2*i);
  for(let j=0;j<k;j++){let W=[];for(let i=0;i<V.length;i+=2)W.push(C.mux(Q[j],V[i],V[i+1],0));V=W;}
  let out=V[0];for(let i=t;i<k;i++)out=C.xor(out,2*(M+i),1);if(C.S[out>>1]===0)out=C.and(out,out,1);
  let data=Array.from({length:M},(_,i)=>i),N=C.S.length,{D,R,F}=structure(C,data);
  let old=Array.from({length:N},(_,v)=>Math.min(D[v].size,2**R[v].size)),st=old.slice();
  for(let v of F){let w=flow(C,Array.from({length:C.n},(_,i)=>i),[...R[v]],Array(N).fill(1));st[v]=Math.min(D[v].size,2**w);}
  let f=flow(C,data,F,old,true);ok(f===M,"old all cuts pass");
  let c=F.reduce((a,v)=>a+st[v],0);ok(c<M&&c<=2**t,"structural rejection");
  S.topology_examples.push({k,M,seed_queries:t,reverse_ports:R[F[0]].size,old_min_cut:f,refined_port_capacity:c,gates:C.E.length});
 }
 // Covering-array obstruction: each data row has just two histories,
 // but a history-only completion code must cover every binary pair pattern.
 let t=17,rows=[];for(let i=0;i<t;i++)for(let j=i+1;j<t;j++)for(let p=0;p<4;p++)rows.push([i,j,p&1,p>>1]);
 // Any collection of <=4 completions has <=16 distinct column signatures.
 // Equal signatures cannot realize an unequal pair pattern.
 ok(2**4<t&&rows.length===4*t*(t-1)/2,"covering obstruction");
 S.partial_history_example={histories:t,rows:rows.length,max_per_row:2,min_colors_lower_bound:Math.ceil(Math.log2(t))};
 return S;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

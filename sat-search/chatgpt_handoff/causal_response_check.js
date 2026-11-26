// Causal response-table cut certificates. Run: node causal_response_check.js
function run(){
 let seed=870022;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(x,m="assertion failed"){if(!x)throw Error(m);}
 function pop(x){let p=0;while(x){p++;x&=x-1;}return p;}
 function builder(n,side){
  let E=[],S=side.slice();
  function AND(a,b,s){let v=2*(n+E.length);E.push([a,b]);S.push(s);return v;}
  function OR(a,b,s){return AND(a^1,b^1,s)^1;}
  function XOR(a,b,s){return OR(AND(a,b^1,s),AND(a^1,b,s),s);}
  function mux(q,a,b,s){return OR(AND(q,b,s),AND(q^1,a,s),s);}
  return {n,E,S,AND,OR,XOR,mux};
 }
 function analyze(C,out){
  let {n,E,S}=C,N=S.length,F=new Set(),R=new Set();
  for(let j=0;j<E.length;j++)for(let l of E[j])if(S[l>>1]!==S[n+j]) (S[l>>1]===0?F:R).add(l>>1);
  let A=Array.from({length:n},(_,i)=>i).filter(i=>S[i]===0),B=Array.from({length:n},(_,i)=>i).filter(i=>S[i]===1);
  let rev=[...R].sort((a,b)=>a-b),fwd=[...F].sort((a,b)=>a-b),ix=new Map(rev.map((v,i)=>[v,i]));
  ok(rev.length<=25,"mask width");
  let D=Array(N).fill(0),H=Array(N).fill(0);
  for(let v of A)D[v]=1<<v;
  for(let v=n;v<N;v++)if(S[v]===0)for(let l of E[v-n]){
   let u=l>>1;if(S[u]===0){D[v]|=D[u];H[v]|=H[u];}else H[v]|=1<<ix.get(u);
  }
  function cut(S0,K){
   let reached=Array(N).fill(false),Kset=new Set(K);
   for(let v of A)reached[v]=!!(S0>>v&1)&&!Kset.has(v);
   for(let v=n;v<N;v++)if(S[v]===0&&!Kset.has(v))reached[v]=E[v-n].some(l=>S[l>>1]===0&&reached[l>>1]);
   return fwd.every(v=>!reached[v]);
  }
  function cap(S0,K){return K.reduce((a,v)=>a+Math.min(pop(D[v]&S0),2**pop(H[v])),0);}
  function evalFull(x){let V=Array.from({length:n},(_,i)=>x>>i&1);for(let [a,b] of E)V.push((V[a>>1]^(a&1))&(V[b>>1]^(b&1)));return V[out>>1]^(out&1);}
  function simulate(x,y,K,tables){
   let V=Array.from({length:n},(_,i)=>(x|y)>>i&1),Kset=new Set(K);
   // For each overridden cut vertex, all local reverse ancestors precede it.
   function at(v){
    if(!Kset.has(v))return;
    let key=0;for(let i=0;i<rev.length;i++)if(H[v]>>i&1)key=2*key+V[rev[i]];
    V[v]=tables.get(v)[key];
   }
   for(let v=0;v<n;v++)at(v);
   for(let v=n;v<N;v++){let [a,b]=E[v-n];V.push((V[a>>1]^(a&1))&(V[b>>1]^(b&1)));at(v);}
   return V[out>>1]^(out&1);
  }
  function tables(x,K){
   let T=new Map();
   for(let v of K){
    let I=rev.filter((_,i)=>H[v]>>i&1),values=[];
    for(let z=0;z<2**I.length;z++){
     let W=Array.from({length:n},(_,i)=>x>>i&1),P=new Map(I.map((u,i)=>[u,(z>>(I.length-1-i))&1]));
     function lit(l){let u=l>>1;return (S[u]===0?W[u]:(P.get(u)||0))^(l&1);}
     for(let u=n;u<=v;u++)W.push(S[u]===0?(lit(E[u-n][0])&lit(E[u-n][1])):0);
     values.push(W[v]);
    }T.set(v,values);
   }return T;
  }
  return {A,B,D,H,fwd,rev,cut,cap,evalFull,simulate,tables};
 }
 function sub(mask){let a=[];for(let x=mask;;x=(x-1)&mask){a.push(x);if(!x)return a;}}
 function frontiers(C,P,S0){
  let V=C.S.map((s,i)=>s===0?i:-1).filter(i=>i>=0);
  let K=new Set(P.fwd),sets=[...new Set([P.fwd.join(","),P.A.filter(i=>S0>>i&1).join(",")])].map(s=>s?s.split(",").map(Number):[]);
  // Push each frontier gate back to its A-only predecessors. The old
  // vertex may remain if separately needed as an output; the cut check
  // is independent of this construction.
  for(let step=0;step<12;step++){
   let choices=[...K].filter(v=>v>=C.n);
   if(!choices.length)break;let v=choices[rnd(choices.length)];K.delete(v);
   for(let l of C.E[v-C.n])if(C.S[l>>1]===0)K.add(l>>1);
   sets.push([...K].sort((a,b)=>a-b));
  }
  for(let j=0;j<6;j++){let K=V.filter(()=>rnd(3)===0);if(P.cut(S0,K))sets.push(K);}
  return sets.filter(K=>P.cut(S0,K));
 }
 const S={random_circuits:0,lookup_circuits:0,source_subsets:0,internal_cuts:0,residual_checks:0,response_reconstructions:0,distinct_response_codes:0,strictly_stronger_port_bounds:0,strictly_stronger_internal_bounds:0,counterexamples:[],max_feedback_bits:0};
 function verify(C,out,tries){
  let P=analyze(C,out),A=P.A.reduce((m,i)=>m|1<<i,0),B=P.B.reduce((m,i)=>m|1<<i,0);
  if(C.S[out>>1]!==1||!A||!B||P.rev.length>8)return false;
  S.max_feedback_bits=Math.max(S.max_feedback_bits,P.rev.length);
  for(let j=0;j<tries;j++){
   let U=j===0?A:(rnd(1<<C.n)&A);if(!U)continue;S.source_subsets++;
   let fixed=rnd(1<<C.n)&(A^U),X=sub(U),Y=sub(B),residuals=new Set();
   for(let x of X)residuals.add(Y.map(y=>P.evalFull(x|fixed|y)).join(""));
   let base=P.fwd.length*2**P.rev.length,port=P.cap(U,P.fwd);
   if(port<base)S.strictly_stronger_port_bounds++;
   for(let K of frontiers(C,P,U)){
    let c=P.cap(U,K),codes=new Map();
    ok(Math.log2(residuals.size)<=c+1e-9,"causal capacity");S.internal_cuts++;
    if(c<port)S.strictly_stronger_internal_bounds++;
    for(let x of X){
     let T=P.tables(x|fixed,K),key=K.map(v=>T.get(v).join("")).join("|"),sig="";
     for(let y of Y){let want=P.evalFull(x|fixed|y),got=P.simulate(fixed,y,K,T);
      ok(got===want,"cut response reconstruction");sig+=got;S.response_reconstructions++;}
     if(codes.has(key))ok(codes.get(key)===sig,"same response code");
     codes.set(key,sig);S.residual_checks++;
    }ok(codes.size<=2**c,"code cardinality");S.distinct_response_codes+=codes.size;
   }
  }return true;
 }
 for(let t=0;t<240;t++){
  let n=3+rnd(4),C=builder(n,Array.from({length:n},()=>rnd(2))),g=3+rnd(9),out;
  for(let j=0;j<g;j++)out=C.AND(2*rnd(n+j)+rnd(2),2*rnd(n+j)+rnd(2),j===g-1?1:rnd(2));
  if(verify(C,out,4))S.random_circuits++;
 }
 for(let k=1;k<=3;k++){
  let M=2**k,n=M+k;
  for(let t=0;t<14;t++){
   let C=builder(n,Array.from({length:n},(_,i)=>+(i>=M))),V=Array.from({length:M},(_,i)=>2*i);
   for(let j=0;j<k;j++){
    let W=[];for(let i=0;i<V.length;i+=2){let s=t===0?0:t===1?1:rnd(2);W.push(C.mux(2*(M+j),V[i],V[i+1],s));}V=W;
   }
   // Bob output gate with a redundant repeated operand is intentional:
   // no claim of normalization; valid circuit even for an Alice-side mux.
   let out=C.AND(V[0],V[0],1);
   if(verify(C,out,2))S.lookup_circuits++;
  }
 }
 // Two topologies with same raw directional port budgets, but an impossible
 // causal interface for INDEX. Every data input has a path to output.
 for(let k=4;k<=7;k++)for(let allFeedback of [false,true]){
  let M=2**k,n=M+k,C=builder(n,Array.from({length:n},(_,i)=>+(i>=M))),groups=Array.from({length:k},()=>[]);
  for(let i=0;i<M;i++)groups[i%k].push(2*i);
  let K=groups.map(G=>G.reduce((a,b)=>C.XOR(a,b,0))),q=allFeedback?Array.from({length:k},(_,i)=>2*(M+i)).reduce((a,b)=>C.XOR(a,b,0)):0;
  let out=K.map((v,i)=>C.XOR(v,allFeedback?q:2*(M+i),0)).reduce((a,b)=>C.AND(a,b,1));
  // Support masks here use only small instances in analyze; compute structural
  // sets explicitly for the larger counterexamples instead.
  let F=new Set(),R=new Set(),H=Array.from({length:C.S.length},()=>new Set()),D=Array.from({length:C.S.length},()=>new Set());
  for(let i=0;i<M;i++)D[i].add(i);
  for(let j=0;j<C.E.length;j++)for(let l of C.E[j]){
   let u=l>>1,v=n+j;
   if(C.S[u]!==C.S[v]){(C.S[u]===0?F:R).add(u);if(C.S[v]===0)H[v].add(u);}
   else if(C.S[v]===0){for(let x of H[u])H[v].add(x);for(let x of D[u])D[v].add(x);}
  }
  let a=F.size,b=R.size;ok(a===k&&b===k,"raw budgets");
  ok(a+b>=k&&a+b+1>=M/(2*2**b)&&a*2**b>=M,"raw tests");
  let pc=[...F].reduce((z,v)=>z+Math.min(D[v].size,2**H[v].size),0);
  let ic=K.reduce((z,l)=>z+Math.min(D[l>>1].size,2**H[l>>1].size),0);
  ok(ic===k&&ic<M,"internal bottleneck");if(allFeedback)ok(pc===M,"port test passes");else ok(pc===2*k&&pc<M,"local feedback fails");
  // Independently check K separates all A data from F within A.
  let KS=new Set(K.map(l=>l>>1)),reach=Array(C.S.length).fill(false);
  for(let i=0;i<M;i++)reach[i]=!KS.has(i);
  for(let j=0;j<C.E.length;j++){let v=n+j;reach[v]=C.S[v]===0&&!KS.has(v)&&C.E[j].some(l=>C.S[l>>1]===0&&reach[l>>1]);}
  ok([...F].every(v=>!reach[v]),"actual cut");
  S.counterexamples.push({k,M,a,b,allFeedback,portCapacity:pc,internalCapacity:ic,gates:C.E.length});
 }
 return S;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

// Batched packed lookup and asymmetric cut replay. Run with node.
function run(){
 let seed=870021;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(v,m="assertion failed"){if(!v)throw Error(m);}
 function enc(C){let out=[];for(let a of C){out.push(1,+(a>0));let v=Math.abs(a)-1;while(v){out.push(1,v%2);v=Math.floor(v/2);}out.push(0,1);}out.push(0,0);return out;}
 function parse(w){let F=[],C=[],i=0;while(i<w.length){let a=w[i++],b=w[i++];if(!a&&!b){F.push(C);C=[];continue;}ok(a===1);let v=0,p=1,last=1;while(i<w.length){let d=w[i++],e=w[i++];if(!d){ok(e===1&&last===1);break;}v+=p*e;p*=2;last=e;}C.push((b?1:-1)*(v+1));}ok(C.length===0);return F;}
 function unitProp(F){
  let C=F.map(a=>[...new Set(a)]).filter(a=>!a.some(v=>a.includes(-v))),V=new Set(),Q=C.filter(a=>a.length===1).map(a=>a[0]);
  for(let i=0;i<Q.length;i++){let l=Q[i];if(V.has(-l))return false;if(V.has(l))continue;V.add(l);let next=[];for(let a of C){if(a.includes(l))continue;if(a.includes(-l)){a=a.filter(x=>x!==-l);if(!a.length)return false;if(a.length===1)Q.push(a[0]);}next.push(a);}C=next;}
  ok(C.length===0,"unresolved gadget");return true;
 }
 function params(k,r){let M=2**k,ell=2**Math.floor(Math.log2(Math.max(1,Math.floor(k/2)))),P=2**ell,B=M/ell,lo=Math.log2(ell),per=k+(2*B-1)+P,Q=2**Math.ceil(Math.log2(r*per));return {M,ell,P,B,lo,per,Q,w:Math.log2(Q)+1};}
 // Aligned dictionary IDs; separate common-width aux interval.
 function packed(k,r,H,X){
  let {M,ell,P,B,lo}=params(k,r),A=r*(k+2*B-1),Q=2**Math.ceil(Math.log2(A+r*P)),w=Math.log2(Q)+1;
  // Q and dictionary block offsets multiples of P (Q>=P).
  let next=Q+r*P,word=[],F=[],data=[],query=[];
  function emit(C){let start=word.length;F.push(C);word.push(...enc(C));return start;}
  for(let j=0;j<r;j++){
   let addr=Array.from({length:k},()=>++next),root=++next,guards=[root];
   for(let i=0;i<k;i++)query.push(emit([(X[j]>>i&1)?addr[i]:-addr[i]])+1);
   emit([root]);
   for(let a of addr.slice(lo).reverse()){
    let N=[];for(let g of guards)for(let l of [-a,a]){let z=++next;emit([-z,g]);emit([-z,l]);emit([z,-g,-l]);N.push(z);}guards=N;
   }
   ok(guards.length===B);
   let V=p=>Q+j*P+p+1;
   for(let p=0;p<P;p++)for(let t=0;t<ell;t++)emit([...addr.slice(0,lo).map((a,i)=>t>>i&1?-a:a),p>>t&1?V(p):-V(p)]);
   for(let i=0;i<B;i++){
    let p=0;for(let t=0;t<ell;t++)p|=H[j][i*ell+t]<<t;
    let off=emit([-guards[i],V(p)]);for(let t=0;t<ell;t++)data.push(off+2*w+4+3+2*t);
   }
  }
  ok(next===Q+r*P+A&&next<=2*Q);
  ok(new Set([...data,...query]).size===data.length+query.length,"distinct terminal coordinates");
  return {word,F,data,query};
 }
 let S={packed_cases:0,sat:0,unsat:0,grammar_checks:0,coordinate_checks:0,max_word:0,max_tables:0,max_data_bits:0,protocols:0,protocol_entries:0,rectangle_checks:0,richness_checks:0,strategy_checks:0};
 for(let k=1;k<=7;k++)for(let r of [1,2,4,8])for(let t=0;t<4;t++){
  let M=2**k,H=Array.from({length:r},()=>Array.from({length:M},()=>rnd(2))),X=Array.from({length:r},()=>rnd(M));
  if(t===0)for(let j=0;j<r;j++)H[j][X[j]]=1;
  if(t===1)H[0][X[0]]=0;
  let a=packed(k,r,H,X),F=parse(a.word),want=H.every((h,i)=>h[X[i]]);
  ok(JSON.stringify(F)===JSON.stringify(a.F),"parse");
  ok(unitProp(F)===want,"SAT");S[want?"sat":"unsat"]++;S.grammar_checks++;
  for(let type of [0,1]){
   let j=rnd(r),i=rnd(type?k:M),H2=H.map(h=>h.slice()),X2=X.slice();
   if(type)X2[j]^=1<<i;else H2[j][i]^=1;
   let b=packed(k,r,H2,X2),diff=a.word.map((v,i)=>v!==b.word[i]?i:-1).filter(i=>i>=0);
   ok(a.word.length===b.word.length&&diff.length===1&&diff[0]===(type?a.query[j*k+i]:a.data[j*M+i]),"coordinate");
   S.coordinate_checks++;
  }
  S.packed_cases++;S.max_word=Math.max(S.max_word,a.word.length);S.max_tables=Math.max(S.max_tables,r);S.max_data_bits=Math.max(S.max_data_bits,r*M);
 }
 // Enumerate the complete communication matrix and actual fixed-schedule
 // protocols: Bob sends high query bits, Alice sends selected table blocks,
 // Bob decodes remaining query bits. Also test output on Alice by sending
 // the remaining query bits and one answer bit per table back.
 function runProtocol(r,k,bPer,owner){
  let M=2**k,d=r*M,A=r*(2**(k-bPer)),B=r*bPer+(owner===0?r*(k-bPer):0),rows=2**d,cols=M**r,groups=new Map(),strategies=new Map();
  ok(d<=16);
  function bits(v,n){return v.toString(2).padStart(n,"0");}
  for(let h=0;h<rows;h++){
   let positive=1;for(let j=0;j<r;j++){let v=(h>>>(j*M))&(M===16?65535:(1<<M)-1),wt=0;for(let i=0;i<M;i++)wt+=(v>>>i)&1;if(wt<M/2)positive=0;}
   let accepts=0,T=new Set(),sig=new Map(),res="";
   for(let q=0;q<cols;q++){
    let u=q,bt="",at="",tail="",out=1;
    for(let j=0;j<r;j++){
     let i=u%M;u=Math.floor(u/M);let hi=i>>>(k-bPer),lo=i&((1<<(k-bPer))-1),len=2**(k-bPer);
     bt+=bPer?bits(hi,bPer):"";tail+=k-bPer?bits(lo,k-bPer):"";
     for(let z=0;z<len;z++)at+=(h>>>(j*M+hi*len+z))&1;
     out&=(h>>>(j*M+i))&1;
    }
    let transcript=bt+"|"+at+(owner===0?"|"+tail:"");
    if(!groups.has(transcript))groups.set(transcript,{R:new Set(),Q:new Set(),n:0,AR:new Set(),AQ:new Set(),an:0});
    let G=groups.get(transcript);G.R.add(h);G.Q.add(q);G.n++;
    if(out){G.AR.add(h);G.AQ.add(q);G.an++;accepts++;T.add(transcript);}
    let key=bt+(owner===0?tail:"");if(sig.has(key))ok(sig.get(key)===at);sig.set(key,at);res+=out;
    S.protocol_entries++;
   }
   if(positive){ok(accepts>=(M/2)**r);ok(T.size<=2**B);let max=0;for(let t of T)max=Math.max(max,groups.get(t).AQ.size);ok(max>=accepts/2**B);}
   if(owner===1){let key=[...sig].sort().map(x=>x.join(":")).join("|");if(strategies.has(key))ok(strategies.get(key)===res);strategies.set(key,res);}
  }
  for(let G of groups.values()){ok(G.n===G.R.size*G.Q.size&&G.an===G.AR.size*G.AQ.size,"rectangles");S.rectangle_checks+=2;}
  ok(A+B+r>=r*M/(2*2**(B/r)),"richness inequality");S.richness_checks++;
  if(owner===1){ok(A*2**B>=r*Math.log2(2**M-1)-1e-9,"strategy bound");S.strategy_checks++;}
  S.protocols++;
 }
 for(let [r,k] of [[1,1],[1,2],[1,3],[2,1],[2,2],[3,1]])for(let b=0;b<=k;b++)for(let o=0;o<2;o++)runProtocol(r,k,b,o);
 // Actual signed mux AIGs under directed vertex partitions.
 S.aig_cuts=0;S.aig_port_cuts=0;S.aig_port_rectangles=0;S.aig_port_savings=0;S.aig_max_port_saving=0;S.aig_assignments=0;S.aig_rectangles=0;S.aig_forward_only=0;S.aig_max_gates=0;
 for(let [r,k] of [[1,1],[1,2],[1,3],[2,1],[2,2]]) {
  let M=2**k,d=r*M,n=d+r*k,E=[];
  function AND(a,b){let v=2*(n+E.length);E.push([a,b]);return v;}
  function OR(a,b){return AND(a^1,b^1)^1;}
  function mux(q,a,b){return OR(AND(q,b),AND(q^1,a));}
  let outputs=[];
  for(let j=0;j<r;j++){
   let V=Array.from({length:M},(_,i)=>2*(j*M+i));
   for(let i=0;i<k;i++){let q=2*(d+j*k+i),W=[];for(let z=0;z<V.length;z+=2)W.push(mux(q,V[z],V[z+1]));V=W;}
   outputs.push(V[0]);
  }
  let o=outputs.reduce((a,b)=>AND(a,b));S.aig_max_gates=Math.max(S.aig_max_gates,E.length);
  for(let trial=0;trial<18;trial++){
   let side=Array.from({length:n+E.length},(_,i)=>i<n?+(i>=d):trial===0?1:trial===1?0:rnd(2));
   let A=0,B=0,ports=new Set();
   for(let j=0;j<E.length;j++)for(let l of E[j])if(side[l>>1]!==side[n+j]){ports.add(l>>1);if(side[l>>1]===0)A++;else B++;}
   let order=[...ports].sort((a,b)=>a-b),pa=order.filter(v=>side[v]===0).length,pb=order.length-pa,saving=A+B-pa-pb;
   if(saving>0)S.aig_port_savings++;S.aig_max_port_saving=Math.max(S.aig_max_port_saving,saving);
   let groups=new Map(),pgroups=new Map(),positiveRows=0;
   for(let h=0;h<2**d;h++){
    let accept=0,transcripts=new Set(),rich=true;
    for(let j=0;j<r;j++){let w=0;for(let i=0;i<M;i++)w+=(h>>>(j*M+i))&1;if(w<M/2)rich=false;}
    for(let q=0;q<2**(r*k);q++){
     let V=Array.from({length:n},(_,i)=>i<d?(h>>i&1):(q>>(i-d)&1)),T="";
     for(let j=0;j<E.length;j++){
      let [a,b]=E[j];for(let l of [a,b])if(side[l>>1]!==side[n+j])T+=V[l>>1];
      V.push((V[a>>1]^(a&1))&(V[b>>1]^(b&1)));
     }
     let want=1;for(let j=0;j<r;j++)want&=h>>>(j*M+((q>>>(j*k))&(M-1)))&1;
     ok((V[o>>1]^(o&1))===want&&T.length===A+B,"AIG semantics");
     if(!groups.has(T))groups.set(T,{R:new Set(),Q:new Set(),n:0,AR:new Set(),AQ:new Set(),an:0});
     let G=groups.get(T);G.R.add(h);G.Q.add(q);G.n++;
     if(want){G.AR.add(h);G.AQ.add(q);G.an++;accept++;transcripts.add(T);}
     let PT=order.map(v=>V[v]).join('');ok(PT.length===pa+pb,'port schedule');
     if(!pgroups.has(PT))pgroups.set(PT,{R:new Set(),Q:new Set(),n:0,AR:new Set(),AQ:new Set(),an:0});
     let P=pgroups.get(PT);P.R.add(h);P.Q.add(q);P.n++;if(want){P.AR.add(h);P.AQ.add(q);P.an++;}
     S.aig_assignments++;
    }
    if(rich){ok(accept>=(M/2)**r&&transcripts.size<=2**B,"AIG richness row");positiveRows++;}
   }
   for(let G of groups.values()){ok(G.n===G.R.size*G.Q.size&&G.an===G.AR.size*G.AQ.size,"AIG rectangle");S.aig_rectangles+=2;}
   ok(positiveRows>=2**(r*(M-1)),"rich row count");
   ok(A+B+r>=r*M/(2*2**(B/r)),"AIG directional cut");
   ok(A+B>=r*k,"AIG rank cut");
   if(side[o>>1]===1)ok(A*2**B>=r*Math.log2(2**M-1)-1e-9,"AIG strategy cut");
   if(!B&&side[o>>1]===1)S.aig_forward_only++;
   for(let G of pgroups.values()){ok(G.n===G.R.size*G.Q.size&&G.an===G.AR.size*G.AQ.size,'port rectangle');S.aig_port_rectangles+=2;}
   ok(pa+pb+r>=r*M/(2*2**(pb/r)),'port richness');ok(pa+pb>=r*k,'port rank');
   if(side[o>>1]===1)ok(pa*2**pb+1e-9>=Math.log2(1+(2**M-1)**r),'exact port strategy');
   S.aig_port_cuts++;S.aig_cuts++;
  }
 }
 return S;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

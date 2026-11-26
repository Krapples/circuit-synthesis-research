// Enabled permutable packed lookup replay. Run: node causal_lookup_check.js
function run(){
 let seed=870023;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(v,m="assertion failed"){if(!v)throw Error(m);}
 function enc(C){let out=[];for(let a of C){out.push(1,+(a>0));let v=Math.abs(a)-1;while(v){out.push(1,v%2);v=Math.floor(v/2);}out.push(0,1);}out.push(0,0);return out;}
 function parse(w){let F=[],C=[],i=0;while(i<w.length){let a=w[i++],b=w[i++];if(!a&&!b){F.push(C);C=[];continue;}ok(a===1);let v=0,p=1,last=1;while(i<w.length){let d=w[i++],e=w[i++];if(!d){ok(e===1&&last===1);break;}v+=p*e;p*=2;last=e;}C.push((b?1:-1)*(v+1));}ok(C.length===0);return F;}
 function unitProp(F){
  let C=F.map(a=>[...new Set(a)]).filter(a=>!a.some(v=>a.includes(-v))),V=new Set(),Q=C.filter(a=>a.length===1).map(a=>a[0]);
  for(let i=0;i<Q.length;i++){let l=Q[i];if(V.has(-l))return false;if(V.has(l))continue;V.add(l);let next=[];for(let a of C){if(a.includes(l))continue;if(a.includes(-l)){a=a.filter(x=>x!==-l);if(!a.length)return false;if(a.length===1)Q.push(a[0]);}next.push(a);}C=next;}
  ok(C.length===0,"unresolved gadget");return true;
 }

 function packed(k,r,H,X,E,pi){
  let M=2**k,ell=2**Math.floor(Math.log2(Math.max(1,Math.floor(k/2)))),P=2**ell,B=M/ell,lo=Math.log2(ell);
  let A=r*(k+2*B),Q=2**Math.ceil(Math.log2(A+r*P)),w=Math.log2(Q)+1,next=Q+r*P;
  let word=[],F=[],data=[],query=[],enable=[],groups=[];
  function emit(C){let start=word.length;F.push(C);word.push(...enc(C));return start;}
  for(let j=0;j<r;j++){
   let addr=Array.from({length:k},()=>++next),e=++next,root=++next,guards=[root];
   for(let i=0;i<k;i++)query.push(emit([(X[j]>>i&1)?addr[i]:-addr[i]])+1);
   enable.push(emit([E[j]?e:-e])+1);emit([root]);
   for(let a of addr.slice(lo).reverse()){
    let N=[];for(let g of guards)for(let l of [-a,a]){let z=++next;emit([-z,g]);emit([-z,l]);emit([z,-g,-l]);N.push(z);}guards=N;
   }
   ok(guards.length===B);let V=p=>Q+j*P+p+1;
   for(let p=0;p<P;p++)for(let t=0;t<ell;t++)emit([...addr.slice(0,lo).map((a,i)=>t>>i&1?-a:a),p>>t&1?V(p):-V(p)]);
   groups.push({e,guards,V});
  }
  for(let i=0;i<r*B;i++){
   let g=groups[Math.floor(pi[i]/B)],p=0;
   for(let t=0;t<ell;t++)p|=H[i*ell+t]<<t;
   let off=emit([-g.e,-g.guards[pi[i]%B],g.V(p)]);for(let t=0;t<ell;t++)data.push(off+2*(2*w+4)+3+2*t);
  }
  ok(next===Q+r*P+A&&next<=2*Q);
  ok(new Set([...data,...query,...enable]).size===data.length+query.length+enable.length);
  return {word,F,data,query,enable,B,ell};
 }
 function perm(n){let p=Array.from({length:n},(_,i)=>i);for(let i=n-1;i>0;i--){let j=rnd(i+1);[p[i],p[j]]=[p[j],p[i]];}return p;}
 function want(H,X,E,pi,B,ell){return E.every((e,j)=>!e||H[pi.indexOf(j*B+Math.floor(X[j]/ell))*ell+X[j]%ell]);}
 function check(a,want){let F=parse(a.word);ok(JSON.stringify(F)===JSON.stringify(a.F),"parse");ok(unitProp(F)===want,"semantics");}
 let S={cases:0,sat:0,unsat:0,coordinate_checks:0,permutation_layout_checks:0,individual_data_retrievals:0,distinct_residuals:0,residual_entries:0,max_word:0,max_data_bits:0,one_active_group_retrievals:0,one_group_residuals:0,one_group_residual_entries:0};
 for(let k=1;k<=6;k++)for(let r of [1,2,4])for(let t=0;t<4;t++){
  let M=2**k,ell=2**Math.floor(Math.log2(Math.max(1,Math.floor(k/2)))),B=M/ell,H=Array.from({length:r*M},()=>rnd(2)),X=Array.from({length:r},()=>rnd(M)),E=Array.from({length:r},()=>rnd(2)),pi=perm(r*B);
  if(t===0)E.fill(0);if(t===1){E.fill(1);H[pi.indexOf(Math.floor(X[0]/ell))*ell+X[0]%ell]=0;}
  let a=packed(k,r,H,X,E,pi),v=want(H,X,E,pi,B,ell);check(a,v);S[v?"sat":"unsat"]++;
  let pi2=perm(r*B),b=packed(k,r,H,X,E,pi2);ok(a.word.length===b.word.length&&["data","query","enable"].every(key=>a[key].join(",")===b[key].join(",")),"permutation layout");check(b,want(H,X,E,pi2,B,ell));S.permutation_layout_checks++;
  for(let type of ["data","query","enable"]){
   let i=rnd(a[type].length),h=H.slice(),x=X.slice(),e=E.slice();
   if(type==="data")h[i]^=1;else if(type==="query")x[Math.floor(i/k)]^=1<<(i%k);else e[i]^=1;
   let c=packed(k,r,h,x,e,pi),diff=a.word.map((v,i)=>v!==c.word[i]?i:-1).filter(i=>i>=0);
   ok(diff.length===1&&diff[0]===a[type][i],"single copy coordinate");S.coordinate_checks++;
  }
  // Read arbitrary physical data by one enabled lookup; use same data word.
  for(let i of [0,r*M-1,rnd(r*M)]){
   let logical=pi[Math.floor(i/ell)],j=Math.floor(logical/B),x=X.slice(),e=E.map(()=>0);x[j]=(logical%B)*ell+i%ell;e[j]=1;
   let c=packed(k,r,H,x,e,pi);check(c,!!H[i]);S.individual_data_retrievals++;
  }
  // Same fixed active group, only its low address and programmable metadata vary.
  let x0=Array(r).fill(0),e0=Array(r).fill(0);e0[0]=1;
  let base=packed(k,r,H,x0,e0,pi);
  for(let i of [0,r*M-1,rnd(r*M)]){
   let p=pi.slice(),j=Math.floor(i/ell),z=p.indexOf(0);[p[j],p[z]]=[p[z],p[j]];
   let x=x0.slice();x[0]=i%ell;let c=packed(k,r,H,x,e0,p);
   check(c,!!H[i]);
   ok(c.data.every((v,j)=>base.word[v]===c.word[v]&&c.word[v]===H[j]),"data fixed");
   ok(c.enable.every(v=>base.word[v]===c.word[v]),"enable fixed");
   ok(c.query.every((v,j)=>j<Math.log2(ell)||base.word[v]===c.word[v]),"only active low query changes");
   S.one_active_group_retrievals++;
  }
  S.cases++;S.max_word=Math.max(S.max_word,a.word.length);S.max_data_bits=Math.max(S.max_data_bits,H.length);
 }
 for(let [k,r] of [[1,2],[2,2],[1,3]]){
  let M=2**k,ell=2**Math.floor(Math.log2(Math.max(1,Math.floor(k/2)))),B=M/ell,pi=perm(r*B),N=r*M,res=new Set();
  for(let h=0;h<2**N;h++){
   let H=Array.from({length:N},(_,i)=>h>>i&1),sig="";
   for(let i=0;i<N;i++){
    let logical=pi[Math.floor(i/ell)],j=Math.floor(logical/B),X=Array(r).fill(0),E=Array(r).fill(0);X[j]=(logical%B)*ell+i%ell;E[j]=1;
    let a=packed(k,r,H,X,E,pi),v=unitProp(parse(a.word));ok(v===!!H[i],"exact residual");sig+=+v;S.residual_entries++;
   }res.add(sig);
  }ok(res.size===2**N,"injective all data");S.distinct_residuals+=res.size;
  let res0=new Set();
  for(let h=0;h<2**N;h++){
   let H=Array.from({length:N},(_,i)=>h>>i&1),sig="";
   for(let i=0;i<N;i++){
    let p=pi.slice(),j=Math.floor(i/ell),z=p.indexOf(0);[p[j],p[z]]=[p[z],p[j]];
    let X=Array(r).fill(0),E=Array(r).fill(0);X[0]=i%ell;E[0]=1;
    let a=packed(k,r,H,X,E,p),v=unitProp(parse(a.word));ok(v===!!H[i],"one-group joint residual");sig+=+v;S.one_group_residual_entries++;
   }res0.add(sig);
  }ok(res0.size===2**N,"one-group joint injection");S.one_group_residuals+=res0.size;
 }
 return S;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

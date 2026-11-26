// Exact finite checks for the fanout-excess <=2 reduction of L-meta-16102.
// Node.js, no dependencies. This is not a kernel proof.
function run(){
 const T=18445899635892944896n;
 function ok(v,m="assertion failed"){if(!v)throw Error(m);}
 function bit(t,x){return Number(t>>BigInt(x)&1n);}
 function mask(n){return (1n<<BigInt(2**n))-1n;}
 function inject(x,U){return U.reduce((z,i,j)=>z|((x>>j&1)<<i),0);}
 function range(n){return Array.from({length:n},(_,i)=>i);}
 function pop(x){let n=0;for(;x;x&=x-1)n++;return n;}
 function tt(n,i){let t=0n;for(let x=0;x<2**n;x++)if(x>>i&1)t|=1n<<BigInt(x);return t;}
 function project(t,U,base=0){let f=0n;for(let x=0;x<2**U.length;x++)if(bit(t,base|inject(x,U)))f|=1n<<BigInt(x);return f;}
 function rows(t,U,V,base=0){return range(2**U.length).map(x=>project(t,V,base|inject(x,U)));}
 function sortedDistinct(a){return [...new Set(a)].sort((x,y)=>x<y?-1:x>y?1:0);}
 function obstruction(n,t){
  let M=[],Z=[],A=2**n-1;
  for(let x=0;x<=A;x++){
   if(bit(t,x)){if(range(n).every(i=>!(x>>i&1)||!bit(t,x^(1<<i))))M.push(x);}
   else if(range(n).every(i=>(x>>i&1)||bit(t,x|1<<i)))Z.push(x);
  }
  for(let a of M)for(let b of Z)if(pop(a&(A^b))>1)return [a,b];
  return null;
 }
 // All NNF formulas over an exact set of leaf POSITIONS. A repeated
 // variable has two different positions; only designated labels may be negated.
 function formulaDP(n,labels,signed,targets=null){
  let A=mask(n),F=(1<<labels.length)-1,D=Array(F+1),stored=0,comparisons=0;
  for(let m=1;m<=F;m++){
   if(!(m&(m-1))){let i=labels[31-Math.clz32(m)],v=tt(n,i);D[m]=signed.has(i)?[v,v^A]:[v];continue;}
   let out=new Set(),low=m&-m;
   for(let a=(m-1)&m;a;a=(a-1)&m)if(a&low){
    let b=m^a;if(!b)continue;
    for(let x of D[a])for(let y of D[b]){
     let p=x&y,q=x|y;comparisons+=2;
     if(m===F&&targets){ok(!targets.has(p)&&!targets.has(q),"two repeated variables realize target");}
     else{out.add(p);out.add(q);}
    }
   }
   D[m]=[...out];if(m!==F)stored+=D[m].length;
  }
  return {tables:D[F],stored,comparisons};
 }
 for(let i=0;i<6;i++){
  ok(range(64).some(x=>bit(T,x)!==bit(T,x^(1<<i))),"full support");
  ok(range(64).every(x=>bit(T,x)<=bit(T,x|1<<i)),"monotonicity");
 }
 let root=obstruction(6,T);ok(root,"not read once");
 let cofactor=[];
 for(let i=0;i<6;i++){
  let V=range(6).filter(j=>j!==i),w=null;
  for(let s=0;s<2;s++){let b=obstruction(5,project(T,V,s<<i));if(b){w={i,phase:s,minPositive:inject(b[0],V),maxNegative:inject(b[1],V)};break;}}
  ok(w,"each primary has non-RO cofactor");cofactor.push(w);
 }
 let modules=[],moduleChecks=0;
 for(let m=1;m<64;m++){
  let U=range(6).filter(i=>m>>i&1),V=range(6).filter(i=>!(m>>i&1));
  let r=sortedDistinct(rows(T,U,V)).length;ok(r>=2,"essential");if(r===2)modules.push(m);moduleChecks++;
 }
 ok(modules.join(",")==="1,2,4,8,16,32,63","no nontrivial proper module");
 // Two independent singleton forks: test all 15 pairs after relabeling.
 let targets=new Set();
 for(let i=0;i<6;i++)for(let j=i+1;j<6;j++){
  let U=[i,j,...range(6).filter(k=>k!==i&&k!==j)];targets.add(project(T,U));
 }
 let direct=formulaDP(6,[0,1,2,3,4,5,0,1],new Set([0,1]),targets);
 // Nested case: exactly one occurrence of the first fork enters g, one
 // remains outside; g is a read-once formula on x_i and nonempty U.
 let cases=[],consistent=0,specs=new Map(),nestedSubsetChecks=0;
 for(let i=0;i<6;i++){
  let rest=range(6).filter(j=>j!==i);
  for(let m=1;m<32;m++){
   nestedSubsetChecks++;
   let U=rest.filter((_,j)=>m>>j&1),V=rest.filter((_,j)=>!(m>>j&1)),k=U.length,pass=true;
   for(let x=0;x<2;x++){
    let R=rows(T,U,V,x<<i),Q=sortedDistinct(R);
    if(Q.length>2||Q.some(t=>obstruction(V.length,t))){pass=false;break;}
    if(Q.length===2){
     let g=0n;for(let j=0;j<R.length;j++)if(R[j]===Q[1])g|=1n<<BigInt(j);
     if(obstruction(k,g)){pass=false;break;}
    }
   }
   if(!pass)continue;cases.push([i,U]);
   let G=formulaDP(k+1,range(k+1),new Set(range(k+1))).tables;
   for(let g of G){
    let M=0n,W=0n,valid=true;
    outer:for(let x=0;x<2;x++)for(let u=0;u<2**k;u++){
     let z=bit(g,x|(u<<1));
     for(let y=0;y<2**V.length;y++){
      let h=x|(z<<1)|(y<<2),b=bit(T,(x<<i)|inject(u,U)|inject(y,V)),flag=1n<<BigInt(h);
      if((M&flag)&&bit(W,h)!==b){valid=false;break outer;}
      M|=flag;if(b)W|=flag;
     }
    }
    if(valid){let n=2+V.length;if(!specs.has(n))specs.set(n,new Map());specs.get(n).set(M+","+W,[M,W]);consistent++;}
   }
  }
 }
 let nested=[];
 for(let [n,S] of [...specs].sort((a,b)=>a[0]-b[0])){
  let D=formulaDP(n,[...range(n),1],new Set([0,1])).tables;
  for(let [M,W] of S.values())ok(!D.some(f=>(f&M)===W),"nested fork realizes target");
  nested.push({variables:n,partial_specs:S.size,tables:D.length});
 }
 return {table:T.toString(),read_once_obstruction:root,non_read_once_cofactors:cofactor,module_checks:moduleChecks,two_residual_modules:modules,independent_pair_checks:15,distinct_relabelled_targets:targets.size,independent_formula_comparisons:direct.comparisons,independent_stored_tables:direct.stored,nested_subset_checks:nestedSubsetChecks,nested_candidates:cases,consistent_upstream_tables:consistent,nested,matching_specs:0,result:"all fanout-excess <=2 cases excluded"};
}
if(typeof module!=="undefined"&&require.main===module)console.log(JSON.stringify(run(),null,2));

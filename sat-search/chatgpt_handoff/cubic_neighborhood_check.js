// Exact-image coordinate kernel for bounded-degree polynomial maps.
// Run: node cubic_neighborhood_check.js
function run(){
  let seed=870012;
  function draw(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
  function assert(x,msg="assertion failed"){if(!x)throw Error(msg);}
  function parity(x){let p=0;while(x){p^=1;x&=x-1;}return p;}
  function reduce(B,v){for(let i=B.length-1;i>=0;i--)if(v&(1<<i)){if(B[i])v^=B[i];else break;}return v;}
  function insert(B,v){v=reduce(B,v);if(!v)return false;B[31-Math.clz32(v)]=v;return true;}
  function canonical(terms){
    const D=new Map();
    for(let [vars,v] of terms){const a=[...new Set(vars)].sort((a,b)=>a-b),key=a.join(",");
      const old=D.get(key);D.set(key,[a,(old?old[1]:0)^v]);}
    return [...D.values()].filter(x=>x[1]);
  }
  function kernel(q,k,input){
    const terms=canonical(input);
    let G=Array.from({length:q},()=>new Set());
    for(let [a,v] of terms)for(let i of a)for(let j of a)if(i!==j)G[i].add(j);
    const degree=Math.max(0,...G.map(s=>s.size));
    const alive=Array(q).fill(true), centers=[], rounds=[];
    function deleteBall(v){let S=new Set([v]);for(let i=0;i<3;i++){let T=new Set(S);for(let u of S)for(let w of G[u])T.add(w);S=T;}for(let u of S)alive[u]=false;}
    for(let r=0;r<8*k;r++){
      let B=Array(k).fill(0),selected=[];
      while(true){
        let hit=terms.find(([a,v])=>a.some(i=>alive[i])&&reduce(B,v));
        if(!hit)break;
        let [a,v]=hit,c=a.find(i=>alive[i]);assert(insert(B,v));
        selected.push([c,v]);centers.push(c);deleteBall(c);
      }
      rounds.push(selected);
    }
    const keep=alive.map(a=>!a), V=Array(k).fill(0);
    for(let [a,v] of terms)if(a.some(i=>alive[i]))insert(V,v);
    const dual=Array.from({length:1<<k},(_,i)=>i).filter(l=>V.every(v=>!parity(l&v)));
    assert(centers.length<=8*k*k);
    assert(keep.filter(Boolean).length<=centers.length*(1+degree+degree**2+degree**3));
    let owner=Array(q).fill(-1);
    for(let c of centers)for(let v of [c,...G[c]]){assert(owner[v]===-1);owner[v]=c;assert(keep[v]);}
    for(let [a,v] of terms)assert(new Set(a.map(i=>owner[i]).filter(i=>i!==-1)).size<=1);
    for(let l of dual)for(let [a,v] of terms)if(parity(l&v))assert(a.every(i=>keep[i]));
    return {terms,keep,dual,centers,rounds,degree};
  }
  function brute(q,k,terms,keep){
    const H=Array(1<<k).fill(0n);
    const T=terms.map(([a,v])=>[a.reduce((m,i)=>m|(1<<i),0),v]);
    const mask=keep.reduce((m,v,i)=>v?m|(1<<i):m,0);
    for(let x=0;x<1<<q;x++)if((x&mask)===x){
      let a=0;for(let [m,v] of T)if((m&x)===m)a^=v;H[a]++;
    }return H;
  }
  // Independent exact transfer-matrix histogram for path-width-two monomials.
  function pathHistogram(q,k,terms,keep){
    let M=1<<k,groups=Array.from({length:q},()=>[]),constant=0;
    for(let [a,v] of terms){
      if(!a.length){constant^=v;continue;}
      let j=a.at(-1);assert(j-a[0]<=2);
      groups[j].push([a.reduce((m,i)=>m|(1<<(j-i)),0),v]);
    }
    let H=Array(4*M).fill(0n);H[constant]=1n;
    for(let j=0;j<q;j++){
      let T=Array(4*M).fill(0n);
      for(let s=0;s<4;s++)for(let b=0;b<=(keep[j]?1:0);b++){
        const w=(s<<1)|b;let v=0;
        for(let [m,c] of groups[j])if((w&m)===m)v^=c;
        const base=(w&3)*M;
        for(let a=0;a<M;a++)if(H[s*M+a])T[base+(a^v)]+=H[s*M+a];
      }H=T;
    }
    return Array.from({length:M},(_,a)=>H[a]+H[M+a]+H[2*M+a]+H[3*M+a]);
  }
  function marg(a,dual){return dual.map(l=>parity(l&a)).join("");}
  function smallWeightImage(k,K){
    // Enumerate <= 3t selected variables, not full kernel. Intended for small t.
    const t=Math.log2(K.dual.length), vars=K.keep.map((v,i)=>v?i:-1).filter(i=>i>=0),out=new Set();
    let low=K.terms.filter(([a,v])=>K.dual.some(l=>parity(l&v)));
    assert(low.every(([a])=>a.every(i=>K.keep[i])));
    // Variables absent from the low marginal may be omitted.
    const active=[...new Set(low.flatMap(([a])=>a))];
    const S=new Set();
    function visit(start,left){
      let a=0;for(let [v,c] of low)if(v.every(i=>S.has(i)))a^=c;
      out.add(marg(a,K.dual));
      if(left)for(let i=start;i<active.length;i++){S.add(active[i]);visit(i+1,left-1);S.delete(active[i]);}
    }
    visit(0,Math.min(3*t,active.length));
    return {out,active:active.length};
  }
  let stats={small_maps:0,connected_path_maps:0,strict_reductions:0,addresses:0,dual_bias_checks:0,
    low_marginal_checks:0,full_image_maps:0,max_q:0,max_degree:0,max_kernel:0,max_discard:0,
    max_low_active:0,largest_connected_kernel_case:null};
  function check(q,k,terms,path){
    const K=kernel(q,k,terms),all=Array(q).fill(true),r=K.keep.filter(Boolean).length;
    const hist=path?pathHistogram:brute,A=hist(q,k,K.terms,all),B=hist(q,k,K.terms,K.keep);
    assert(A.reduce((s,x)=>s+x,0n)===(1n<<BigInt(q)));
    assert(B.reduce((s,x)=>s+x,0n)===(1n<<BigInt(r)));
    const marginal=new Set(A.map((v,i)=>v?marg(i,K.dual):null).filter(x=>x!==null));
    for(let a=0;a<A.length;a++){
      assert((A[a]>0n)===(B[a]>0n),"lost address");
      assert((A[a]>0n)===marginal.has(marg(a,K.dual)),"marginal lift");
      stats.addresses++;
    }
    for(let l=1;l<1<<k;l++)if(!K.dual.includes(l)){
      for(let round of K.rounds)assert(round.some(([c,v])=>parity(l&v)));
      for(let [H,d] of [[A,q],[B,r]]){
        let s=H.reduce((a,v,i)=>a+(parity(i&l)?-v:v),0n);if(s<0n)s=-s;
        assert(s*4n**BigInt(8*k)<=3n**BigInt(8*k)*(1n<<BigInt(d)),"bias bound");
        stats.dual_bias_checks++;
      }
    }
    if(K.dual.length<=8||q<=12){
      const low=smallWeightImage(k,K);
      assert(low.out.size===marginal.size&&[...low.out].every(x=>marginal.has(x)));
      stats.low_marginal_checks++;stats.max_low_active=Math.max(stats.max_low_active,low.active);
    }
    stats[path?"connected_path_maps":"small_maps"]++;
    stats.strict_reductions+=r<q;
    stats.full_image_maps+=A.every(x=>x>0n);
    stats.max_q=Math.max(stats.max_q,q);stats.max_degree=Math.max(stats.max_degree,K.degree);
    stats.max_kernel=Math.max(stats.max_kernel,r);stats.max_discard=Math.max(stats.max_discard,q-r);
    if(path&&(!stats.largest_connected_kernel_case||q-r>stats.largest_connected_kernel_case.discarded))
      stats.largest_connected_kernel_case={q,k,degree:K.degree,retained:r,discarded:q-r,low_dimension:Math.log2(K.dual.length),image:A.filter(x=>x>0n).length};
  }
  for(let k=1;k<=6;k++)for(let trial=0;trial<25;trial++){
    let q=1+draw(12),terms=[[[],draw(1<<k)]];
    for(let j=0;j<3*q;j++){let a=Array.from({length:1+draw(3)},()=>draw(q));terms.push([a,draw(1<<k)]);}
    check(q,k,terms,false);
  }
  // Long connected hypergraph paths: high directions repeated, low directions local.
  for(let k=2;k<=6;k++)for(let t=0;t<=Math.min(2,k-1);t++){
    let q=2300,hi=k-t,terms=[[[],draw(1<<k)]];
    for(let i=0;i<q-2;i++)terms.push([[i,i+1,i+2],1<<(i%hi)]);
    if(t===1)terms.push([[0,1],1<<hi]);
    if(t===2){terms.push([[0,1],3<<hi]);terms.push([[0],2<<hi]);}
    check(q,k,terms,true);
  }
  return stats;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

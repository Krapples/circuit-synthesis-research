// Reproduce the local descent obstruction on small matchings.
// All circuits are explicitly NONLEAST; this is not a counterexample to L-meta-3754.
function check(k) {
  const n=2*k,N=1<<n,edges=Array.from({length:k},(_,i)=>[2*i,2*i+1]);
  const gates=[],add=(op,a,b)=>{gates.push([op,a,b]);return n+gates.length-1};
  let clauses=[0,1];
  for(let i=1;i<k;i++){let next=[];for(const p of clauses)for(let b=0;b<2;b++)next.push(add("or",p,2*i+b));clauses=next}
  let root=clauses[0];for(let i=1;i<clauses.length;i++)root=add("and",root,clauses[i]);
  const r=gates.length-2,cut=n+r,F=m=>edges.some(([a,b])=>!!(m&(1<<a))&&!!(m&(1<<b)));
  const ev=(m,hole=-1,fill=false,repl=null)=>{
    const v=Array.from({length:n},(_,i)=>!!(m&(1<<i)));
    for(let j=0;j<gates.length;j++){
      if(j===hole&&!repl){v.push(fill);continue}
      const [op,a,b]=j===hole?repl:gates[j];
      v.push(op==="and"?v[a]&&v[b]:v[a]||v[b]);
    }
    return v
  };
  const masks=Array.from({length:N},(_,i)=>i),orig=masks.map(m=>ev(m)),w0=masks.map(m=>ev(m,r,false)),w1=masks.map(m=>ev(m,r,true));
  const edgeMasks=edges.map(([a,b])=>(1<<a)|(1<<b)),L=edgeMasks.filter(m=>!w0[m][root]),H=masks.filter(m=>!F(m)&&w1[m][root]);
  const clean=w=>masks.every(m=>!orig[m][w]||F(m)),safe=Array.from({length:cut},(_,w)=>w).filter(w=>H.every(m=>!orig[m][w]));
  let exactAND=0,exactOR=0,cleanAND=0;
  for(let a=0;a<cut;a++)for(let b=a;b<cut;b++)for(const op of ["and","or"]){
    const x=masks.map(m=>ev(m,r,false,[op,a,b]));
    if(x.every((v,m)=>v[root]===F(m))){
      if(op==="and"){exactAND++;if(x.every((v,m)=>!v[cut]||F(m)))cleanAND++}else exactOR++;
    }
  }
  const charges=gates.map((_,j)=>j).filter(j=>j>=r&&(j===r||gates[j].slice(1).some(w=>!w0[N-1][w])));
  let repair=[];
  for(let a=0;a<=root;a++)for(let b=a;b<=root;b++)
    if(L.every(m=>w0[m][a]&&w0[m][b])&&masks.every(m=>!(w0[m][a]&&w0[m][b])||F(m)))repair.push([a,b]);
  const piv=gates.map((_,j)=>edgeMasks.filter(m=>!ev(m,j,false)[root]).length);
  const sig=Array.from({length:n+gates.length},(_,w)=>orig.map(v=>+v[w]).join(""));
  const used=new Set([root]);for(let j=gates.length-1;j>=0;j--)if(used.has(n+j))gates[j].slice(1).forEach(w=>used.add(w));
  const comparatorGates=[],append=(op,a,b)=>{comparatorGates.push([op,a,b]);return n+comparatorGates.length-1};
  const es=edges.map(([a,b])=>append("and",a,b));let o=es[0];for(let i=1;i<es.length;i++)o=append("or",o,es[i]);
  const comparatorExact=masks.every(m=>{
    const v=Array.from({length:n},(_,i)=>!!(m&(1<<i)));
    for(const [op,a,b] of comparatorGates)v.push(op==="and"?v[a]&&v[b]:v[a]||v[b]);
    return v[o]===F(m)
  });
  const result={k,n,gates:gates.length,dirty:gates.filter(([op],j)=>op==="and"&&!clean(n+j)).length,exact:orig.every((v,m)=>v[root]===F(m)),live:gates.every((_,j)=>used.has(n+j)),distinct:new Set(sig).size===sig.length,liftSites:gates.filter(([op,a,b],j)=>op==="or"&&!clean(n+j)&&(clean(a)||clean(b))).length,minPivotal:Math.min(...piv),lost:L.length,hazards:H.length,safe:safe.length,exactAND,exactOR,cleanAND,charges,residualOutput:w0[N-1][root],repair:repair.length,comparator:comparatorGates.length,comparatorExact};
  if(!result.exact||!result.live||!result.distinct||result.liftSites!==0||result.minPivotal<1||result.lost!==k||result.safe!==0||result.exactOR!==0||result.cleanAND!==0||result.repair!==0||result.charges.length!==2||result.residualOutput||!comparatorExact||result.comparator>=result.gates)throw Error(JSON.stringify(result));
  return result;
}
console.log(JSON.stringify([2,3,4].map(check), null, 2));

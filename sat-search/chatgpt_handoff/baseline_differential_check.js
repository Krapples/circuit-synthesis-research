"use strict";
// Exact finite replay; no dependencies. Run node baseline_differential_check.js.
function replay(){
  let seed=870028; const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
  const assert=(b,m)=>{if(!b)throw Error(m)};
  const parity=x=>{let p=0;while(x){p^=1;x&=x-1}return p};
  const add=(a,b)=>{let c=new Set(a);for(const z of b)c.has(z)?c.delete(z):c.add(z);return c};
  const mul=(a,b)=>{let c=new Set;for(const x of a)for(const y of b){let z=x|y;c.has(z)?c.delete(z):c.add(z)}return c};
  const one=()=>new Set([0n]),zero=()=>new Set();
  const rank=vs=>{let piv=new Map;for(let v of vs){while(v){let p=v.toString(2).length-1;if(piv.has(p))v^=piv.get(p);else{piv.set(p,v);break}}}return piv.size};
  let circuits=0,contexts=0,gateChecks=0,termChecks=0,degreeChecks=0,spanChecks=0;
  function check(d,k,gates,out,baseline=0){
    const N=1<<d,Q=1<<k,full=(1n<<BigInt(N))-1n;
    const xs=Array.from({length:d},(_,i)=>{let v=0n;for(let x=0;x<N;x++)if(x>>i&1)v|=1n<<BigInt(x);return v});
    const xor=(mask,w)=>{let v=0n;for(let i=0;i<w.length;i++)if(mask&(1n<<BigInt(i)))v^=w[i];return v};
    const rows=Array.from({length:Q},(_,q)=>{let w=[full,...xs,...Array.from({length:k},(_,i)=>q>>i&1?full:0n)],ops=[];for(const [u,v] of gates){let a=xor(u,w),b=xor(v,w);ops.push([a,b]);w.push(a&b)}return {w,ops,f:xor(out,w)}});
    const off=1+d+k, base=rows[baseline], mixed=gates.map((_,i)=>!rows.every(r=>r.w[off+i]===base.w[off+i])&&!rows.every(r=>r.w[off+i]===0n||r.w[off+i]===full));
    let operands=[],idx=[];for(let i=0;i<gates.length;i++){idx[i]=operands.length/2;if(mixed[i])operands.push(...base.ops[i])}
    const t=operands.length/2;
    const evalPoly=p=>{let v=0n;for(const z of p){let w=full;for(let i=0;i<operands.length;i++)if(z>>BigInt(i)&1n)w&=operands[i];v^=w}return v};
    const polyXor=(mask,w)=>{let p=zero();for(let i=0;i<w.length;i++)if(mask>>BigInt(i)&1n)p=add(p,w[i]);return p};
    const verify=(p,expected)=>{for(const z of p){for(let i=0;i<t;i++)assert((z>>BigInt(2*i)&3n)!==3n,"transversal");termChecks++}assert(evalPoly(p)===expected,"evaluation")};
    const deg=v=>{let a=Array.from({length:N},(_,x)=>Number(v>>BigInt(x)&1n));for(let j=0;j<d;j++)for(let x=0;x<N;x++)if(x>>j&1)a[x]^=a[x^(1<<j)];let D=0;for(let x=0;x<N;x++)if(a[x]){let w=x,c=0;while(w){w&=w-1;c++}D=Math.max(D,c)}return D};
    const budget=Array.from({length:t},(_,i)=>Math.max(deg(operands[2*i]),deg(operands[2*i+1]))).reduce((a,b)=>a+b,0);
    const residuals=[];
    for(let q=0;q<Q;q++){
      let row=rows[q],w=[zero(),...xs.map(zero),...Array.from({length:k},(_,i)=>(q^baseline)>>i&1?one():zero())];
      for(let i=0;i<gates.length;i++){
        let expected=row.w[off+i]^base.w[off+i],p;
        if(!mixed[i]){assert(expected===0n||expected===full,"pure");p=expected?one():zero()}
        else{const [u,v]=gates[i],du=polyXor(u,w),dv=polyXor(v,w),j=idx[i];p=add(add(mul(new Set([1n<<BigInt(2*j)]),dv),mul(new Set([1n<<BigInt(2*j+1)]),du)),mul(du,dv))}
        verify(p,expected);gateChecks++;w.push(p)
      }
      const p=polyXor(out,w),delta=row.f^base.f;verify(p,delta);assert(deg(delta)<=budget,"degree");degreeChecks++;residuals.push(delta);contexts++;
    }
    // Count distinct residual signatures, and the exact transversal-function span.
    const signatures=new Set(Array.from({length:N},(_,x)=>residuals.map(v=>String(v>>BigInt(x)&1n)).join("")));
    assert(BigInt(signatures.size)<=1n<<BigInt(2*t),"image");
    let trans=new Set([full]);for(let i=0;i<t;i++){const next=new Set;for(const v of trans){next.add(v);next.add(v&operands[2*i]);next.add(v&operands[2*i+1])}trans=next}
    const r=rank([...trans]);assert(rank([...trans,...residuals])===r,"span");assert(BigInt(r)<=3n**BigInt(t),"rank");spanChecks++;circuits++;
    return {d,k,gates:gates.length,t,budget,residualRank:rank(residuals),signatures:signatures.size};
  }
  const bit=i=>1n<<BigInt(i);
  for(let z=0;z<240;z++){
    const d=2+rnd(3),k=1+rnd(3),n=1+rnd(6),off=1+d+k;
    // use high bits of the LCG, not its alternating low bit, for masks
    const mask=w=>{let a=0n;for(let i=0;i<w;i++)if(rnd(65536)&32768)a|=bit(i);return a};
    let g=[];for(let i=0;i<n;i++)g.push([mask(off+i),mask(off+i)]);
    check(d,k,g,mask(off+n),rnd(1<<k));
  }
  const controls=[];
  // d-input conjunction enabled by a query: exact affine-baseline budget d.
  for(let d=2;d<=5;d++){let off=d+2,g=[[bit(1),bit(d+1)]];for(let i=2;i<=d;i++)g.push([bit(i),bit(off+g.length-1)]);let r=check(d,1,g,bit(off+g.length-1));assert(r.t===d&&r.budget===d&&r.signatures===2,"conjunction");controls.push({kind:"enabled AND",...r})}
  // Two data bits per mixed AND, with pure correction gates.
  for(let pairs=1;pairs<=2;pairs++){let d=2*pairs,k=d,off=1+d+k,g=[],out=0n;for(let j=0;j<pairs;j++){let a=bit(1+2*j),b=bit(2+2*j),u=bit(1+d+2*j),v=bit(2+d+2*j);for(const ab of [[a,b],[u,v],[a^u,b^v]]){out^=bit(off+g.length);g.push(ab)}}let r=check(d,k,g,out);assert(r.t===pairs&&r.signatures===1<<d,"paired inner product");controls.push({kind:"paired inner product",...r})}
  // Shared witness F: OR over selected columns of AND of selected rows.
  for(const [m,l] of [[1,2],[2,1],[2,2],[3,1]]){
    let d=m*l,k=m+l,off=1+d+k,g=[];
    const gate=(a,b)=>{let z=bit(off+g.length);g.push([a,b]);return z};
    let result=0n;
    for(let t=0;t<l;t++){let col=1n;for(let i=0;i<m;i++){const term=1n^gate(bit(1+d+i),1n^bit(1+i*l+t));col=col===1n?term:gate(col,term)}col=gate(col,bit(1+d+m+t));result=result===0n?col:result^col^gate(result,col)}
    let r=check(d,k,g,result);assert(r.residualRank===1+((1<<m)-1)*((1<<l)-1)&&r.signatures===1<<d,"witness rank");controls.push({kind:"shared witness",m,l,...r});
  }
  return {seed:870028,circuits,contexts,gateChecks,termChecks,degreeChecks,spanChecks,controls};
}
console.log(JSON.stringify(replay(), null, 2));

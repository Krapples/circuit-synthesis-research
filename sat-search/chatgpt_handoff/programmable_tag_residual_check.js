"use strict";
// Exact graph residual count and physical unit-clause grammar replay.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};
 const pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 // Exact recurrence for labelled disjoint unions of nontrivial complete
 // bipartite components, and isolated vertices.
 function counts(n){let a=[1n];for(let m=1;m<=n;m++){let z=a[m-1],c=1n;for(let b=2;b<=m;b++){c=c*BigInt(m-b+1)/BigInt(b-1);z+=c*((1n<<BigInt(b-1))-1n)*a[m-b]}a.push(z)}return a}
 // recurrence above c for b=2 starts m-1; update b=3 (m-2)/2 etc.
 const a=counts(128);
 let graphCases=0,semantics=0,distinctChecks=0,physicalChecks=0,layouts=0,examples=[];
 function pairIndex(n){let pairs=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)pairs.push([i,j]);return pairs}
 function graphs(n){
  const pairs=pairIndex(n),out=new Map;
  function rec(B,i){if(i===n){
    const tag=new Array(n),sign=new Array(n);
    function signs(k){if(k===B.length){let mask=0;for(let p=0;p<pairs.length;p++){let [u,v]=pairs[p];if(tag[u]===tag[v]&&sign[u]!==sign[v])mask|=1<<p}if(!out.has(mask))out.set(mask,{tag:tag.slice(),sign:sign.slice()});return}
     let G=B[k];for(let s=0;s<1<<(G.length-1);s++){if(G.length>1&&!s)continue;for(let j=0;j<G.length;j++){tag[G[j]]=k+1;sign[G[j]]=j===0?0:s>>(j-1)&1}signs(k+1)}
    }signs(0);return}
    for(let j=0;j<B.length;j++){B[j].push(i);rec(B,i+1);B[j].pop()}B.push([i]);rec(B,i+1);B.pop()
  }
  rec([],0);return {pairs,out}
 }
 // Paired grammar exact unit clauses: [1,s], pairs [1,d], [0,1], [0,0].
 function unit(id,s){let bits=[1,s];let ds=id.toString(2).split("").reverse().map(Number);for(let d of ds)bits.push(1,d);bits.push(0,1,0,0);return bits}
 function satUnits(w){let seen=new Map;for(let i=0;i<w.length;){assert(w[i]===1,"literal");let sign=w[i+1];i+=2;let id=0,p=1;while(w[i]===1){id+=p*w[i+1];p*=2;i+=2}assert(w[i]===0&&w[i+1]===1&&w[i+2]===0&&w[i+3]===0,"unit delimiter");i+=4;if(seen.has(id)&&seen.get(id)!==sign)return false;seen.set(id,sign)}return true}
 for(let n=1;n<=6;n++){
  let {pairs,out}=graphs(n);assert(BigInt(out.size)===a[n],"exact graph count");graphCases+=out.size;
  // For every graph, test binary zero/nonzero restricted patterns with
  // independently chosen bit coordinate in each slot, including different coordinates.
  let ell=3,P=1<<ell,Q=1;while(Q<(n+1)*P)Q*=2;let width=Q.toString(2).length,dict=[];
  for(let j=0;j<P;j++)dict.push(...unit(Q+j,0));
  for(let pattern=0;pattern<3;pattern++){
   let coordinate=Array.from({length:n},(_,i)=>(pattern===0?0:pattern===1?i%3:(i*2+1)%3)),seen=new Set;layouts++;
   for(let [mask,{tag,sign}] of out){let truth=0n;
    for(let x=0;x<1<<n;x++){let vals=coordinate.map((c,i)=>(x>>i&1)<<c),expect=pairs.every(([i,j],p)=>!(mask>>p&1)||vals[i]!==vals[j]);
     let word=dict.slice();for(let i=0;i<n;i++)word.push(...unit(Q+tag[i]*P+vals[i],sign[i]));
     assert(satUnits(word)===expect,"grammar consistency");semantics++;
     for(let i=0;i<n;i++){let at=(P+i)*(2*width+6)+3+2*coordinate[i];assert(word[at]===(x>>i&1),"physical coordinate");physicalChecks++}
     if(expect)truth|=1n<<BigInt(x);
    }
    assert(!seen.has(truth.toString()),"distinct graph residuals");seen.add(truth.toString());distinctChecks++;
   }
  }
  examples.push({n,count:a[n].toString()});
 }
 // Lower bound from fixed block size b, with a fixed leftover set inactive.
 const log2big=x=>x===0n?0:x.toString(2).length-1;
 const ceilLog=x=>x<=1n?0:(x-1n).toString(2).length;
 function fact(n){let f=1n;for(let i=2;i<=n;i++)f*=BigInt(i);return f}
 let bounds=[];for(let m of [8,16,32,64,128]){
  let best=1n,bestb=0;for(let b=2;b<=m;b++){let g=Math.floor(m/b),n=g*b,z=fact(n)/(fact(b)**BigInt(g)*fact(g))*(((1n<<BigInt(b-1))-1n)**BigInt(g));assert(z<=a[m],"fixed-block lower");if(z>best){best=z;bestb=b}}
  bounds.push({slots:m,exactPortFloor:ceilLog(a[m]),fixedBlockFloor:ceilLog(best),bestb})
 }
 return {graphCases,semantics,physicalChecks,distinctChecks,layouts,examples,bounds};
}
console.log(JSON.stringify(replay(),null,2));

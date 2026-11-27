"use strict";
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870037;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const bit=i=>1n<<BigInt(i);
 const xor=(a,b)=>{let S=new Set(a);for(let m of b)S.has(m)?S.delete(m):S.add(m);return [...S]};
 const mul=(a,b)=>{let S=new Set;for(let x of a)for(let y of b){let m=x|y;S.has(m)?S.delete(m):S.add(m)}return [...S]};
 const sum=(m,g)=>g.reduce((p,h,i)=>m>>i&1?xor(p,h):p,[]);
 function basis(vs){let p=new Map;for(let v of vs)while(v){let k=v&-v;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}return [...p.values()]}
 const rank=vs=>basis(vs).length;
 function rows(h){let M=new Map;for(let m of h)for(let i=m;;i=(i-1)&m){M.set(i,(M.get(i)||0n)|bit(m^i));if(!i)break}return [...M.values()]}
 function diff(v,s){let out=0n;for(let m=0;v;m++,v>>=1n)if(v&1n){let x=m&s;for(let j=x;j;j=(j-1)&x)out^=bit(m^j)}return out}
 function anfDiff(h,s){let S=new Set;for(let m of h){let x=m&s;for(let j=x;j;j=(j-1)&x){let v=m^j;S.has(v)?S.delete(v):S.add(v)}}return [...S]}
 let checks=0,zero=0,nonzero=0,aligned=0,independent=0,strictResidual=0,largest=0;
 for(let z=0;z<360;z++){
  let p=1+rnd(4),f=[];
  for(let i=0;i<p;i++)f.push(mul(xor([1<<(2*i)],sum(rnd(1<<i),f)),xor([1<<(2*i+1)],sum(rnd(1<<i),f))));
  let s=rnd(1<<(2*p)),v=z%4===0?0:z%4===1?s:rnd(1<<(2*p));
  let W=basis(f.flatMap(rows)),B=basis([1n,...W.map(w=>diff(w,s))]),E=basis(W.map(w=>diff(w,v)));
  // tagged elimination modulo B to compute L(M^{-1}(B))
  let piv=new Map,images=[];
  for(let b of B){while(b){let k=b&-b;if(piv.has(k))b^=piv.get(k)[0];else{piv.set(k,[b,0n]);break}}}
  for(let w of W){let x=diff(w,v),y=diff(w,s);while(x){let k=x&-x;if(piv.has(k)){let [a,b]=piv.get(k);x^=a;y^=b}else{piv.set(k,[x,y]);break}}if(!x)images.push(y)}
  let Z=rank([1n,...images]),P=rank([...E,...B]),MB=rank(B.map(w=>diff(w,v)));
  assert(Z<=B.length-MB,"residual kernel cap");
  if(Z<B.length-MB)strictResidual++;
  let g=[[3],...f.map(h=>xor(h.map(m=>m<<2),anfDiff(h,s).map(m=>(m<<2)|3)))];
  for(let a=0;a<4;a++){
    let actual=rank(g.flatMap(h=>rows(anfDiff(h,(v<<2)|a)))),pred=a===0?E.length+2*rank(W.map(w=>diff(diff(w,v),s))):P+Z;
    assert(actual===pred,"direction formula");
    if(!a)zero++;else{nonzero++;if(v===0||v===s){assert(actual===2*B.length,"aligned");aligned++}else independent++}
    largest=Math.max(largest,actual);checks++;
  }
 }
 return {seed:870037,checks,zero,nonzero,aligned,independent,strictResidual,largest}
}
console.log(JSON.stringify(replay(),null,2));

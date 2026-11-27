"use strict";
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870035;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const bit=i=>1n<<BigInt(i);
 const rank=vs=>{let p=new Map;for(let v of vs){while(v){let k=v&-v;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}}return p.size};
 const xor=(a,b)=>{let s=new Set(a);for(let v of b)s.has(v)?s.delete(v):s.add(v);return [...s]};
 const mul=(a,b)=>{let s=new Set;for(let u of a)for(let v of b){let w=u|v;s.has(w)?s.delete(w):s.add(w)}return [...s]};
 const sum=(m,g)=>g.reduce((p,h,i)=>m>>i&1?xor(p,h):p,[]);
 function translate(h,s){let a=[];for(let m of h){let x=m&s;for(let j=x;;j=(j-1)&x){a.push(m^j);if(!j)break}}return xor([],[]).concat([...a.reduce((p,v)=>{p.has(v)?p.delete(v):p.add(v);return p},new Set)])}
 const diff=(h,s)=>xor(h,translate(h,s));
 function rows(h,mixed){let a=new Map;for(let m of h)for(let i=m;;i=(i-1)&m){if(!mixed||(i&&i!==m))a.set(i,(a.get(i)||0n)|bit(m^i));if(!i)break}return [...a.values()]}
 let cases=0,lambdaOne=0,zeroF=0,maxR=0,jointCases=0,jointViol=0,directionalViol=0,maxJoint=0;
 function check(t,g,dep,mask){
  let old=g.slice(1).map(h=>h.filter(m=>!(m&3)).map(m=>m>>2)),s=0;
  for(let i=1;i<t;i++){s|=(dep[i][0]&1)<<(2*i-2);s|=(dep[i][1]&1)<<(2*i-1)}
  const f=sum(mask>>1,old),d=xor(diff(f,s),mask&1?[0]:[]),H=sum(mask,g);
  let rebuilt=xor(f.map(m=>m<<2),d.map(m=>(m<<2)|3));
  assert(xor(rebuilt,H).length===0,"first gate identity");
  let r=rank(rows(f,false)),dr=rank(rows(d,false)),hr=rank(rows(H,false)),mr=rank(rows(H,true));
  if(mask&1)lambdaOne++;
  if(!f.length){zeroF++;assert(hr===((mask&1)?4:0),"zero f");}
  else{
   const pc=m=>{let n=0;while(m){m&=m-1;n++}return n};
   let S=f.reduce((a,b)=>pc(a)>=pc(b)?a:b,0);
   assert(S!==0,"nonconstant");
   let ds=f;for(let j=0;j<2*(t-1);j++)if(S>>j&1)ds=diff(ds,1<<j);
   assert(ds.length===1&&ds[0]===0,"constant derivative");
   assert(hr===r+2*dr&&2*dr<=r,"scalar exact rank");
   assert(mr===hr-2,"mixed border");
  }
  assert(hr<=2**(t+1),"universal scalar bound");maxR=Math.max(maxR,hr);
  let J=rank(old.flatMap(h=>rows(h,true))),Jnew=rank(g.flatMap(h=>rows(h,true)));
  // Span of translates of directional derivatives, plus constant 1.
  let dJoint=rank([1n,...old.flatMap(h=>rows(diff(h,s),false))]);
  assert(Jnew===J+2*dJoint,"joint first gate update");
  if(Jnew>2**(t+1)-2)jointViol++;maxJoint=Math.max(maxJoint,Jnew);
  let dir=rnd(1<<(2*t));let directional=rank(g.flatMap(h=>rows(diff(h,dir),false)));
  if(directional>2**t)directionalViol++;
  cases++;jointCases++;
 }
 for(let t=1;t<=7;t++){
  let n=t<=5?180:100;
  for(let z=0;z<n;z++){let g=[],dep=[];for(let i=0;i<t;i++){let a=rnd(1<<i),b=rnd(1<<i);dep.push([a,b]);g.push(mul(xor([1<<(2*i)],sum(a,g)),xor([1<<(2*i+1)],sum(b,g))))}
   check(t,g,dep,rnd(1<<t));
  }
 }
 // Direct truth translation cross-check for arbitrary f, including affine cases.
 let arbitrary=0;
 for(let n=1;n<=5;n++)for(let z=0;z<40;z++){
  let f=[];for(let m=1;m<1<<n;m++)if(rnd(2))f.push(m);if(!f.length)f=[1];
  let d=xor(diff(f,rnd(1<<n)),rnd(2)?[0]:[]),h=xor(f.map(m=>m<<2),d.map(m=>(m<<2)|3));
  let r=rank(rows(f,false)),dr=rank(rows(d,false)),hr=rank(rows(h,false));
  assert(hr===r+2*dr&&2*dr<=r,"arbitrary first gate");
  const direct=(h,n)=>{let N=1<<n,F=Array.from({length:N},(_,x)=>h.reduce((v,m)=>v^Number((x&m)===m),0));return rank(F.map((_,x)=>F.reduce((v,b,y)=>F[x^y]?v|bit(y):v,0n)))};
  assert(direct(h,n+2)===hr&&direct(f,n)===r,"direct truth matrix");arbitrary++;
 }
 return {seed:870035,cases,lambdaOne,zeroF,maxR,jointCases,jointViol,directionalViol,maxJoint,arbitrary};
}
console.log(JSON.stringify(replay(),null,2));

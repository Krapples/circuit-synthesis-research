"use strict";
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};let seed=870057;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 let covers=0,dictChecks=0,strict=0;
 for(let P of [2,4,8])for(let r=2;r<=P;r++){
  let partitions=new Map;
  for(let h=0;h<1<<P;h++){
   let p=Array.from({length:P},(_,i)=>i<r-2?i:r-2+((h>>i&1)^(h>>(r-2)&1)));
   let key=p.join(",");if(!partitions.has(key))partitions.set(key,p);
   assert(p.every((v,i)=>p.every((w,j)=>v!==w||((h>>i^h>>j)&1)===0)),"covered dictionary");dictChecks++;
  }
  assert(partitions.size===2**(P-r+1),"partition construction count");
  if(r<P){assert((partitions.size/2)*(2**r-2)<2**P-2,"strict lower");strict++}
  covers++;
 }
 function build(m,l,mask){
  let P=1<<l,d=m*l,q=P+m+1,g=[],next=d+q+1;
  const and=(a,b)=>{assert(a>>1!==b>>1,"proper");let i=next++;g.push({i,a,b});return i*2},or=(a,b)=>and(a^1,b^1)^1,mux=(s,a,b)=>or(and(s^1,a),and(s,b)),fold=a=>a.reduce((x,y)=>or(x,y));
  let h=Array.from({length:P},(_,i)=>2*(d+i+1)),sel=Array.from({length:m},(_,i)=>2*(d+P+i+1)),enable=2*(d+P+m+1),x=Array.from({length:m},(_,i)=>Array.from({length:l},(_,j)=>2*(i*l+j+1)));
  function lookup(a){let t=h.slice();for(let s of a){let b=[];for(let i=0;i<t.length;i+=2)b.push(mux(s,t[i],t[i+1]));t=b}return t[0]}
  let raw=[],done=[];for(let i=0;i<m;i++)if(mask>>i&1)done.push(and(lookup(x[i]),sel[i]));else raw.push(i);
  if(raw.length){let addr=Array.from({length:l},(_,j)=>fold(raw.map(i=>and(x[i][j],sel[i]))));done.push(and(lookup(addr),enable))}
  return {m,l,P,d,q,g,o:fold(done),mask};
 }
 let circuits=0,semantic=0,slots=0,compressed=0,ledgers=0,profiles=[];
 for(let m of [2,3,4])for(let l of [1,2,3])for(let mask=0;mask<1<<m;mask++){
  let C=build(m,l,mask),{P,d,q,g,o}=C,A=new Map,privateCounts=Array(m).fill(0),Q=Array(m).fill(0),ports=Array.from({length:m},()=>new Set),mixed=0,ingress=0,I=0,E=0;
  for(let i=1;i<=d+q;i++)A.set(i,i<=d?1<<Math.floor((i-1)/l):0);
  for(let v of g){let a=A.get(v.a>>1),b=A.get(v.b>>1),s=a|b;A.set(v.i,s);assert(s,"data gate");let pure=!(s&(s-1));
   if(pure){let j=Math.log2(s);privateCounts[j]++;Q[j]+=Number(!a)+Number(!b)}else{mixed++;for(let [t,i] of [[a,v.a>>1],[b,v.b>>1]])if(t&&!(t&(t-1)))ports[Math.log2(t)].add(i)}
   for(let z of [v.a>>1,v.b>>1])if(!A.get(z))ingress++;else if(z<=d)I++;else E++;
  }
  let L=0,B=0,c=0;for(let j=0;j<m;j++){let n=ports[j].size;assert(n>0,"essential port");let b=n<l?P-2**n+1:0;assert(Q[j]>=b,"private ingress");assert(privateCounts[j]>=l-n+Math.max(0,l-n)+b,"private gate floor");L+=b;B+=Math.max(0,l-n);c+=n;slots++;if(n<l)compressed++}
  assert(mixed>=c-1&&ingress>=L&&g.length>=d-1+L+B,"disjoint ledger");assert(2*g.length===I+E+ingress,"slots");ledgers++;
  for(let t=0;t<24;t++){let h=rnd(1<<P),j=rnd(m),x=rnd(1<<d),w=[0];for(let k=0;k<d;k++)w.push(x>>k&1);for(let k=0;k<P;k++)w.push(h>>k&1);for(let k=0;k<m;k++)w.push(Number(k===j));w.push(Number(!(mask>>j&1)));let read=v=>w[v>>1]^(v&1);for(let v of g)w[v.i]=read(v.a)&read(v.b);assert(read(o)===(h>>(x>>(j*l)&(P-1))&1),"hybrid truth");semantic++}
  if(m===4&&l===3&&(mask===0||mask===3||mask===15))profiles.push({mask,gates:g.length,privateCounts,Q,ports:ports.map(s=>s.size),mixed,lower:d-1+L+B});circuits++;
 }
 return {seed:870057,covers,dictChecks,strict,circuits,semantic,slots,compressed,ledgers,profiles}
}
console.log(JSON.stringify(replay(),null,2));

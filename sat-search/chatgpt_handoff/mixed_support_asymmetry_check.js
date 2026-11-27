"use strict";
// Support-asymmetry and first-large-support frontier checks on exact hybrid dictionary circuits.
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};let seed=870058;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n},pc=x=>{let n=0;for(;x;x&=x-1)n++;return n};
 function build(m,l,mask){
  let P=1<<l,d=m*l,g=[],next=d+P+m+2;
  const and=(a,b)=>{assert(a>>1!==b>>1,"proper");let i=next++;g.push({i,a:a>>1,b:b>>1,pa:a&1,pb:b&1});return 2*i},or=(a,b)=>and(a^1,b^1)^1,mux=(s,a,b)=>or(and(s^1,a),and(s,b)),fold=a=>a.reduce(or);
  let h=Array.from({length:P},(_,i)=>2*(d+i+1)),sel=Array.from({length:m},(_,i)=>2*(d+P+i+1)),enable=2*(d+P+m+1),x=Array.from({length:m},(_,i)=>Array.from({length:l},(_,j)=>2*(i*l+j+1)));
  function lookup(a){let t=h.slice();for(let s of a){let b=[];for(let i=0;i<t.length;i+=2)b.push(mux(s,t[i],t[i+1]));t=b}return t[0]}
  let raw=[],done=[];for(let i=0;i<m;i++)if(mask>>i&1)done.push(and(lookup(x[i]),sel[i]));else raw.push(i);
  if(raw.length){let addr=Array.from({length:l},(_,j)=>fold(raw.map(i=>and(x[i][j],sel[i]))));done.push(and(lookup(addr),enable))}
  return {m,l,P,d,g,o:fold(done),mask,prim:d+P+m+1};
 }
 let circuits=0,slots=0,thresholds=0,semantic=0,cellChecks=0,portChecks=0,ledgerChecks=0,compressed=0,wideChecks=0,profiles=[];
 for(let m of [2,3,4])for(let l of [1,2,3])for(let mask=0;mask<1<<m;mask++){
  let C=build(m,l,mask),{P,d,g,o,prim}=C,anc=new Map,uses=new Map;
  for(let i=1;i<=prim;i++)anc.set(i,i<=d?1<<Math.floor((i-1)/l):0);
  for(let v of g){anc.set(v.i,anc.get(v.a)|anc.get(v.b));for(let a of [v.a,v.b]){if(!uses.has(a))uses.set(a,[]);uses.get(a).push(v.i)}}
  let asym=g.map(v=>pc(anc.get(v.a)^anc.get(v.b))),sum=asym.reduce((a,b)=>a+b,0);
  let global=Array.from({length:m},()=>new Set),occ=Array(m).fill(0);
  for(let v of g){for(let i=0;i<m;i++)if(((anc.get(v.a)^anc.get(v.b))>>i)&1){global[i].add((anc.get(v.a)>>i&1)?v.b:v.a);occ[i]++}}
  assert(sum===occ.reduce((a,b)=>a+b,0)&&sum>=m*P&&global.every(s=>s.size>=P),"global ledger");ledgerChecks++;
  let stats=[];
  // For every support threshold and slot, check the exact dictionary/port maps.
  for(let r=2;r<=m;r++){
   let low=g.filter(v=>pc(anc.get(v.i))<r),lowIDs=new Set(low.map(v=>v.i)),hi=g.filter(v=>!lowIDs.has(v.i));
   let ports=[...anc.keys()].filter(i=>anc.get(i)&&pc(anc.get(i))<r&&(uses.get(i)||[]).some(j=>!lowIDs.has(j)));
   let demand=0,Z=0,highDemand=0,Lsum=0,lowAsym=0,highAsym=0;
   for(let v of low)lowAsym+=pc(anc.get(v.a)^anc.get(v.b));for(let v of hi)highAsym+=pc(anc.get(v.a)^anc.get(v.b));
   for(let i=0;i<m;i++){
    let K=ports.filter(v=>anc.get(v)>>i&1),side=new Set,lowocc=0;
    for(let v of low)if((anc.get(v.a)^anc.get(v.b))>>i&1){side.add(anc.get(v.a)>>i&1?v.b:v.a);lowocc++}
    let floor=K.length<l?P-2**K.length+1:0;assert(K.length>=1&&side.size>=floor&&lowocc>=side.size,"local ingress");
    if(floor){Z++;compressed++}demand+=floor;Lsum+=lowocc;highDemand+=Math.max(0,P-lowocc);
    let maps=new Map,decode=new Map;
    for(let h=0;h<1<<P;h++){
     let code=null,values=[];
     for(let x=0;x<P;x++){let w=[0];for(let k=0;k<d;k++)w.push(Math.floor(k/l)===i?(x>>(k%l)&1):0);for(let k=0;k<P;k++)w.push(h>>k&1);for(let k=0;k<m;k++)w.push(Number(k===i));w.push(Number(!(mask>>i&1)));
      for(let v of g)w[v.i]=(w[v.a]^v.pa)&(w[v.b]^v.pb);
      assert((w[o>>1]^(o&1))===(h>>x&1),"hybrid function");semantic++;
      let a=[...side].map(j=>w[j]).join(""),b=K.map(j=>w[j]).join("");if(code===null)code=a;else assert(code===a,"side independence");values.push(b);
      let key=h+":"+b,val=h>>x&1;if(decode.has(key))assert(decode.get(key)===val,"port partition");else decode.set(key,val);portChecks++;
     }
     if(maps.has(code))assert(maps.get(code)===values.join(","),"fixed map");else maps.set(code,values.join(","));cellChecks++;
    }
    slots++;
   }
   assert(lowAsym===Lsum&&lowAsym+highAsym===sum,"disjoint asymmetry");
   assert(lowAsym>=demand&&low.length*(r-1)>=lowAsym&&demand>=Z*(P/2+1),"weighted low region");
   assert(highAsym>=highDemand,"high residual reserve");wideChecks++;
   thresholds++;stats.push({r,Z,low:low.length,high:hi.length,lowAsym,highAsym,highDemand});
  }
  if(m===4&&l===3&&[0,3,15].includes(mask))profiles.push({mask,gates:g.length,sumAsym:sum,global:global.map(s=>s.size),stats});
  circuits++;
 }
 return {seed:870058,circuits,slots,thresholds,semantic,cellChecks,portChecks,ledgerChecks,compressed,wideChecks,profiles}
}
console.log(JSON.stringify(replay(),null,2));

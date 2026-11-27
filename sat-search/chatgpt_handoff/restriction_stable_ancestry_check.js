"use strict";
// Optimistic restriction quotient and restriction-stable selector matching regression.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870046;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 // Primaries 1..d are data, next q query, 0 fixed. Signed literal = 2*ID+phase.
 const lit=(i,p=0)=>2*i+p,id=l=>l>>1;
 const gate=(tt,a,b)=>tt>>((a<<1)|b)&1;
 const proper=t=>[0,1].some(b=>gate(t,0,b)!==gate(t,1,b))&&[0,1].some(a=>gate(t,a,0)!==gate(t,a,1));
 const ts=Array.from({length:16},(_,i)=>i).filter(proper);
 function builder(d,q){let g=[],next=d+q+1;return {x:i=>lit(i+1),q:i=>lit(d+1+i),add:(a,b,t=8)=>{let i=next++;g.push({i,a,b,t});return lit(i)},done:o=>({d,q,g:g.slice(),o})}}
 function prune(C){let live=new Set([id(C.o)]);for(let k=C.g.length-1;k>=0;k--){let g=C.g[k];if(live.has(g.i)){live.add(id(g.a));live.add(id(g.b))}}return {...C,g:C.g.filter(g=>live.has(g.i))}}
 function optimistic(C,S){let rep=new Map([[0,0]]),g=[];for(let i=1;i<=C.d+C.q;i++)rep.set(i,i<=C.d&&(S>>BigInt(i-1)&1n)?0:i);
  for(let v of C.g){let a=rep.get(id(v.a)),b=rep.get(id(v.b));assert(a!==undefined&&b!==undefined,"topo");
   let r=!a?b:!b?a:a===b?a:v.i;if(r===v.i)g.push({...v,a:lit(a),b:lit(b)});rep.set(v.i,r)}
  return {C:prune({...C,g,o:lit(rep.get(id(C.o)))}),rep};
 }
 function actual(C,S,values){let rep=new Map([[0,0]]),g=[];for(let i=1;i<=C.d+C.q;i++)rep.set(i,i<=C.d&&(S>>BigInt(i-1)&1n)?Number(values>>BigInt(i-1)&1n):lit(i));
  const get=l=>rep.get(id(l))^(l&1);
  for(let v of C.g){let a=get(v.a),b=get(v.b),vs=[...new Set([id(a),id(b)].filter(Boolean))],z=[];for(let w=0;w<1<<vs.length;w++){let read=l=>(id(l)?w>>vs.indexOf(id(l))&1:0)^(l&1);z.push(gate(v.t,read(a),read(b)))}
   let r=null;if(z.every(w=>w===z[0]))r=z[0];else for(let j=0;j<vs.length;j++)for(let p=0;p<2;p++)if(z.every((w,i)=>w===((i>>j&1)^p)))r=lit(vs[j],p);
   if(r===null){assert(vs.length===2,"proper residual");r=lit(v.i);g.push({...v,a,b})}rep.set(v.i,r)}
  return {C:prune({...C,g,o:get(C.o)}),rep};
 }
 function ancestry(C,S=0n){let A=new Map([[0,0n]]),G=new Map;for(let i=1;i<=C.d+C.q;i++)A.set(i,i<=C.d&&!(S>>BigInt(i-1)&1n)?1n<<BigInt(i-1):0n);
  for(let {i,a,b} of C.g){let s=A.get(id(a))|A.get(id(b));A.set(i,s);G.set(i,s)}return G;
 }
 function reach(C,s,avoid=0){let R=new Set([s]);for(let g of C.g)if(g.i!==avoid&&(R.has(id(g.a))||R.has(id(g.b))))R.add(g.i);return R}
 function pc(x){let n=0;while(x){x&=x-1n;n++}return n}
 function actualValue(C,x,q){let w=[0];for(let i=0;i<C.d;i++)w.push(x>>i&1);for(let i=0;i<C.q;i++)w.push(q>>i&1);let read=l=>(w[id(l)]||0)^(l&1);for(let g of C.g)w[g.i]=gate(g.t,read(g.a),read(g.b));return read(C.o)}
 function matching(C,S,exempt){let A=ancestry(C,S),tok=[];for(let i=0;i<C.d;i++)if(!(S>>BigInt(i)&1n)){tok.push(i);if(i!==exempt)tok.push(i)}
  let M=new Map;function aug(k,seen){for(let [g,s] of A)if((s>>BigInt(tok[k])&1n)&&!seen.has(g)){seen.add(g);if(!M.has(g)||aug(M.get(g),seen)){M.set(g,k);return true}}return false}
  return tok.reduce((n,_,i)=>n+Number(aug(i,new Set)),0)
 }
 let random=0,restrictions=0,truth=0,contain=0,ancestryChecks=0,strict=0,collision=0;
 for(let z=0;z<300;z++){
  let d=2+rnd(5),q=1+rnd(3),b=builder(d,q),available=[0,1,...Array.from({length:d+q},(_,i)=>lit(i+1))],n=2+rnd(10);
  for(let i=0;i<n;i++){let a=available[rnd(available.length)]^rnd(2),c=available[rnd(available.length)]^rnd(2);available.push(b.add(a,c,ts[rnd(ts.length)]))}
  let C=prune(b.done(available[available.length-1]));
  for(let j=0;j<8;j++){
   let S=BigInt(rnd(1<<d)),v=BigInt(rnd(1<<d))&S,O=optimistic(C,S),A=actual(C,S,v),OA=ancestry(O.C,S),AA=ancestry(A.C,S);
   let Oids=new Set(O.C.g.map(g=>g.i));
   assert(A.C.g.every(g=>Oids.has(g.i)),"actual subset optimistic live");contain++;
   for(let [g,s] of AA){assert((s&~OA.get(g))===0n,"actual ancestry subset");ancestryChecks++}
   if(A.C.g.length<O.C.g.length)strict++;
   let direct=C.g.filter(g=>[id(g.a),id(g.b)].some(i=>i>0&&i<=d&&(S>>BigInt(i-1)&1n))).length;
   if(C.g.length-O.C.g.length>direct)collision++;
   for(let k=0;k<16;k++){let x=rnd(1<<d),y=rnd(1<<q),fixed=(BigInt(x)&~S)|v;assert(actualValue(C,Number(fixed),y)===actualValue(A.C,x,y),"restriction semantics");truth++}
   restrictions++;
  }random++;
 }
 // Valid selector controls: one-hot gate + OR tree, binary mux trees in AND/OR and XOR styles.
 function selector(k,style){let D=1<<k,b=builder(D,style===0?D:k),a=[];
  if(style===0){for(let i=0;i<D;i++)a.push(b.add(b.x(i),b.q(i),8));while(a.length>1)a=[b.add(a[0],a[1],14),...a.slice(2)];return b.done(a[0])}
  a=Array.from({length:D},(_,i)=>b.x(i));for(let j=0;j<k;j++){let c=[];for(let i=0;i<a.length;i+=2){let q=b.q(j);c.push(style===1?b.add(b.add(a[i],q^1,8),b.add(a[i+1],q,8),14):b.add(a[i],b.add(b.add(a[i],a[i+1],6),q,8),6))}a=c}return b.done(a[0])
 }
 let controls=0,controlMasks=0,controlMatch=0,controlSubsets=0;
 for(let k=1;k<=3;k++)for(let style=0;style<3;style++){
  let C=selector(k,style),D=C.d,full=(1n<<BigInt(D))-1n;for(let S=0n;S<full;S++){let O=optimistic(C,S).C,R=full^S,A=ancestry(O,S);if(pc(R)<2)continue;
   for(let T=R;T;T=(T-1n)&R){let have=[...A.values()].filter(x=>x&T).length;assert(have>=2*pc(T)-Number(T===R),"control subset after restriction");controlSubsets++}
   for(let e=0;e<D;e++)if(R>>BigInt(e)&1n){assert(matching(O,S,e)===2*pc(R)-1,"control matching");controlMatch++}controlMasks++
  }controls++;
 }
 // Separation family. m encoded leaves (hub + private data) paired with m query-gated leaves, plus hub gated.
 function obstruction(m){let D=2*m+1,b=builder(D,m+1),u=[],qports=[],ports=[];
  let hub=b.add(b.x(0),b.q(0));qports.push(id(b.x(0)));
  for(let i=1;i<=m;i++){let a=b.add(b.x(0),b.x(i),6),c=b.add(b.x(m+i),b.q(i),8);ports.push(id(a),id(b.x(m+i)));u.push(b.add(a,c,14))}
  let out=hub;for(let a of u)out=b.add(out,a,14);return b.done(out);
 }
 let examples=[],oldMatch=0,oldSubset=0,dominator=0;
 for(let m of [2,3,4,8,16,32]){
  let C=obstruction(m),D=C.d,A=ancestry(C),S=1n,O=optimistic(C,S).C,AO=ancestry(O,S),needed=2*(D-1)-1,have=[...AO.values()].filter(Boolean).length;
  assert(C.g.length===2*D-1&&have===2*D-m-2&&needed-have===m-1,"separation");
  for(let e=0;e<D;e++){assert(matching(C,0n,e)===2*D-1,"old all exemption matchings");oldMatch++}
  if(D<=9)for(let T=1n;T<1n<<BigInt(D);T++){assert([...A.values()].filter(x=>x&T).length>=2*pc(T)-Number(pc(T)===D),"old all subsets");oldSubset++}
  for(let i=1;i<D;i++){let rs=C.g.filter(g=>id(g.a)===i+1||id(g.b)===i+1);assert(rs.length===1,"sole");
   for(let j=0;j<D;j++)if(j!==i){assert(reach(C,j+1,rs[0].i).has(id(C.o)),"sole reader domination passes");dominator++}}
  let encoded=new Set;for(let x=0;x<1<<Math.min(D,9);x++){if(D>9)break;let a=x&1,w=a;for(let i=1;i<=m;i++)w|=((x>>i&1)^a)<<i;for(let i=m+1;i<D;i++)w|=(x>>i&1)<<i;encoded.add(w)}if(D<=9)assert(encoded.size===1<<D,"injective first query cut");
  examples.push({m,D,gates:C.g.length,queryPorts:m+1,remaining:have,needed,deficit:needed-have})
 }
 return {seed:870046,random,restrictions,truth,contain,ancestryChecks,strict,collision,controls,controlMasks,controlMatch,controlSubsets,oldMatch,oldSubset,dominator,examples}
}
console.log(JSON.stringify(replay(),null,2));

"use strict";
// Exhaustive raw carrier and branch replacement checks for one-junk completion.
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)},pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 let graphs=0,oneCarrier=0,singleHomogeneous=0,singleMixed=0,singleRedundant=0,largeProtected=0,largeUnprotected=0,oneReplace=0,oneTruncate=0,twoCarrier=0,twoTruncate=0,overlapReplace=0,rawClean=0,edgeChecks=0;
 for(let [l,r] of [[2,2],[2,3],[3,3]]){
 const n=l+r,V=1<<n,L=(1<<l)-1,T=Array(V).fill(0n);for(let s=1;s<V;s++)for(let x=0;x<V;x++)if(s&x)T[s]|=1n<<BigInt(x);
 for(let g=1;g<1<<(l*r);g++){
 let N=Array(n).fill(0),edges=[];for(let i=0;i<l;i++)for(let j=0;j<r;j++)if(g>>(i*r+j)&1){N[i]|=1<<(l+j);N[l+j]|=1<<i;edges.push((1<<i)|(1<<(l+j)))}if(N.some((a,i)=>N.some((b,j)=>i<j&&pc(a&b)>1)))continue;graphs++;
 let F=0n;for(let x=0;x<V;x++)if(edges.some(e=>(x&e)===e))F|=1n<<BigInt(x);
 const clean=f=>(f&~F)===0n,ep=f=>edges.reduce((a,e,i)=>a|(((f>>BigInt(e))&1n)<<BigInt(i)),0n),neighbors=s=>N.reduce((a,b,i)=>s>>i&1?a&b:a,V-1),mixed=s=>!!(s&L)&&!!(s&~L),single=s=>s&&!(s&(s-1));
 for(let A=1;A<V;A++)for(let B=A;B<V;B++){
 let J=T[A]&T[B];if(clean(J)||(A&B)===A||(A&B)===B)continue;
 let U=0;for(let c=0;c<n;c++)if(clean(J&T[1<<c]))U|=1<<c;
 if(!U)continue;let I=A&B;
 if(I){
  if(pc(I)>=2){assert(single(U),"unique overlap cleaner");let c=Math.log2(U),S=(U&A)?B:A,R=S&N[c];assert(clean(T[R]&T[U])&&(ep(J&T[U])&~ep(T[R]&T[U]))===0n,"overlap large rewrite");overlapReplace++}
  else{let E=(A|B)&U;if(E){assert(single(E),"one exposed");let S=E&A?B:A;assert((S&N[Math.log2(E)])===S,"overlap exposed provider");let f=(T[I]&T[U])|(T[E]&T[S^I]);assert(clean(f)&&(ep(J&T[U])&~ep(f))===0n,"overlap small rewrite")}else assert(ep(J&T[U])===ep(T[I]&T[U]),"overlap no exposed");overlapReplace++}
  continue;
 }
 let aSet=A&U,bSet=B&U,records=[];
 for(let D=1;D<V;D++){
 let C=U&neighbors(D);if(!C)continue;assert(clean((J|T[D])&T[C]),"all eligible C");rawClean++;
 let useful=ep(J&T[C]);if(!useful)continue;oneCarrier++;
 if(single(A)||single(B)){
 let a=single(A)?A:B,S=a===A?B:A,bits=S&C&N[Math.log2(a)];
 if(D&a){assert((useful&~ep(T[D]&T[C]))===0n,"redundant singleton");singleRedundant++;continue}
 assert(!(a&C)&&single(bits),"sole carrier singleton unique edge");
 if(!mixed(S)){assert(clean(T[a]&T[C]),"homogeneous singleton expansion");assert((useful&~ep(T[a]&T[C]))===0n,"singleton coverage");singleHomogeneous++}
 else{assert(!neighbors(S),"mixed root exclusive in residual");assert(clean(T[a]&T[bits])&&(useful&~ep(T[a]&T[bits]))===0n,"mixed singleton edge");singleMixed++}
 continue;
 }
 let ac=C&A,bc=C&B;assert(!(ac&&bc),"single carrier one centre");let center=ac||bc,S=ac?B:A,W=ac?A:B;assert(single(center),"one centre");records.push({D,C,center,S,W,useful});
 if(!neighbors(W)){largeUnprotected++;continue}
 assert(!mixed(W),"protected root homogeneous");largeProtected++;let universals=S&neighbors(W),non=S&~universals;assert(pc(universals)<=1&&non,"C4 unique universal");
 assert((C&neighbors(non))===C,"all cleaners adjacent nonuniversal");
 let R=S;if(!clean(T[S]&T[C])){assert(pc(non)===1&&pc(S)===2&&single(universals),"truncation only size two");R=non;oneTruncate++}else oneReplace++;
 assert(clean(T[R]&T[C]),"replacement clean");assert((useful&~(ep(T[R]&T[C])|ep(T[W]&T[universals])))===0n,"protected root central rescue");edgeChecks++;
 }
 if(!single(A)&&!single(B)&&aSet&&bSet){assert(single(aSet)&&single(bSet),"global two centres");
 const aa=records.filter(x=>x.center===aSet),bb=records.filter(x=>x.center===bSet);
 for(let x of aa)for(let y of bb){
 twoCarrier++;let rx=clean(T[B]&T[x.C])?B:B&~bSet,ry=clean(T[A]&T[y.C])?A:A&~aSet;
 assert(clean(T[rx]&T[x.C])&&clean(T[ry]&T[y.C]),"branch rewrite clean");
 let lost=(x.useful|y.useful)&~(ep(T[rx]&T[x.C])|ep(T[ry]&T[y.C]));
 let central=ep(T[aSet]&T[bSet]);assert((lost&~central)===0n,"only central lost");
 if(lost){assert(pc(A)===2&&pc(B)===2&&rx!==B&&ry!==A,"both truncation");twoTruncate++}edgeChecks++;
 }
 }
 }
 }
 }
 return {graphs,oneCarrier,singleHomogeneous,singleMixed,singleRedundant,largeProtected,largeUnprotected,oneReplace,oneTruncate,twoCarrier,twoTruncate,overlapReplace,rawClean,edgeChecks}
}
console.log(JSON.stringify(replay(),null,2));

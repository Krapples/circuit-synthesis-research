"use strict";
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};const pc=x=>{let c=0;for(;x;x&=x-1)c++;return c};
 let graphs=0,overlap=0,reader=0,multi=0,single=0,exposed=0,noExposed=0,singleton=0,filter=0,carrier=0,strictDirect=0,profiles=[];
 for(let [l,r] of [[2,2],[2,3],[3,3]]){
 let n=l+r,V=1<<n,T=Array(V).fill(0n);for(let s=1;s<V;s++)for(let x=0;x<V;x++)if(s&x)T[s]|=1n<<BigInt(x);
 for(let mask=1;mask<1<<(l*r);mask++){let N=Array(n).fill(0),edges=[];for(let i=0;i<l;i++)for(let j=0;j<r;j++)if(mask>>(i*r+j)&1){N[i]|=1<<(l+j);N[l+j]|=1<<i;edges.push((1<<i)|(1<<(l+j)))}if(N.some((a,i)=>N.some((b,j)=>i<j&&pc(a&b)>1)))continue;graphs++;let F=0n;for(let x=0;x<V;x++)if(edges.some(e=>(x&e)===e))F|=1n<<BigInt(x);
 const clean=f=>(f&~F)===0n;const edgeEq=(a,b)=>edges.every(e=>((a^b)>>BigInt(e)&1n)===0n);
 for(let c=0;c<n;c++)for(let S=1;S<V;S++)if(pc(S)>=2)for(let d=0;d<n;d++)if((S&N[d])===S){assert((S&N[c])===S||pc(S&N[c])<=1,"protected filter");filter++}
 for(let A=1;A<V;A++)for(let B=A;B<V;B++){
 let J=T[A]&T[B];if(clean(J))continue;let I=A&B,valid=[];
 for(let C=1;C<V;C++)if(clean(J&T[C]))valid.push(C);
 if(!valid.length)continue;
 if(I){overlap++;let U=valid.reduce((a,b)=>a|b,0);for(let i=0;i<n;i++)if(I>>i&1)assert((U&N[i])===U,"overlap cleaner");
 if(pc(I)>=2){multi++;assert(pc(U)===1,"unique cleaner");let c=Math.log2(U),S=(U&A)?B:A,R=S&N[c];for(let C of valid){assert(clean(T[R]&T[C])&&edges.every(e=>!((J&T[C])>>BigInt(e)&1n)||!!((T[R]&T[C])>>BigInt(e)&1n)),"multi replacement");reader++}}
 else{single++;let a=I,EA=A&U,EB=B&U;assert(pc(EA)+pc(EB)<=1||pc(A)===1||pc(B)===1,"single intersection exposed");if((A===I)||(B===I))continue;let E=EA|EB;if(!E){noExposed++;for(let C of valid){assert(clean(T[I]&T[C])&&edgeEq(J&T[C],T[I]&T[C]),"single no exposure");reader++}}else{exposed++;let S=EA?B:A,c=Math.log2(E);assert((S&N[c])===S&&pc(E)===1,"exposed star");for(let C of valid){let replacement=(T[I]&T[C])|(T[E]&T[S]);assert(clean(replacement)&&edges.every(e=>!((J&T[C])>>BigInt(e)&1n)||!!(replacement>>BigInt(e)&1n)),"single exposure");reader++}}}
 }else if(pc(A)===1||pc(B)===1){singleton++;let a=pc(A)===1?A:B,S=a===A?B:A,c=Math.log2(a),R=S&N[c];for(let C of valid){assert(!(C&a),"dirty singleton center unavailable");assert(clean(T[a]&T[R])&&edges.every(e=>!((J&T[C])>>BigInt(e)&1n)||!!((T[a]&T[R])>>BigInt(e)&1n)),"singleton coverage");reader++;strictDirect++}}
 else{
 let EA=A&valid.reduce((a,b)=>a|b,0),EB=B&valid.reduce((a,b)=>a|b,0);if(!EA||!EB)continue;
 assert(pc(EA)===1&&pc(EB)===1,"two centers");for(let D=1;D<V;D++){let va=valid.some(C=>(C&EA)&&clean((J|T[D])&T[C])),vb=valid.some(C=>(C&EB)&&clean((J|T[D])&T[C]));assert(!(va&&vb),"carrier cannot expose both");carrier++}
 }
 }
 }profiles.push({l,r,graphs})
 }
 return {graphs,overlap,reader,multi,single,exposed,noExposed,singleton,filter,carrier,strictDirect,profiles}
}
console.log(JSON.stringify(replay(),null,2));

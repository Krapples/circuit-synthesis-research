"use strict";
// Unsafe full-provider replacement implies an exposed star is redundant.
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)},pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 let graphs=0,pairs=0,truncations=0,redundant=0,bothNeeded=0,fullSafe=0;
 for(let [l,r] of [[2,2],[2,3],[3,3]]){let n=l+r,V=1<<n,T=Array(V).fill(0n);for(let s=1;s<V;s++)for(let x=0;x<V;x++)if(x&s)T[s]|=1n<<BigInt(x);
 for(let mask=1;mask<1<<(l*r);mask++){let N=Array(n).fill(0),E=[];for(let i=0;i<l;i++)for(let j=0;j<r;j++)if(mask>>(i*r+j)&1){N[i]|=1<<(l+j);N[l+j]|=1<<i;E.push((1<<i)|(1<<(l+j)))}if(N.some((a,i)=>N.some((b,j)=>i<j&&pc(a&b)>1)))continue;graphs++;let F=0n;for(let x=0;x<V;x++)if(E.some(e=>(e&x)===e))F|=1n<<BigInt(x);
 const clean=x=>(x&~F)===0n,ep=x=>E.reduce((z,e,i)=>z|(((x>>BigInt(e))&1n)<<BigInt(i)),0n),common=S=>N.reduce((a,b,i)=>S>>i&1?a&b:a,V-1);
 for(let A=1;A<V;A++)for(let B=A+1;B<V;B++){if((A&B)||pc(A)<2||pc(B)<2)continue;let a=A&common(B),b=B&common(A);if(!a||!b)continue;assert(pc(a)===1&&pc(b)===1,"centres");let J=T[A]&T[B],U=0;for(let c=0;c<n;c++)if(clean(J&T[1<<c]))U|=1<<c;
 let aStar=ep(T[a]&T[B]),bStar=ep(T[b]&T[A]),aa=[],bb=[];
 for(let D=1;D<V;D++){let C=U&common(D);if(!C)continue;if(C&a)aa.push({D,C,raw:ep(T[D]&T[C])});if(C&b)bb.push({D,C,raw:ep(T[D]&T[C])})}
 for(let x of aa)for(let y of bb){pairs++;let raw=x.raw|y.raw,needA=!!(aStar&~(raw|bStar)),needB=!!(bStar&~(raw|aStar)),safeA=clean(T[B]&T[x.C]),safeB=clean(T[A]&T[y.C]);
 if(!safeA){truncations++;assert(pc(B)===2&&x.D===(B^b)&&!needA,"A star redundant if unsafe");redundant++}
 if(!safeB){truncations++;assert(pc(A)===2&&y.D===(A^a)&&!needB,"B star redundant if unsafe");redundant++}
 if(needA&&needB){bothNeeded++;assert(safeA&&safeB,"both needed forces full safety");let old=ep((J|T[x.D])&T[x.C])|ep((J|T[y.D])&T[y.C]),nw=ep((T[B]|T[x.D])&T[x.C])|ep((T[A]|T[y.D])&T[y.C]);assert((old&~nw)===0n,"both branches preserve");fullSafe++}
 }
 }
 }}
 return {graphs,pairs,truncations,redundant,bothNeeded,fullSafe}
}
console.log(JSON.stringify(replay(),null,2));

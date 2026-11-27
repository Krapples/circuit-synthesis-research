"use strict";
// Fixed-coordinate triangle incidence, balanced cut matching, and cofactor checks.
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};let seed=870061;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function layout(A){let m=1;while(m<3*A*A+9*(A-1)+4)m*=2;let P=16*A,l=Math.log2(P),t=3*m,Q=1;while(Q<(t+2)*P+t+1)Q*=2;let w=Math.log2(Q)+1,base=Q+(t+2)*P;return {A,m,P,l,t,Q,w,base,mode:base+t}}
 function make(L){let {A,m}=L,f=3*A,next=f+1,C=[],free=[];let p=v=>2*v,n=v=>2*v+1;function cl(...a){while(a.length<3)a.push(p(f));C.push(a)}
 cl(n(f),n(f),n(f));
 // layers X(i,j), Y(j,k), Z(k,i), third literal sign is the free edge bit.
 for(let s=0;s<3;s++)for(let i=0;i<A;i++)for(let j=0;j<A;j++){free.push(3*C.length+2);cl(n(s*A+i),n(((s+1)%3)*A+j),p(f))}
 for(let s=0;s<3;s++){let u=p(s*A);for(let i=1;i<A;i++){let v=p(s*A+i),y=p(next++);cl(u^1,y);cl(v^1,y);cl(y^1,u,v);u=y}cl(u)}
 assert(next<=L.P/2&&C.length<=m,"capacity");while(C.length<m)C.push([p(f),n(f),p(f)]);return {C,free}}
 function data(B,x){let a=B.C.flat();for(let i=0;i<B.free.length;i++)a[B.free[i]]^=x[i];return a}
 function sat(C){while(true){if(C.some(a=>!a.length))return false;if(!C.length)return true;let a=C.find(a=>a.length===1);if(!a)break;let [v,s]=a[0];C=C.filter(a=>!a.some(([u,t])=>u===v&&s===t)).map(a=>a.filter(([u])=>u!==v))}
 let [v]=C.reduce((a,b)=>a.length<=b.length?a:b)[0];return [0,1].some(s=>sat([...C,[[v,s]]]))}
 function logical(L,a){return sat(Array.from({length:L.m},(_,i)=>a.slice(3*i,3*i+3).map(z=>[z>>1,1^(z&1)])))}
 function triangle(A,x){for(let i=0;i<A;i++)for(let j=0;j<A;j++)for(let k=0;k<A;k++)if(x[i*A+j]&&x[A*A+j*A+k]&&x[2*A*A+k*A+i])return true;return false}
 function encode(L,v){let W=[],pos=[];const lit=(u,s)=>{assert(u.toString(2).length===L.w,"width");W.push(1,s);for(let j=0;j<L.w;j++)W.push(1,(u>>j)&1);W.push(0,1)},cl=A=>{for(let [u,s] of A)lit(u,s);W.push(0,0)};
 for(let a=0;a<L.P;a++)cl([[L.Q+a,0]]);for(let a=0;a<L.P;a+=2){let u=L.Q+L.P+a;cl([[u,1],[u+1,1]]);cl([[u,0],[u+1,0]])}cl([[L.mode,0]]);
 for(let j=0;j<L.m;j++){let z=L.base+3*j;cl([[z,1],[z+1,1],[z+2,1]]);for(let a=0;a<3;a++){let i=3*j+a;cl([[L.mode,0],[z+a,1]]);lit(z+a,0);pos[i]=W.length+3;lit(L.Q+L.P+v[i],1);W.push(0,0)}}
 assert(W.length===(3*L.P+15*L.m+1)*(2*L.w+4)+2*(2*L.P+7*L.m+1),"length");return {W,pos}}
 function parse(W){let C=[],a=[],i=0;while(i<W.length){if(!W[i]){assert(W[i+1]===0&&a.length,"clause");C.push(a);a=[];i+=2;continue}let s=W[i+1],v=0,p=1;i+=2;while(W[i]){v+=p*W[i+1];p*=2;i+=2}assert(W[i+1]===1&&v>=p/2,"literal");i+=2;a.push([v,s])}assert(!a.length,"end");return C}
 let logicalChecks=0,physical=0,positions=0,mutations=0,yes=0,maxLength=0;
 for(let A of [2,4]){let L=layout(A),B=make(L),D=3*A*A,n=A===2?2**D:120;
 for(let z=0;z<n;z++){let x=Array.from({length:D},(_,i)=>A===2?z>>i&1:rnd(2)),v=data(B,x),want=triangle(A,x);assert(logical(L,v)===want,"triangle logical");logicalChecks++;yes+=want;
 if(z<12){let W=encode(L,v);assert(sat(parse(W.W))===want,"triangle physical");physical++;maxLength=Math.max(maxLength,W.W.length);for(let i=0;i<D;i++){assert(W.W[W.pos[B.free[i]]]===x[i],"edge coordinate");positions++}let k=rnd(D),x1=x.slice();x1[k]^=1;let V=encode(L,data(B,x1));assert(W.W.every((v,i)=>i===W.pos[B.free[k]]?v!==V.W[i]:v===V.W[i]),"one edge bit");mutations++}
 }}
 function permutations(A){let out=[];function r(a){if(a.length===A){out.push(a);return}for(let i=0;i<A;i++)if(!a.includes(i))r(a.concat(i))}r([]);return out}
 let cuts=0,deltaChecks=0,matchingChecks=0,cofactors=0,minRatio=Infinity,profiles=[];
 for(let A of [2,3,4,5]){let D=3*A*A,perms=permutations(A),n=A===2?2**D:300;
 for(let z=0;z<n;z++){let side=Array.from({length:D},(_,i)=>A===2?z>>i&1:rnd(2)),count=side.reduce((a,b)=>a+b,0);if(!count||count===D)continue;
 let delta=[],best={r:-1};for(let s=0;s<3;s++){let p=s*A*A,q=((s+1)%3)*A*A,n=0;for(let i=0;i<A;i++)for(let j=0;j<A;j++)for(let k=0;k<A;k++)n+=side[p+i*A+j]!==side[q+j*A+k]?1:0;delta.push(n/A**3);
 let total=0;for(let pi of perms){let pairs=[];for(let i=0;i<A;i++)for(let j=0;j<A;j++){let a=p+i*A+j,b=q+j*A+pi[i];if(side[a]!==side[b])pairs.push([a,b])}total+=pairs.length;if(pairs.length>best.r)best={r:pairs.length,s,pi,pairs};matchingChecks++}
 assert(total===n*perms.length/A,"average exact");
 }
 let p=count/D,ds=delta.reduce((a,b)=>a+b,0);assert(ds+1e-9>=2*p*(1-p),"cut expansion");assert(best.r+1e-9>=A*A*2*p*(1-p)/3,"matching floor");minRatio=Math.min(minRatio,best.r/(A*A*2*p*(1-p)/3));deltaChecks++;
 let x=Array(D).fill(0);for(let i=0;i<A;i++)x[((best.s+2)%3)*A*A+best.pi[i]*A+i]=1;
 let r=best.r,num=r<=5?2**(2*r):20;
 for(let z=0;z<num;z++){let y=x.slice(),want=false;for(let i=0;i<r;i++){let a=r<=5?z>>i&1:rnd(2),b=r<=5?z>>(r+i)&1:rnd(2);y[best.pairs[i][0]]=a;y[best.pairs[i][1]]=b;want||=!!(a&b)}assert(triangle(A,y)===want,"matching cofactor");cofactors++}cuts++;
 }
 profiles.push({A,partitions:n});
 }
 return {seed:870061,logicalChecks,physical,positions,mutations,yes,maxLength,cuts,deltaChecks,matchingChecks,cofactors,minRatio,profiles}
}
console.log(JSON.stringify(replay(),null,2));

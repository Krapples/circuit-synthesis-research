"use strict";
// Exact finite replay. Run node two_sided_degree_rank_check.js.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};
 let seed=870031;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n};
 const bit=i=>1n<<BigInt(i);
 const pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 const rank=vs=>{let p=new Map;for(let v of vs){while(v){let k=v.toString(2).length-1;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}}return p.size};
 const C=(n,k)=>{if(k<0||k>n)return 0n;let v=1n;for(let i=1;i<=k;i++)v=v*BigInt(n-i+1)/BigInt(i);return v};
 const sum=(n,l,h)=>{let v=0n;for(let i=Math.max(0,l);i<=Math.min(n,h);i++)v+=C(n,i);return v};
 function cap(t,rd,rq,L,M){let best=null;for(let k=0;k<=t;k++){let v=sum(rd,L,k)+sum(rq,M,t-k);if(best===null||v<best)best=v}return best}
 function matrixRank(coeff,d,k,r,s){
   let mask=0n;for(let q=1;q<1<<k;q++)if(pc(q)>=s)mask|=bit(q);
   let rows=[];for(let x=1;x<1<<d;x++)if(pc(x)>=r)rows.push(coeff[x]&mask);
   return rank(rows)
 }
 function anf(d,k,fn){
   let N=1<<(d+k),a=Uint8Array.from({length:N},(_,i)=>fn(i&((1<<d)-1),i>>d));
   for(let j=0;j<d+k;j++)for(let i=0;i<N;i++)if(i>>j&1)a[i]^=a[i^(1<<j)];
   let rows=Array(1<<d).fill(0n);for(let i=0;i<N;i++)if(a[i])rows[i&((1<<d)-1)]|=bit(i>>d);
   return rows
 }
 let circuits=0,frontiers=0,strictRankCuts=0,zeroCaps=0,rectangles=0,rectangleFrontiers=0,profileRejections=0;
 function check(d,k,g,out){
   const off=1+d+k;
   let support=[0,...Array(d).fill(1),...Array(k).fill(2)],classes=[],di=[],qi=[],a=0,b=0,t=0;
   for(let i=0;i<g.length;i++){
     const [u,v]=g[i];let su=0;for(let j=0;j<off+i;j++)if((u|v)&bit(j))su|=support[j];
     support.push(su);classes.push(su);
     if(su===0)continue;
     if(su===1)a++;else if(su===2)b++;else{
       t++;
       for(let mask of [u,v]){
         let x=0n,y=0n;
         for(let j=1;j<off+i;j++)if(mask&bit(j)){if(support[j]===1)x|=bit(j);if(support[j]===2)y|=bit(j)}
         di.push(x);qi.push(y)
       }
     }
   }
   let rd=rank(di),rq=rank(qi);
   const evalf=(x,q)=>{let w=1n|(BigInt(x)<<1n)|(BigInt(q)<<BigInt(1+d));for(let i=0;i<g.length;i++){let f=m=>pcBig(m&w)&1;if(f(g[i][0])&&f(g[i][1]))w|=bit(off+i)}return pcBig(out&w)&1};
   const pcBig=x=>{let n=0;while(x){x&=x-1n;n++}return n};
   const coeff=anf(d,k,evalf);
   for(let r=1;r<=d;r++)for(let s=1;s<=k;s++){
     let L=Math.max(1,r-a),M=Math.max(1,s-b),R=matrixRank(coeff,d,k,r,s),B=cap(t,rd,rq,L,M);
     assert(BigInt(R)<=B,"rank frontier");assert(L+M<=t+1||R===0,"degree frontier");
     let left=sum(rd,L,t+1-M),right=sum(rq,M,t+1-L);
     if(B<left&&B<right)strictRankCuts++;if(B===0n)zeroCaps++;frontiers++;
   }
   circuits++;return {d,k,a,b,t,rd,rq}
 }
 for(let z=0;z<300;z++){
   let d=1+rnd(4),k=1+rnd(3),n=1+rnd(7),off=1+d+k,g=[];
   for(let i=0;i<n;i++){
     const mode=rnd(4);
     let allowed=Array.from({length:off+i},(_,j)=>j).filter(j=>mode>=2||j===0||(mode===0?j<=d:j>d&&j<off)||j>=off);
     const m=()=>allowed.reduce((x,j)=>rnd(2)?x|bit(j):x,0n);
     g.push([m(),m()])
   }
   check(d,k,g,BigInt(rnd(1<<(off+n))))
 }
 // Reused pure conjunction; all t mixed gates are live at output.
 let d=5,k=4,off=1+d+k,g=[[bit(1),bit(2)]];
 for(let i=3;i<=d;i++)g.push([bit(i),bit(off+g.length-1)]);
 const h=bit(off+g.length-1);let out=0n;
 for(let i=0;i<k;i++){out^=bit(off+g.length);g.push([h^bit(1+i),bit(1+d+i)])}
 let shared=check(d,k,g,out);
 assert(shared.a===4&&shared.t===4&&shared.rd===4&&shared.rq===4,"shared preprocessing control");
 const expected=(m,l,r,s)=>{let R=0n;for(let j=1;j<=l;j++)R+=C(l,j)*sum(m,Math.max(1,Math.ceil(r/j),s-j),m);return R};
 const witnesses=[];
 for(let m=1;m<=3;m++)for(let l=1;l<=3;l++){
   let d=m*l,k=m+l;
   let coeff=anf(d,k,(x,q)=>{let S=q&((1<<m)-1),Q=q>>m;for(let j=0;j<l;j++)if(Q>>j&1){let ok=true;for(let i=0;i<m;i++)if((S>>i&1)&&!(x>>(i*l+j)&1))ok=false;if(ok)return 1}return 0});
   // Full ANF identity, not just ranks.
   let rows=Array(1<<d).fill(0n);
   for(let J=0;J<1<<m;J++)for(let T=1;T<1<<l;T++){
     let X=0;for(let i=0;i<m;i++)for(let j=0;j<l;j++)if((J>>i&1)&&(T>>j&1))X|=1<<(i*l+j);
     for(let I=0;I<1<<m;I++)if((I&J)===J)rows[X]^=bit(I|(T<<m));
   }
   assert(rows.every((v,i)=>v===coeff[i]),"rectangle ANF");
   for(let r=1;r<=d;r++)for(let s=1;s<=k;s++){
     let R=matrixRank(coeff,d,k,r,s);assert(BigInt(R)===expected(m,l,r,s),"rectangle rank");rectangleFrontiers++;
   }
   rectangles++;witnesses.push({m,l,d,k,rank:Number(expected(m,l,1,1)),topRank:Number(expected(m,l,d,k)),totalDegree:d+k});
 }
 // Search split profiles (including a specified ingress rank) with degree and separate rank bounds but failed joint rank cut.
 let rejection=null;
 for(let m=2;m<=5;m++)for(let l=2;l<=4;l++){
   let d=m*l,k=m+l;
   for(let t=1;t<=Math.min(12,d+k);t++)for(let a=0;a<=d;a++)for(let b=0;b<=k;b++){
     if(Math.max(1,d-a)+Math.max(1,k-b)>t+1)continue;
     for(let rd=1;rd<=Math.min(2*t,d+a);rd++)for(let rq=1;rq<=Math.min(2*t,k+b);rq++){
       if(rd<d||rq<k-1)continue; // retain basic ingress cardinality demand (weaker on query side)
       let failures=[];
       for(let r=1;r<=d;r++)for(let s=1;s<=k;s++){
         let L=Math.max(1,r-a),M=Math.max(1,s-b),R=expected(m,l,r,s),B=cap(t,rd,rq,L,M);
         if(R>B&&R<=sum(rd,L,t+1-M)&&R<=sum(rq,M,t+1-L)&&R<=3n**BigInt(t))failures.push({r,s,R:String(R),B:String(B)})
       }
       if(failures.length){profileRejections++;if(!rejection)rejection={m,l,t,a,b,rd,rq,failures:failures.slice(0,3)}}
     }
     if(rejection)break
   }
   if(rejection)break
 }
 return {seed:870031,circuits,frontiers,strictRankCuts,zeroCaps,shared,rectangles,rectangleFrontiers,witnesses,profileRejections,rejection}
}
console.log(JSON.stringify(replay(),null,2));

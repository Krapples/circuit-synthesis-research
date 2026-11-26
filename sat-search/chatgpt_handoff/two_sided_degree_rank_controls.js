"use strict";
function supplemental(){
 const C=(n,k)=>{if(k<0||k>n)return 0n;let v=1n;for(let i=1;i<=k;i++)v=v*BigInt(n-i+1)/BigInt(i);return v};
 const sum=(n,l,h)=>{let v=0n;for(let i=Math.max(0,l);i<=Math.min(n,h);i++)v+=C(n,i);return v};
 function cap(t,rd,rq,L,M){let best=null;for(let k=0;k<=t;k++){let v=sum(rd,L,k)+sum(rq,M,t-k);if(best===null||v<best)best=v}return best}
 const assert=(b,m)=>{if(!b)throw Error(m)};
 const rank=vs=>{let p=new Map;for(let v of vs){while(v){let k=v.toString(2).length-1;if(p.has(k))v^=p.get(k);else{p.set(k,v);break}}}return p.size};
 // Four independent linear pairs and five independent quadratic pairs.
 const masks=[1,2,4,8,3,5,9,6,10];let coeff=Array(16).fill(0n);
 for(let i of masks)coeff[i]^=1n<<BigInt(i);
 let R=rank(coeff);assert(R===9&&cap(2,4,4,1,1)===8n&&R===3**2,"strict improvement");
 const pc=x=>{let n=0;while(x){x&=x-1;n++}return n};
 const truth=Uint8Array.from({length:256},(_,i)=>{let x=i&15,q=i>>4,z=0;for(let m of masks)z^=Number((x&m)===m&&(q&m)===m);return z});
 for(let i=0;i<8;i++)for(let j=0;j<256;j++)if(j>>i&1)truth[j]^=truth[j^(1<<i)];
 let recovered=Array(16).fill(0n),degree=0;for(let j=0;j<256;j++)if(truth[j]){recovered[j&15]|=1n<<BigInt(j>>4);degree=Math.max(degree,pc(j))}
 assert(recovered.every((v,i)=>v===coeff[i])&&degree===4,"explicit truth table");
 let checked=0,matches=[];
 for(let m=2;m<=5;m++)for(let l=2;l<=5;l++){let d=m*l,k=m+l,Rfull=((1n<<BigInt(m))-1n)*((1n<<BigInt(l))-1n)+1n;
 const expected=(r,s)=>{let R=0n;for(let j=1;j<=l;j++)R+=C(l,j)*sum(m,Math.max(1,Math.ceil(r/j),s-j),m);return R};
 let demands=[];for(let r=1;r<=d;r++)for(let s=1;s<=k;s++)demands.push([r,s,expected(r,s)]);
 for(let t=Math.ceil(d/2);t<=Math.min(12,d+k);t++){if(3n**BigInt(t)<Rfull)continue;
 for(let a=0;a<=d;a++)for(let b=0;b<=k;b++){if(Math.max(1,d-a)+Math.max(1,k-b)>t+1)continue;
 let rd=d,rq=k;if(rd>Math.min(2*t,d+a)||rq>Math.min(2*t,k+b))continue;
 checked++;
 for(let [r,s,R] of demands){let L=Math.max(1,r-a),M=Math.max(1,s-b),B=cap(t,rd,rq,L,M);if(R>B&&R<=sum(rd,L,t+1-M)&&R<=sum(rq,M,t+1-L)){matches.push({m,l,t,a,b,rd,rq,r,s,R:String(R),B:String(B)});break}}
 }}}
 return {explicit:{masks,rank:R,degree,oldRankCap:9,newRankCap:8,separateCaps:10},checked,matches:matches.slice(0,10),matchCount:matches.length}
}
console.log(JSON.stringify(supplemental(),null,2));

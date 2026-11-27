"use strict";
function replay(){
 const assert=(x,m)=>{if(!x)throw Error(m)};let seed=870054;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 let cases=0,checks=0,pairs=0,strict=0,maxGap=0;
 for(let z=0;z<1800;z++){
 let d=2+rnd(4),q=1+rnd(3),g=[],pool=Array.from({length:d+q},(_,i)=>i+1),n=2+rnd(12);
 for(let j=0;j<n;j++){let a=pool[rnd(pool.length)],b=pool[rnd(pool.length)];if(a===b){j--;continue}let i=d+q+j+1;g.push({i,a:2*a+rnd(2),b:2*b+rnd(2)});pool.push(i)}
 let cut=1+rnd(n),ports=pool.filter(i=>i<=d||i>d+q&&i<=d+q+cut).filter(i=>g.slice(cut).some(v=>v.a>>1===i||v.b>>1===i)||i===pool[pool.length-1]);
 if(!ports.length)continue;
 let A=new Map;for(let i=1;i<=d+q;i++)A.set(i,i<=d?1<<(i-1):0);
 for(let v of g)A.set(v.i,A.get(v.a>>1)|A.get(v.b>>1));
 ports=ports.filter(i=>A.get(i));if(!ports.length)continue;
 let live=new Set(ports);for(let j=cut-1;j>=0;j--)if(live.has(g[j].i)){live.add(g[j].a>>1);live.add(g[j].b>>1)}
 let G=g.slice(0,cut).filter(v=>live.has(v.i)&&A.get(v.i)),S=ports.reduce((a,i)=>a|A.get(i),0);
 // Only consider cuts covering every data primary, with no direct downstream bypass.
 if(S!==(1<<d)-1||g.slice(cut).some(v=>[v.a>>1,v.b>>1].some(i=>i<=d+q+cut&&A.get(i)&&!ports.includes(i))))continue;
 let Q=new Set,I=0,E=0,out=new Map;for(let v of G)for(let l of [v.a,v.b]){let i=l>>1;if(!A.get(i))Q.add(i);else{if(i<=d)I++;else E++;if(!out.has(i))out.set(i,new Set);out.get(i).add(v.i)}}
 let c=ports.length,cp=ports.filter(i=>i<=d).length,cg=c-cp,occ=2*G.length-I-E;
 let ends=[];for(let i=1;i<=d;i++){let j=i;while(!ports.includes(j)&&out.get(j)?.size===1)j=[...out.get(j)][0];ends.push(j)}
 let H=[],R=new Set,M=new Set;
 for(let y=0;y<1<<q;y++){let row=[],map=[];for(let x=0;x<1<<d;x++){let w=[0];for(let i=0;i<d;i++)w.push(x>>i&1);for(let i=0;i<q;i++)w.push(y>>i&1);let read=l=>w[l>>1]^(l&1);for(let v of g)w[v.i]=read(v.a)&read(v.b);row.push(w[pool[pool.length-1]]);map.push(ports.map(i=>w[i]).join(''))}H.push(row);R.add(row.join(''));M.add(map.join(','));}
 assert(M.size<=2**Q.size,"maps");assert(R.size<=M.size*2**(2**Math.min(c,10))||c>10,"residual");
 let distinct=new Set(ends).size;assert(G.length>=d-c+occ+Math.max(0,distinct-c),"slot");
 for(let i=0;i<d;i++)for(let j=i+1;j<d;j++){let f=new Set;for(let row of H)for(let x=0;x<1<<d;x++)if(!(x>>i&1)&&!(x>>j&1)){let t=row[x]+2*row[x|1<<i]+4*row[x|1<<j]+8*row[x|1<<i|1<<j];if([1,2,4,7,8,11,13,14].includes(t))f.add(Math.min(t,15-t));}if(f.size>1){assert(ends[i]!==ends[j],"endpoint");pairs++}}
 let b=Math.max(0,Math.ceil(Math.log2(R.size))-2**c);assert(Q.size>=b,"ingress");if(b){strict++;maxGap=Math.max(maxGap,b)}cases++;checks+=H.length*(1<<d);
 }
 return {seed:870054,cases,checks,pairs,strict,maxGap}
}
console.log(JSON.stringify(replay(),null,2));

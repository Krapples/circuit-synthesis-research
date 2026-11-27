"use strict";
// Exact switchable SAT pair cofactors and signed-AIG first-branch separation controls.
function replay(){
 const assert=(b,m)=>{if(!b)throw Error(m)};
 let seed=870053;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 // Exact switchable grammar, with independent parser/DPLL.
 function layout(m,l){let P=2**l,t=3*m,Q=1;while(Q<(t+2)*P+t+1)Q*=2;let w=Q.toString(2).length,base=Q+(t+2)*P;return {m,l,P,t,Q,w,base,mode:base+t}}
 function encode(L,h,mode,tag,sg,x){let W=[],pos=[];
  function lit(v,s){assert(v.toString(2).length===L.w,"width");W.push(1,s);for(let j=0;j<L.w;j++)W.push(1,(v>>j)&1);W.push(0,1)}
  function cl(A){for(let [v,s] of A)lit(v,s);W.push(0,0)}
  for(let i=0;i<L.P;i++)cl([[L.Q+i,h[i]]]);
  for(let i=0;i<L.P;i+=2){let a=L.Q+L.P+i;cl([[a,1],[a+1,1]]);cl([[a,0],[a+1,0]])}
  cl([[L.mode,mode]]);
  for(let g=0;g<L.m;g++){let z=L.base+3*g;cl([[z,1],[z+1,1],[z+2,1]]);for(let j=0;j<3;j++){let i=3*g+j;cl([[L.mode,0],[z+j,1]]);lit(z+j,0);pos[i]=Array.from({length:L.l},(_,k)=>W.length+3+2*k);lit(L.Q+tag[i]*L.P+x[i],sg[i]);W.push(0,0)}}
  assert(W.length===(3*L.P+15*L.m+1)*(2*L.w+4)+2*(2*L.P+7*L.m+1),"length");return {W,pos}
 }
 function parse(W){let C=[],a=[],i=0;while(i<W.length){if(!W[i]){assert(W[i+1]===0&&a.length,"clause");C.push(a);a=[];i+=2;continue}let s=W[i+1],v=0,p=1;i+=2;while(W[i]){v+=p*W[i+1];p*=2;i+=2}assert(W[i+1]===1&&v>=p/2,"literal");i+=2;a.push([v,s])}assert(!a.length,"end");return C}
 function sat(C){while(true){if(C.some(a=>!a.length))return false;if(!C.length)return true;let a=C.find(a=>a.length===1);if(!a)break;let [v,s]=a[0];C=C.filter(a=>!a.some(([u,t])=>u===v&&s===t)).map(a=>a.filter(([u])=>u!==v))}
  let [v]=C.reduce((a,b)=>a.length<=b.length?a:b)[0];return [0,1].some(s=>sat([...C,[[v,s]]]))}
 function context(L,a,b,isOr){let i=Math.floor(a/L.l),j=Math.floor(b/L.l),r=a%L.l,s=b%L.l;
  let h=Array.from({length:L.P},(_,p)=>p!==0?1:0),mode=1,tag=Array.from({length:L.t},(_,i)=>i+2),sg=Array(L.t).fill(1);
  if(i===j){tag[i]=0;h=h.map((_,p)=>isOr?((p>>r|p>>s)&1):((p>>r&p>>s)&1))}
  else{tag[i]=tag[j]=0;if(isOr){mode=0;
   if(Math.floor(i/3)===Math.floor(j/3)){let k=3*Math.floor(i/3);while(k===i||k===j)k++;tag[k]=0}
   else{let A=[0,1,2].map(k=>3*Math.floor(i/3)+k).filter(k=>k!==i),B=[0,1,2].map(k=>3*Math.floor(j/3)+k).filter(k=>k!==j);
    // Use a fresh tag equal to t+1, except if that tag is held by an inactive slot:
    // reassign all inactive tags from 3 upward, reserving 2 for shared z.
    tag=Array.from({length:L.t},(_,k)=>k+3); // temporary t+2 last value, replaced below
    let used=new Set([i,j,...A,...B]),n=3;for(let k=0;k<L.t;k++)if(!used.has(k))tag[k]=n++;
    tag[i]=tag[j]=0;tag[A[0]]=tag[B[0]]=2;sg[B[0]]=0;tag[A[1]]=tag[B[1]]=0;
   }
  }}
  assert(tag.every(t=>t>=0&&t<=L.t+1),"namespace");return {h,mode,tag,sg}
 }
 let configs=0,pairs=0,withinSlot=0,withinTriple=0,crossTriple=0,words=0,singleCopy=0,stable=0;
 for(let m of [1,2,3])for(let l of [1,2,3]){let L=layout(m,l),D=L.t*l;configs++;
  for(let a=0;a<D;a++)for(let b=a+1;b<D;b++){
   let i=Math.floor(a/l),j=Math.floor(b/l);if(i===j)withinSlot++;else if(Math.floor(i/3)===Math.floor(j/3))withinTriple++;else crossTriple++;pairs++;
   let refs=null;
   for(let isOr of [false,true]){let {h,mode,tag,sg}=context(L,a,b,isOr),all=[];
    for(let x=0;x<4;x++){let p=Array(L.t).fill(0);p[i]|=(x&1)<<(a%l);p[j]|=(x>>1)<<(b%l);
     let w=encode(L,h,mode,tag,sg,p);assert(sat(parse(w.W))===(isOr?x!==0:x===3),"pair cofactor physical SAT");words++;
     if(refs){assert(JSON.stringify(refs)===JSON.stringify(w.pos),"shared positions");stable++}else refs=w.pos;
     all.push(w)
    }
    let pa=refs[i][a%l],pb=refs[j][b%l];for(let x=0;x<4;x++){assert(all[0].W.every((v,k)=>v===all[x].W[k]||k===pa||k===pb),"only two physical coordinates");assert(all[x].W[pa]===(x&1)&&all[x].W[pb]===(x>>1),"positive orientation");singleCopy++}
   }
  }
 }
 // Generic signed-AIG structural check, with exhaustive pair cofactors.
 function analyze(d,q,g,o){
  const id=l=>l>>1,read=(w,l)=>(w[id(l)]||0)^(l&1);
  let live=new Set([id(o)]);for(let k=g.length-1;k>=0;k--)if(live.has(g[k].i)){live.add(id(g[k].a));live.add(id(g[k].b))}
  g=g.filter(v=>live.has(v.i));let out=new Map;for(let v of g)for(let l of [v.a,v.b]){let i=id(l);if(!out.has(i))out.set(i,new Set);out.get(i).add(v.i)}
  function endpoint(i){while(i!==id(o)){let r=out.get(i);if(!r||!r.size)return -1;if(r.size>1)return i;i=[...r][0]}return i}
  let ep=Array.from({length:d},(_,i)=>endpoint(i+1)),truth=[];
  for(let x=0;x<1<<(d+q);x++){let w=[0];for(let i=0;i<d+q;i++)w.push(x>>i&1);for(let v of g)w[v.i]=read(w,v.a)&read(w,v.b);truth.push(read(w,o))}
  let Q=0,I=0,E=0,B=0,anc=new Map([[0,0]]);for(let i=1;i<=d+q;i++)anc.set(i,i<=d?1<<(i-1):0);
  for(let v of g){let a=anc.get(id(v.a)),b=anc.get(id(v.b)),s=a|b;anc.set(v.i,s);if(s){B++;for(let l of [v.a,v.b]){let i=id(l);if(!anc.get(i))Q++;else if(i<=d)I++;else E++}}}
  let count=0,same=0,both=0,essential=0;
  for(let i=0;i<d;i++)if(truth.some((x,j)=>x!==truth[j^(1<<i)]))essential++;
  for(let i=0;i<d;i++)for(let j=i+1;j<d;j++){
   let and=false,or=false;
   for(let x=0;x<truth.length;x++)if(!(x&(1<<i))&&!(x&(1<<j))){let v=truth[x]|truth[x|1<<i]<<1|truth[x|1<<j]<<2|truth[x|1<<i|1<<j]<<3;and||=v===8;or||=v===14;count++}
   if(and&&or){both++;assert(ep[i]!==ep[j],"AND/OR pair cannot share first branch")}
   if(ep[i]>=0&&ep[i]===ep[j])same++;
  }
  let complete=both===d*(d-1)/2&&essential===d;
  if(complete){assert(I>=d&&E>=B-1&&2*B===I+E+Q,"slot identity");assert(B>=2*d-2+Q,"branch+query bound")}
  return {count,same,both,complete}
 }
 let circuitCases=0,cofactorChecks=0,sameEndpoint=0,bothCofactors=0,completeCases=0;
 function record(r){circuitCases++;cofactorChecks+=r.count;sameEndpoint+=r.same;bothCofactors+=r.both;if(r.complete)completeCases++}
 for(let z=0;z<2400;z++){let d=2+rnd(4),q=rnd(3),n=1+rnd(12),g=[],pool=Array.from({length:d+q},(_,i)=>i+1);
  for(let k=0;k<n;k++){let a=pool[rnd(pool.length)],b=pool[rnd(pool.length)];if(a===b){k--;continue}let i=d+q+k+1;g.push({i,a:2*a+rnd(2),b:2*b+rnd(2)});pool.push(i)}record(analyze(d,q,g,2*pool[pool.length-1]+rnd(2)))
 }
 // Planted programmable AND/OR: query chooses threshold 1 or d.
 // AIG OR via inverted AND. Each data source must branch before merging.
 for(let d=2;d<=6;d++){
  let q=1,g=[],next=d+q+1;
  function and(a,b){let i=next++;g.push({i,a,b});return 2*i}
  function or(a,b){return and(a^1,b^1)^1}
  let A=2,B=2;for(let i=2;i<=d;i++){A=and(A,2*i);B=or(B,2*i)}
  let t=2*(d+1),o=or(and(A,t^1),and(B,t));let r=analyze(d,q,g,o);
  // for d>2, pair AND/OR cofactors come from setting other inputs to 1/0, respectively.
  assert(r.complete,"planted pair property");record(r)
 }
 // Pure majority gives both cofactor types on every pair; tight 4 AIG gates.
 let g=[{i:4,a:2,b:4},{i:5,a:3,b:5},{i:6,a:11,b:6},{i:7,a:9,b:13}];
 // g4=x1&x2; g5=~x1&~x2; g6=(x1 OR x2)&x3; output g4 OR g6.
 let r=analyze(3,0,g,15);assert(r.complete,"majority control");record(r);
 return {seed:870053,configs,pairs,withinSlot,withinTriple,crossTriple,words,singleCopy,stable,circuitCases,cofactorChecks,sameEndpoint,bothCofactors,completeCases}
}
console.log(JSON.stringify(replay(),null,2));

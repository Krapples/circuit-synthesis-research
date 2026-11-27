"use strict";
// Exact three-address table inside fixed-metadata existential incidence.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 let seed=870060;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 function spec(b,m){let A=2**b,P=16*A,l=b+4,t=3*m,Q=1;while(Q<(t+2)*P+t+1)Q*=2;let w=Q.toString(2).length,base=Q+(t+2)*P;return {b,A,P,l,m,t,Q,w,base,mode:base+t,f:4*A}}
 function make(L,random){
  let {A,m,f}=L,groups=Array.from({length:m},(_,i)=>i);if(random)for(let i=m-1;i>0;i--){let j=rnd(i+1);[groups[i],groups[j]]=[groups[j],groups[i]]}
  const pos=v=>2*v,neg=v=>2*v+1,clauses=Array.from({length:m},()=>[pos(f),neg(f),pos(f)]),source=[],target=[];
  let cursor=0;const put=(values,which)=>{let g=groups[cursor++],j=random?rnd(3):0,arr=values.slice();if(which){[arr[0],arr[j]]=[arr[j],arr[0]]}clauses[g]=arr;return 3*g+j};
  put([neg(f),neg(f),neg(f)],false);
  for(let k=0;k<A;k++)put(Array(3).fill(neg(3*A+k)),false);
  for(let a=0;a<3;a++)target.push(put([pos(a*A),pos(f),pos(f)],true));
  for(let a=0;a<A;a++)for(let b=0;b<A;b++)for(let c=0;c<A;c++)source.push(put([neg(2*A+c),neg(a),neg(A+b)],true));
  assert(cursor<=m,"capacity");return {clauses,source,target}
 }
 function data(L,C,h,x){let v=C.clauses.flat();for(let i=0;i<3;i++)v[C.target[i]]+=2*x[i];for(let i=0;i<C.source.length;i++)v[C.source[i]]^=(h[i]?2*L.A:0);return v}
 function evaluate(L,v){ // independent check of logical incidence by DPLL
  return sat(Array.from({length:L.m},(_,i)=>v.slice(3*i,3*i+3).map(x=>[x>>1,1^(x&1)])))
 }
 function sat(C){while(true){if(C.some(c=>!c.length))return false;if(!C.length)return true;let a=C.find(c=>c.length===1);if(!a)break;let [v,s]=a[0];C=C.filter(c=>!c.some(([u,t])=>u===v&&t===s)).map(c=>c.filter(([u])=>u!==v))}
  let [v]=C.reduce((a,b)=>a.length<=b.length?a:b)[0];return [0,1].some(s=>sat([...C,[[v,s]]]))}
 function encode(L,v){let W=[],pos=[];const lit=(u,s)=>{assert(u.toString(2).length===L.w,"width");W.push(1,s);for(let j=0;j<L.w;j++)W.push(1,(u>>j)&1);W.push(0,1)},cl=A=>{for(let [u,s] of A)lit(u,s);W.push(0,0)};
  for(let a=0;a<L.P;a++)cl([[L.Q+a,0]]);
  for(let a=0;a<L.P;a+=2){let u=L.Q+L.P+a;cl([[u,1],[u+1,1]]);cl([[u,0],[u+1,0]])}
  cl([[L.mode,0]]);
  for(let j=0;j<L.m;j++){let z=L.base+3*j;cl([[z,1],[z+1,1],[z+2,1]]);for(let a=0;a<3;a++){let i=3*j+a;cl([[L.mode,0],[z+a,1]]);lit(z+a,0);pos[i]=Array.from({length:L.l},(_,k)=>W.length+3+2*k);lit(L.Q+L.P+v[i],1);W.push(0,0)}}
  assert(W.length===(3*L.P+15*L.m+1)*(2*L.w+4)+2*(2*L.P+7*L.m+1),"word length");return {W,pos}
 }
 function parse(W){let C=[],a=[],i=0;while(i<W.length){if(!W[i]){assert(W[i+1]===0&&a.length,"clause");C.push(a);a=[];i+=2;continue}let s=W[i+1],v=0,p=1;i+=2;while(W[i]){v+=p*W[i+1];p*=2;i+=2}assert(W[i+1]===1&&v>=p/2,"literal");i+=2;a.push([v,s])}assert(!a.length,"end");return C}
 // A deterministic evaluation of the movable-role promise, using only the raw
 // fixed-metadata incidence payload; identify all three target pins then find cell.
 function direct(L,v){let {A,f,m}=L,sel=[-1,-1,-1],cell=[];
  for(let g=0;g<m;g++){let c=v.slice(3*g,3*g+3),p=c.filter(z=>z===2*f);
   if(p.length===2){let a=c.find(z=>z!==2*f);if(a!==undefined&&!(a&1)&&a/2<3*A){let j=Math.floor(a/(2*A));sel[j]=(a/2)%A}}
   if(c.every(z=>z&1)){let a=c.map(z=>z>>1),i=a.find(z=>z<A),j=a.find(z=>z>=A&&z<2*A),k=a.find(z=>z>=2*A&&z<4*A);if(i!==undefined&&j!==undefined&&k!==undefined)cell.push([i,j-A,k%A,Number(k>=3*A)])}
  }
  assert(sel.every(x=>x>=0),"target recognition");let match=cell.filter(c=>c.slice(0,3).every((v,i)=>v===sel[i]));assert(match.length===1,"unique cell");return !!match[0][3]
 }
 let logical=0,physical=0,mutations=0,positions=0,distinct=0,roles=0,yes=0,maxLength=0;
 for(let [b,m,count] of [[1,16,3],[2,128,2]]){
  let L=spec(b,m),A=L.A;
  for(let z=0;z<count;z++){let C=make(L,z!==0),seen=new Set;
   let num=A===2?256:40;
   for(let hidx=0;hidx<num;hidx++){let h=Array.from({length:A**3},(_,i)=>A===2?(hidx>>i&1):rnd(2)),result="";
    for(let a=0;a<A;a++)for(let b=0;b<A;b++)for(let c=0;c<A;c++){let x=[a,b,c],v=data(L,C,h,x),want=!!h[(a*A+b)*A+c],got=evaluate(L,v);assert(got===want&&direct(L,v)===want,"hard incidence lookup");logical++;if(got)yes++;result+=Number(got);
     if(hidx<2&&a===0&&b===0&&c<2){let W=encode(L,v),f=sat(parse(W.W));assert(f===want,"actual paired SAT");physical++;maxLength=Math.max(maxLength,W.W.length);
      for(let i=0;i<h.length;i++){let p=W.pos[C.source[i]][L.b+1];assert(W.W[p]===h[i],"table coordinate");positions++}
      for(let i=0;i<3;i++)for(let j=0;j<L.b;j++){assert(W.W[W.pos[C.target[i]][j+1]]===(x[i]>>j&1),"address coordinate");positions++}
      let k=rnd(h.length),h1=h.slice();h1[k]^=1;let T=encode(L,data(L,C,h1,x));assert(W.W.every((v,i)=>i===W.pos[C.source[k]][L.b+1]?v!==T.W[i]:v===T.W[i]),"single table bit");mutations++;
      let i=rnd(3),j=rnd(L.b),x1=x.slice();x1[i]^=1<<j;T=encode(L,data(L,C,h,x1));assert(W.W.every((v,k)=>k===W.pos[C.target[i]][j+1]?v!==T.W[k]:v===T.W[k]),"single address bit");mutations++;
     }
    }
    if(A===2){assert(!seen.has(result),"distinct complete residual");seen.add(result);distinct++}
   }roles++;
  }
 }
 // Exact gate capacity and union of single-slot side sets for arbitrary supports.
 let capacityChecks=0,unionChecks=0,profiles=[];
 const pc=n=>{let c=0;while(n){n&=n-1;c++}return c};
 for(let z=0;z<400;z++){let m=3+rnd(4),t=3*m;let u=rnd(1<<t),v=rnd(1<<t),a=pc(u^v),count=0;
  for(let i=0;i<t;i++)for(let j=i+1;j<t;j++)for(let k=j+1;k<t;k++)if(Math.floor(i/3)!==Math.floor(j/3)&&Math.floor(j/3)!==Math.floor(k/3)){let T=(1<<i)|(1<<j)|(1<<k),p=!!(u&T),q=!!(v&T);if(p!==q){count++;assert(!!((u^v)&T),"pair membership");unionChecks++}}
  assert(count<=a*9*(m-1)*(m-2)/2,"triple capacity");capacityChecks++;
 }
 for(let k of [18,24,30,60]){let m=2**k,l=Math.floor(k/3),A=2**(l-4),H=A**3;profiles.push({k,l,m,A,H,sourceFraction:H/m,asymMass:m*H})}
 return {seed:870060,logical,physical,mutations,positions,distinct,roles,yes,maxLength,capacityChecks,unionChecks,profiles}
}
console.log(JSON.stringify(replay(),null,2));

"use strict";
// Fixed-layout affine embedding retaining protected selector and hard incidence modes.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};let seed=870066;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return(seed>>>8)%n};
 const parity=x=>{let p=0;while(x){p^=1;x&=x-1}return p};
 function spec(m,l){let t=3*m,P=1<<l,Q=1;while(Q<(t+2)*P+t+1)Q*=2;return {m,l,t,P,Q,w:Math.log2(Q)+1,base:Q+(t+2)*P}}
 function encode(L,x,s,lambda,mode){let W=[],pos=[],sp=[],hp=[],mp=-1;const lit=(v,z)=>{assert(v.toString(2).length===L.w,"width");W.push(1,z);for(let j=0;j<L.w;j++)W.push(1,(v>>j)&1);W.push(0,1)},cl=A=>{for(let [v,z] of A)lit(v,z);W.push(0,0)};
  for(let a=0;a<L.P;a++){hp.push(W.length+1);cl([[L.Q+a,parity(lambda&a)]])}
  for(let a=0;a<L.P;a+=2){let v=L.Q+L.P+a;cl([[v,1],[v+1,1]]);cl([[v,0],[v+1,0]])}
  let p=L.base+L.t;mp=W.length+1;cl([[p,mode]]);
  for(let g=0;g<L.m;g++){let z=L.base+3*g;cl([[z,1],[z+1,1],[z+2,1]]);for(let j=0;j<3;j++){let i=3*g+j;cl([[p,0],[z+j,1]]);lit(z+j,0);let tag=(mode^1)^((s[i]^1)*(i+2));assert(tag>=0&&tag<=L.t+1,"legal tag");pos[i]=Array.from({length:L.l},(_,j)=>W.length+3+2*j);sp[i]=W.length+3+2*(L.l+1);lit(L.Q+tag*L.P+x[i],1);W.push(0,0)}}
  assert(W.length===(3*L.P+15*L.m+1)*(2*L.w+4)+2*(2*L.P+7*L.m+1),"length");return {W,pos,sp,hp,mp}
 }
 function parse(W){let C=[],a=[],i=0;while(i<W.length){if(!W[i]){assert(W[i+1]===0&&a.length,"clause");C.push(a);a=[];i+=2;continue}let s=W[i+1],v=0,p=1;i+=2;while(W[i]){v+=p*W[i+1];p*=2;i+=2}assert(W[i+1]===1&&v>=p/2,"literal");i+=2;a.push([v,s])}assert(!a.length,"end");return C}
 function sat(C){while(true){if(C.some(a=>!a.length))return false;if(!C.length)return true;let a=C.find(a=>a.length===1);if(!a)break;let [v,s]=a[0];C=C.filter(a=>!a.some(([u,t])=>u===v&&s===t)).map(a=>a.filter(([u])=>u!==v))}
 let [v]=C.reduce((a,b)=>a.length<=b.length?a:b)[0];return [0,1].some(s=>sat([...C,[[v,s]]]))}
 function hard(L,x){return Array.from({length:1<<(L.P/2)},(_,a)=>a).some(a=>Array.from({length:L.m},(_,g)=>[0,1,2].some(j=>((a>>(x[3*g+j]>>1)&1)^(x[3*g+j]&1))===1)).every(Boolean))}
 let words=0,unit=0,hardChecks=0,affine=0,coords=0,mutation=0,profiles=[];
 for(let [m,l] of [[2,1],[4,2],[8,3]]){let L=spec(m,l),N=L.t*l+L.t+l+1;
  const decode=v=>{let x=[],s=[],j=0;for(let i=0;i<L.t;i++){let a=0;for(let k=0;k<l;k++)a|=v[j++]<<k;x.push(a)}for(let i=0;i<L.t;i++)s.push(v[j++]);let h=0;for(let k=0;k<l;k++)h|=v[j++]<<k;return [x,s,h,v[j]]};
  let zero=Array(N).fill(0),Z=encode(L,...decode(zero)),basis=[];for(let j=0;j<N;j++){let v=zero.slice();v[j]=1;let E=encode(L,...decode(v));basis.push(E.W.map((x,k)=>x^Z.W[k]));if(j<L.t*l){assert(basis[j].reduce((a,b)=>a+b,0)===1&&basis[j][Z.pos[Math.floor(j/l)][j%l]]===1,"single physical payload");mutation++}}
  for(let z=0;z<70;z++){let v=Array.from({length:N},()=>rnd(2)),E=encode(L,...decode(v)),pred=Z.W.slice();for(let j=0;j<N;j++)if(v[j])for(let k=0;k<pred.length;k++)pred[k]^=basis[j][k];assert(E.W.every((x,k)=>x===pred[k]),"affine word");affine++;
   let [x,s,h,p]=decode(v);assert(E.W[E.mp]===p,"mode recovery");coords++;for(let j=0;j<l;j++){assert(E.W[E.hp[1<<j]]===(h>>j&1),"lambda recovery");coords++}for(let i=0;i<L.t;i++){assert(E.W[E.sp[i]]===(s[i]^1)*((i+2)>>1&1)||((i+2)>>1&1)===0,"tag recovery bit control");for(let k=0;k<l;k++){assert(E.W[E.pos[i][k]]===(x[i]>>k&1),"payload recovery");coords++}}
   // Actual selector control uses any nonzero high tag bit, not necessarily bit 1.
   for(let i=0;i<L.t;i++){let b=1;while(!((i+2)>>b&1))b++;let c=E.sp[i]+2*(b-1);assert(E.W[c]===(s[i]^1),"selector recovery");coords++}
  }
  for(let z=0;z<45;z++){let x=Array.from({length:L.t},()=>rnd(L.P)),s=Array.from({length:L.t},()=>rnd(2)),h=rnd(L.P),p=1;let E=encode(L,x,s,h,p);assert(sat(parse(E.W))===s.every((b,i)=>!b||parity(h&x[i])),"unit selector");words++;unit++;
   s.fill(1);p=0;E=encode(L,x,s,h,p);assert(sat(parse(E.W))===hard(L,x),"hard incidence");words++;hardChecks++;
   if(z<4){s=Array.from({length:L.t},()=>rnd(2));E=encode(L,x,s,h,0);parse(E.W);words++}
  }
  profiles.push({m,l,N,length:Z.W.length,affineXorBudget:L.t/2+L.P-l-1});
 }
 return {seed:870066,words,unit,hardChecks,affine,coords,mutation,profiles}
}
console.log(JSON.stringify(replay(),null,2));

// Nonlinear response period certificates. Node.js.
function run(){
 let seed=870027;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(x,m="assertion"){if(!x)throw Error(m);}
 function pop(x){let n=0;while(x){x&=x-1n;n++;}return n;}
 function toggle(S,v){if(S.has(v))S.delete(v);else S.add(v);}
 function xor(A,B){let S=new Set(A);for(let v of B)toggle(S,v);return S;}
 function mul(A,B){let S=new Set();for(let a of A)for(let b of B)toggle(S,a|b);return S;}
 function lin(I){return new Set(I.map(i=>1n<<BigInt(i)));}
 function evalP(P,x){let v=0;for(let a of P)if((a&x)===a)v^=1;return v;}
 function derivative(P,d){let S=new Set();for(let a of P){let t=a&d;for(let b=t;b;b=(b-1n)&t)toggle(S,a^b);}return S;}
 function sig(F,d,k,n){let S=new Set();for(let i=0;i<F.length;i++)for(let a of derivative(F[i],d))if(pop(a)===k)S.add((BigInt(i)<<BigInt(n))|a);return S;}
 function pivot(S){let p=-1n;for(let a of S)if(a>p)p=a;return p;}
 function periods(F,n){
  let D=0;for(let P of F)for(let a of P)D=Math.max(D,pop(a));
  let V=Array.from({length:n},(_,i)=>1n<<BigInt(i)),profile=[n],calls=0;
  for(let k=D-1;k>=0;k--){
   let B=new Map(),W=[];
   for(let d of V){let z=sig(F,d,k,n);calls++;
    while(z.size){let p=pivot(z);if(!B.has(p)){B.set(p,[z,d]);break;}let [s,e]=B.get(p);z=xor(z,s);d^=e;}
    if(!z.size)W.push(d);
   }V=W;profile.push(V.length);
  }
  for(let d of V)for(let P of F)ok(!derivative(P,d).size,"period basis");
  return {basis:V,rank:n-V.length,profile,calls};
 }
 function rankSets(F){let B=new Map();for(let a of F){let z=new Set(a);z.delete(0n);while(z.size){let p=pivot(z);if(!B.has(p)){B.set(p,z);break;}z=xor(z,B.get(p));}}return B.size;}
 function span(V){let S=[0n];for(let d of V)S.push(...S.map(x=>x^d));return S;}
 function randomPoly(n,D){let P=new Set(),t=1+rnd(12);for(let j=0;j<t;j++){let a=0n,k=rnd(D+1);for(let i=0;i<k;i++)a|=1n<<BigInt(rnd(n));toggle(P,a);}return P;}
 let S={randomMaps:0,plantedMaps:0,periodBasisChecks:0,bruteRows:0,translationChecks:0,filtrationChecks:0,examples:[],witness:[],limitations:[]};
 for(let t=0;t<160;t++){
  let n=2+rnd(6),D=1+rnd(4),r=1+rnd(5),F=Array.from({length:r},()=>randomPoly(n,D));
  if(t%2===0){let d=1+rnd(n-1),L=Array.from({length:d},()=>lin(Array.from({length:n},(_,i)=>i).filter(()=>rnd(2))));
   F=Array.from({length:r},()=>{let z=new Set();for(let a of randomPoly(d,D)){let P=new Set([0n]);for(let i=0;i<d;i++)if(a>>BigInt(i)&1n)P=mul(P,L[i]);z=xor(z,P);}return z;});S.plantedMaps++;
  }else S.randomMaps++;
  let A=periods(F,n),W=span(A.basis),R=Array.from({length:2**n},(_,i)=>F.map(P=>evalP(P,BigInt(i))).join("")),B=[];
  for(let d=0;d<R.length;d++){let good=true;for(let x=0;x<R.length;x++){S.translationChecks++;if(R[x]!==R[x^d]){good=false;break;}}if(good)B.push(BigInt(d));}
  ok(W.length===B.length&&W.every(x=>B.includes(x)),"exact period space");ok(new Set(R).size<=2**A.rank,"image");
  S.periodBasisChecks+=A.basis.length;S.bruteRows+=R.length;
  let V=Array.from({length:2**n},(_,i)=>BigInt(i)),D0=0;for(let P of F)for(let a of P)D0=Math.max(D0,pop(a));
  for(let k=D0-1;k>=0;k--){for(let j=0;j<8;j++){let a=V[rnd(V.length)],b=V[rnd(V.length)];ok(!xor(xor(sig(F,a,k,n),sig(F,b,k,n)),sig(F,a^b,k,n)).size,"linear filtration");S.filtrationChecks++;}V=V.filter(d=>!sig(F,d,k,n).size);}
  ok(V.length===W.length&&V.every(x=>W.includes(x)),"nested kernels");
 }
 function candidate(k){
  let M=2**k,d=M*M+2*M,n=d+k,E=[];
  function AND(a,b){let v=2*(n+E.length);E.push([a,b]);return v;}
  function OR(a,b){return AND(a^1,b^1)^1;}
  function mux(q,a,b){return OR(AND(q,b),AND(q^1,a));}
  let rows=[];
  for(let j=0;j<M;j++){let V=Array.from({length:M},(_,i)=>2*(j*M+(i^j)));for(let t=0;t<k;t++)V=V.map((v,i)=>mux(2*(d+t),v,V[i^(1<<t)]));rows.push(V);}
  let w=Array.from({length:M},(_,i)=>2*(M*M+M+i));for(let t=0;t<k;t++)w=w.map((v,i)=>mux(2*(d+t),v,w[i^(1<<t)]));
  let out=[],paths=[];
  for(let i=0;i<M;i++){let m=AND(2*(M*M+i),w[i]),p=rows[i][i],path=[p>>1];
   function step(q){let a=AND(p,q^1),b=AND(p^1,q);p=OR(a,b);path.push(a>>1,p>>1);}
   step(m);for(let j=0;j<M;j++)if(j!==i)step(rows[j][i]);out.push(p);paths.push(path);
  }
  let P=Array.from({length:M},(_,t)=>lin(Array.from({length:M},(_,j)=>j*M+(t^j)))),F=[];
  let nodes=Array.from({length:d},()=>null),H=new Map(),AH=new Map();
  let A=Array.from({length:M},(_,q)=>Array.from({length:n},(_,i)=>i<d?2*i:-2+((q>>(i-d))&1)));
  let forms=Array.from({length:M},(_,q)=>Array.from({length:n},(_,i)=>i<d?new Set([1n<<BigInt(i)]):new Set((q>>(i-d))&1?[0n]:[])));
  function key(S){return [...S].sort((a,b)=>a<b?-1:a>b?1:0).join(",");}
  function get(h,l){let z=forms[h][l>>1];return l&1?xor(z,new Set([0n])):z;}
  function lit(h,l){return A[h][l>>1]^(l&1);}
  AH.set("",-2);AH.set("0",-1);
  for(let i=0;i<d;i++){let x=1n<<BigInt(i);AH.set(key(new Set([x])),2*i);AH.set(key(new Set([x,0n])),2*i+1);}
  for(let j=0;j<E.length;j++)for(let h=0;h<M;h++){
   let [a,b]=E[j],x=lit(h,a),y=lit(h,b),z=mul(get(h,a),get(h,b)),r;
   let affine=[...z].every(a=>pop(a)<=1),s=key(z);
   if(affine&&AH.has(s))r=AH.get(s);
   else if(x===-2||y===-2||x===(y^1))r=-2;
   else if(x===-1||x===y)r=y;else if(y===-1)r=x;
   else{if(x>y)[x,y]=[y,x];let h=x+","+y;if(!H.has(h)){H.set(h,2*nodes.length);nodes.push([x,y]);}r=H.get(h);}
   if(affine){if(AH.has(s))ok(AH.get(s)===r,"affine alias");AH.set(s,r);AH.set(key(xor(z,new Set([0n]))),r^1);}
   A[h].push(r);forms[h].push(z);
  }
  let used=new Set(),pathNodes=0,evalChecks=0;
  for(let h=0;h<M;h++)for(let i=0;i<M;i++){
   let t=h^i,z=1n<<BigInt(M*M+i),w=1n<<BigInt(M*M+M+t),want=xor(P[t],new Set([z|w])),got=get(h,out[i]);
   ok(!xor(want,got).size,"ANF");F.push(got);
   let path=paths[i].map(v=>A[h][v]>>1);
   ok(path[0]===i*M+h&&path[path.length-1]===(lit(h,out[i])>>1),"endpoints");
   for(let j=0;j<path.length;j++){let v=path[j];ok(!used.has(v),"disjoint path");used.add(v);pathNodes++;if(j)ok(nodes[v].some(l=>(l>>1)===path[j-1]),"edge");}
   for(let j=1;j<paths[i].length;j++)ok([...forms[h][paths[i][j]]].some(a=>(a&z)&&(a&w)),"private marker");
  }
  for(let i=M*M;i<d;i++){ok(!used.has(i),"raw ports");used.add(i);F.push(new Set([1n<<BigInt(i)]));}
  let R=periods(F,d),r=rankSets(F);ok(R.rank===3*M&&r===d,"separation");
  for(let t=0;t<32;t++){let q=rnd(M),x=0n;for(let i=0;i<d;i++)if(rnd(2))x|=1n<<BigInt(i);
   let V=Array.from({length:n},(_,i)=>i<d?Number(x>>BigInt(i)&1n):(q>>(i-d))&1);
   for(let [a,b] of E)V.push((V[a>>1]^(a&1))&(V[b>>1]^(b&1)));
   for(let i=0;i<M;i++){ok((V[out[i]>>1]^(out[i]&1))===evalP(F[q*M+i],x),"AIG");evalChecks++;}
  }
  return {M,data:d,gates:E.length,fullQuotientFlow:d,polynomialSpanRank:r,periodCodimension:R.rank,filtration:R.profile,pathNodes,evalChecks,derivativeBasisCalls:R.calls};
 }
 for(let k=1;k<=3;k++)S.examples.push(candidate(k));
 for(let [m,l] of [[2,2],[3,2],[2,4]]){let d=m*l,F=[];
  for(let s=0;s<2**m;s++)for(let q=0;q<2**l;q++){
   let P=new Set([0n]);for(let t=0;t<l;t++)if(q>>t&1){let a=0n;for(let i=0;i<m;i++)if(s>>i&1)a|=1n<<BigInt(i*l+t);P=mul(P,xor(new Set([0n]),new Set([a])));}
   F.push(xor(P,new Set([0n])));
  }
  let R=periods(F,d);ok(R.rank===d,"witness period");S.witness.push({m,l,d,queries:F.length,periodCodimension:R.rank,polynomialSpan:rankSets(F)});
 }
 for(let n=2;n<=6;n++){let F=[new Set(Array.from({length:2**n-1},(_,i)=>BigInt(i+1)))];let R=periods(F,n);ok(R.rank===n,"OR");S.limitations.push({n,periodCodimension:R.rank,logImage:1});}
 return S;
}
if(typeof module!=="undefined"&&require.main===module)console.log(JSON.stringify(run(),null,2)+"\nall assertions passed");

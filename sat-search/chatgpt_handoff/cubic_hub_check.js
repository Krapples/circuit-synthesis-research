// Common coordinate kernel for hub-conditioned maps and Walsh table queries.
// Run: node cubic_hub_check.js
function run(){
  let seed=870014;
  function draw(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
  function ok(x,m="assertion failed"){if(!x)throw Error(m);}
  function parity(x){let p=0;while(x){p^=1;x&=x-1;}return p;}
  function wt(x){let p=0;while(x){p++;x&=x-1;}return p;}
  function insert(B,v){for(let j=B.length-1;j>=0;j--)if(v&(1<<j)){if(B[j])v^=B[j];else{B[j]=v;return true;}}return false;}
  function reduce(B,v){for(let j=B.length-1;j>=0;j--)if(v&(1<<j)){if(B[j])v^=B[j];else break;}return v;}
  function canonical(T){let D=new Map();for(let [a,c] of T){a=[...new Set(a)].sort((a,b)=>a-b);let key=a.join(",");D.set(key,[a,(D.get(key)?.[1]||0)^c]);}return [...D.values()].filter(x=>x[1]);}
  function graph(q,T){let G=Array.from({length:q},()=>new Set());for(let [a] of T)for(let i of a)for(let j of a)if(i!==j)G[i].add(j);return G;}
  function kernel(q,k,T){
    const G=graph(q,T),alive=Array(q).fill(true);let centers=0;
    for(let r=0;r<8*k;r++){
      let B=Array(k).fill(0);
      while(true){
        let hit=T.find(([a,c])=>a.some(i=>alive[i])&&reduce(B,c));if(!hit)break;
        let [a,c]=hit,v=a.find(i=>alive[i]);ok(insert(B,c));centers++;
        let S=new Set([v]);for(let i=0;i<3;i++){let N=new Set(S);for(let j of S)for(let w of G[j])N.add(w);S=N;}
        for(let j of S)alive[j]=false;
      }
    }
    let V=Array(k).fill(0);for(let [a,c] of T)if(a.some(i=>alive[i]))insert(V,c);
    const keep=alive.map(a=>!a),degree=Math.max(0,...G.map(x=>x.size));
    ok(centers<=8*k*k&&keep.filter(Boolean).length<=centers*(1+degree+degree**2+degree**3));
    return {keep,V,degree};
  }
  function split(s,k,T){
    let keys=Array.from({length:1<<s},(_,i)=>i).filter(i=>wt(i)<=2),J=[],C=[];
    for(let [a,c] of T){
      let h=0,y=[];for(let i of a)if(i<s)h|=1<<i;else y.push(i-s);
      if(y.length){ok(keys.includes(h));J.push([y,c<<(k*keys.indexOf(h))]);}else C.push([h,c]);
    }return {J:canonical(J),C,keys};
  }
  function branch(k,u,S){
    let T=[],b=0;for(let [h,c] of S.C)if((h&u)===h)b^=c;
    T.push([[],b]);
    for(let [a,c] of S.J){let v=0;for(let j=0;j<S.keys.length;j++)if((S.keys[j]&u)===S.keys[j])v^=(c>>>(k*j))&((1<<k)-1);if(v)T.push([a,v]);}
    return canonical(T);
  }
  function restrict(T,keep){return T.filter(([a])=>a.every(i=>keep[i]));}
  function brute(q,T,keep){
    let mask=keep.reduce((m,v,i)=>v?m|(1<<i):m,0),S=new Set();
    let terms=T.map(([a,c])=>[a.reduce((m,i)=>m|(1<<i),0),c]);
    for(let x=0;x<1<<q;x++)if((x&mask)===x){let v=0;for(let [a,c] of terms)if((x&a)===a)v^=c;S.add(v);}return S;
  }
  function path(q,k,T,keep){
    let M=1<<k,groups=Array.from({length:q},()=>[]),b=0;
    for(let [a,c] of T){if(!a.length){b^=c;continue;}let j=a.at(-1);ok(j-a[0]<=2);groups[j].push([a.reduce((m,i)=>m|(1<<(j-i)),0),c]);}
    let H=new Uint8Array(4*M);H[b]=1;
    for(let j=0;j<q;j++){let N=new Uint8Array(4*M);for(let s=0;s<4;s++)for(let u=0;u<=(keep[j]?1:0);u++){
      let w=(s<<1)|u,v=0;for(let [m,c] of groups[j])if((w&m)===m)v^=c;
      for(let a=0;a<M;a++)if(H[s*M+a])N[(w&3)*M+(a^v)]=1;
    }H=N;}
    return new Set(Array.from({length:M},(_,a)=>H[a]||H[M+a]||H[2*M+a]||H[3*M+a]?a:-1).filter(x=>x>=0));
  }
  function dualBasis(k,V){
    let B=Array(k).fill(0),out=[];for(let l=1;l<1<<k;l++)if(V.every(v=>!parity(l&v))&&insert(B,l))out.push(l);return out;
  }
  function project(a,B){return B.reduce((v,l,i)=>v|(parity(a&l)<<i),0);}
  function transpose(l,B){return B.reduce((v,b,i)=>l>>i&1?v^b:v,0);}
  function fwht(a){for(let d=1;d<a.length;d*=2)for(let i=0;i<a.length;i+=2*d)for(let j=i;j<i+d;j++){let x=a[j],y=a[j+d];a[j]=x+y;a[j+d]=x-y;}return a;}
  function same(A,B){return A.size===B.size&&[...A].every(x=>B.has(x));}
  let stats={maps:0,hub_branches:0,joint_image_checks:0,branch_image_checks:0,marginal_lift_checks:0,walsh_table_queries:0,
    long_maps:0,detected_hub_sets:0,strict_joint_reductions:0,max_original_variables:0,max_retained:0,max_discard:0,largest_reduction:null};
  function check(s,q,k,T,long){
    T=canonical(T);let S=split(s,k,T),dim=k*S.keys.length;ok(dim<31);
    let K=kernel(q,dim,S.J),all=Array(q).fill(true),r=K.keep.filter(Boolean).length;
    if(!long){ok(same(brute(q,S.J,all),brute(q,S.J,K.keep)));stats.joint_image_checks++;}
    else {
      let G=graph(s+q,T),detected=G.map((a,i)=>a.size>4?i:-1).filter(i=>i>=0);
      // Threshold counts only original hubs after allowing up to s added neighbors at leaves.
      detected=G.map((a,i)=>a.size>4+s?i:-1).filter(i=>i>=0);
      ok(detected.length===s&&detected.every((x,i)=>x===i));stats.detected_hub_sets++;
      ok(K.degree<=4);
    }
    for(let u=0;u<1<<s;u++){
      let B=branch(k,u,S),C=restrict(B,K.keep);
      let im=long?path(q,k,B,all):brute(q,B,all);
      let ci=long?path(q,k,C,K.keep):brute(q,C,K.keep);
      ok(same(im,ci),"joint kernel lost branch image");stats.branch_image_checks++;
      let L=kernel(q,k,C),R=restrict(C,L.keep),ri=long?path(q,k,R,L.keep):brute(q,R,L.keep);
      ok(same(ci,ri));let dual=dualBasis(k,L.V),t=dual.length;
      let g=new Set([...ri].map(a=>project(a,dual)));
      for(let a=0;a<1<<k;a++){ok(im.has(a)===g.has(project(a,dual)));stats.marginal_lift_checks++;}
      // Padded projection rows model a circuit with variable marginal dimension.
      for(let z=0;z<3;z++){
        let H=Array.from({length:1<<k},()=>z===0?0:z===1?1:draw(2));
        let direct=H.reduce((v,b,a)=>v+(im.has(a)?b:0),0),W=fwht(H.slice());
        let padded=[...dual,...Array(k-t).fill(0)],ghat=fwht(Array.from({length:1<<k},(_,a)=>g.has(a)?1:0));
        let num=ghat.reduce((v,b,l)=>v+b*W[transpose(l,padded)],0);
        ok(num===direct*(1<<k),"Walsh query mismatch");stats.walsh_table_queries++;
      }stats.hub_branches++;
    }
    stats.maps++;stats.long_maps+=long;stats.strict_joint_reductions+=r<q;
    stats.max_original_variables=Math.max(stats.max_original_variables,q+s);stats.max_retained=Math.max(stats.max_retained,r+s);
    if(q-r>stats.max_discard){stats.max_discard=q-r;stats.largest_reduction={hubs:s,address_bits:k,original:q+s,retained:r+s};}
  }
  for(let s=0;s<=2;s++)for(let k=1;k<=3;k++)for(let trial=0;trial<12;trial++){
    let q=1+draw(9),T=[];for(let j=0;j<3*(s+q);j++)T.push([Array.from({length:draw(4)},()=>draw(s+q)),draw(1<<k)]);
    check(s,q,k,T,false);
  }
  for(let s=1;s<=2;s++)for(let k=1;k<=2;k++){
    let q=s===1?1600:3000,T=[];
    for(let i=0;i<q-2;i++){
      T.push([[s+i,s+i+1,s+i+2],1<<(i%k)]);
      for(let j=0;j<s;j++)T.push([[j,s+i,s+i+1],1<<((i+j)%k)]);
    }
    T.push([[0],1]);check(s,q,k,T,true);
  }
  return stats;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

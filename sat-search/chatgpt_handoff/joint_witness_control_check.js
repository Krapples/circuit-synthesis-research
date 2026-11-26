// Joint-witness consistency + packed Andreev negative control.
// Run: node joint_witness_control_check.js
function run(){
  let seed=870015;
  function draw(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
  function ok(x,m="assertion failed"){if(!x)throw Error(m);}
  function parity(x){let p=0;while(x){p^=1;x&=x-1;}return p;}
  function params(k){let M=2**k,ell=2**Math.floor(Math.log2(Math.max(1,Math.floor(k/2)))),J=Math.floor(M/(k*ell)),P=2**ell,B=M/ell,m=k*J,A=k*(2*J-1)+2*B-1;return {M,ell,J,P,B,m,A,r:Math.max(3,m)};}
  function pattern(a){return a.reduce((v,x,i)=>v+x*2**i,0);}
  function enc(C){let w=[];for(let l of C){w.push(1,+(l>0));let v=Math.abs(l)-1;while(v){w.push(1,v%2);v=Math.floor(v/2);}w.push(0,1);}w.push(0,0);return w;}
  function parse(w){
    let F=[],C=[],i=0;ok(w.length%2===0);
    while(i<w.length){let a=w[i++],b=w[i++];if(a===0&&b===0){F.push(C);C=[];continue;}ok(a===1);
      let v=0,p=1,last=1;while(i<w.length){let c=w[i++],d=w[i++];if(!c){ok(d===1&&last===1);break;}v+=p*d;p*=2;last=d;}C.push((b?1:-1)*(v+1));
    }ok(!C.length);return F;
  }
  function balance(w){return [...w,1,0,0,1,1,1,0,1,1,0,...w.slice(0,-2).flatMap(v=>[1,1-v]),1,1,0,1,0,0];}
  function decide(F,pins){
    let C=F.map(a=>[...new Set(a)]).filter(a=>!a.some(l=>a.includes(-l))),val=new Set(),queue=[...pins,...C.filter(a=>a.length===1).map(a=>a[0])];
    if(C.some(a=>!a.length))return false;
    for(let i=0;i<queue.length;i++){let l=queue[i];if(val.has(-l))return false;if(val.has(l))continue;val.add(l);
      let next=[];for(let a of C){if(a.includes(l))continue;if(a.includes(-l)){a=a.filter(v=>v!==-l);if(!a.length)return false;if(a.length===1)queue.push(a[0]);}next.push(a);}C=next;
    }ok(!C.length,"unexpected unresolved clauses");return true;
  }
  function make(k,h,x,order,c){
    const {M,ell,J,P,B,m,A,r}=params(k);ok(c.length===r-1&&x.length===m*ell);
    // Old A auxiliaries, selected output a, r-1 charge bits, and 5 edge variables per edge.
    let cap=A+1+(r-1)+5*r,Q=2**Math.ceil(Math.log2(Math.max(4*P,cap))),nxt=Q+1,F=[];
    const fresh=()=>nxt++,U=p=>P+p+1,V=p=>2*P+p+1;
    const emit=(...C)=>F.push(...C);
    function xor(a,b,z){for(let i=0;i<2;i++)for(let j=0;j<2;j++){let v=[i,j,1^i^j];emit([a,b,z].map((l,t)=>v[t]?-l:l));}}
    function and(a,b,z){emit([-z,a],[-z,b],[z,-a,-b]);}
    for(let p=0;p<P;p++)emit([parity(p)?U(p):-U(p)]);
    let zs=Array.from({length:m},fresh);
    for(let i=0;i<m;i++){let z=zs[order[i]],p=pattern(x.slice(i*ell,(i+1)*ell));emit([-z,U(p)],[z,-U(p)]);}
    let addr=[];
    for(let i=0;i<k;i++){let a=zs[i*J];for(let j=1;j<J;j++){let z=fresh();xor(a,zs[i*J+j],z);a=z;}addr.push(a);}
    let lo=Math.log2(ell);
    for(let p=0;p<P;p++)for(let t=0;t<ell;t++)
      emit([...addr.slice(0,lo).map((a,i)=>t>>i&1?-a:a),p>>t&1?V(p):-V(p)]);
    let root=fresh();emit([root]);let guards=[root];
    for(let a of addr.slice(lo).reverse()){let children=[];for(let g of guards)for(let b of [-a,a]){let z=fresh();and(g,b,z);children.push(z);}guards=children;}
    ok(nxt===Q+A+1&&guards.length===B);
    const a=fresh();
    for(let i=0;i<B;i++){let p=pattern(h.slice(i*ell,(i+1)*ell));emit([-guards[i],-a,V(p)],[-guards[i],a,-V(p)]);}
    const charge=[a,...c.map(b=>{let z=fresh();emit([b?z:-z]);return z;})];
    const edges=Array.from({length:r},()=>{let x=fresh(),y=fresh(),z=fresh(),p=fresh(),w=fresh();and(y,z,p);xor(x,p,w);return {x,y,z,w};});
    for(let v=0;v<r;v++)xor(edges[(v+r-1)%r].w,edges[v].w,charge[v]);
    ok(nxt===Q+cap+1&&nxt-2<2*Q);
    const w=F.flatMap(enc);ok(JSON.stringify(F)===JSON.stringify(parse(w)));
    return {w,edges};
  }
  function addr(k,x,order){let {ell,J,m}=params(k),a=0;for(let i=0;i<m;i++)if(x.slice(i*ell,(i+1)*ell).reduce((s,b)=>s^b,0))a^=1<<Math.floor(order[i]/J);return a;}
  function pins(edges,e,mode){return edges.flatMap((v,i)=>{let y=mode?draw(2):0,z=mode?draw(2):0,x=e[i]^(y&z);return [x?v.x:-v.x,y?v.y:-v.y,z?v.z:-v.z];});}
  function solveCycle(b){let e=Array(b.length).fill(0);for(let i=1;i<b.length;i++)e[i]=e[i-1]^b[i];return e;}
  function diffs(a,b){ok(a.length===b.length);return a.map((v,i)=>v!==b[i]?i:-1).filter(i=>i>=0);}
  let stats={packed_cases:0,pinned_original:0,pinned_padded:0,pinned_balanced:0,charge_flips:0,coordinate_checks:0,
    full_marginal_checks:0,proper_marginal_checks:0,nonlinear_histograms:0,edge_assignments:0,max_word:0,max_vertices:0};
  // Every proper projection of the residual vector has the same exact histogram.
  for(let r=3;r<=9;r++){
    let M=1<<r,A=Array(M).fill(0n),B=Array(M).fill(0n);
    for(let e=0;e<M;e++){let a=0;for(let i=0;i<r;i++)if(((e>>i)^(e>>((i+r-1)%r)))&1)a|=1<<i;
      A[a]+=1n<<BigInt(2*r);B[a^1]+=1n<<BigInt(2*r);stats.edge_assignments++;}
    for(let a=0;a<M;a++){ok(A[a]===(parity(a)?0n:1n<<BigInt(2*r+1)));ok(B[a]===A[a^1]);stats.full_marginal_checks++;}
    if(r<=5){let D=Array(M).fill(0n);for(let w=0;w<1<<(3*r);w++){let e=0;for(let i=0;i<r;i++){let z=w>>(3*i)&7;e|=((z&1)^((z>>1&1)&(z>>2&1)))<<i;}let a=0;for(let i=0;i<r;i++)if(((e>>i)^(e>>((i+r-1)%r)))&1)a|=1<<i;D[a]++;}
      ok(D.every((x,i)=>x===A[i]));stats.nonlinear_histograms++;}
    for(let S=0;S<M-1;S++){let HA=Array(M).fill(0n),HB=Array(M).fill(0n);
      for(let a=0;a<M;a++){HA[a&S]+=A[a];HB[a&S]+=B[a];}
      for(let a=0;a<M;a++)if((a&S)===a){ok(HA[a]===HB[a]&&HA[a]===(1n<<BigInt(3*r-S.toString(2).replace(/0/g,"").length)));stats.proper_marginal_checks++;}
    }
  }
  for(let k=1;k<=8;k++)for(let t=0;t<6;t++){
    let {M,ell,J,m,r}=params(k),h=Array.from({length:M},()=>draw(2)),x=Array.from({length:m*ell},()=>draw(2)),order=Array.from({length:m},(_,i)=>i);
    for(let i=m-1;i>0;i--){let j=draw(i+1);[order[i],order[j]]=[order[j],order[i]];}
    let a=h[addr(k,x,order)],c=Array.from({length:r-1},()=>draw(2));c[0]^=a^c.reduce((s,v)=>s^v,0);
    let c2=c.slice();c2[0]^=1;let P=make(k,h,x,order,c),N=make(k,h,x,order,c2);
    ok(diffs(P.w,N.w).length===1);stats.charge_flips++;
    let e=solveCycle([a,...c]);
    for(let [W,want] of [[P,true],[N,false]]){let pin=pins(W.edges,e,true),pad=[...W.w,...enc([1,-1]),...enc([2,-2]),...enc([1,-1]),...enc([2,-2])];
      ok(decide(parse(W.w),pin)===want);stats.pinned_original++;
      ok(decide(parse(pad),pin)===want);stats.pinned_padded++;
      let bw=balance(pad);ok(bw.length===3*pad.length+12&&bw.reduce((s,v)=>s+v,0)===2*pad.length+5);
      ok(decide(parse(bw),pin)===want);stats.pinned_balanced++;
    }
    let reverse=order.slice().reverse(),R=make(k,h,x,reverse,c2);
    for(let data of [false,true]){let z=draw(data?M:x.length),H=h.slice(),X=x.slice();(data?H:X)[z]^=1;
      let P2=make(k,H,X,order,c),R2=make(k,H,X,reverse,c2),d1=diffs(P.w,P2.w),d2=diffs(R.w,R2.w);
      ok(d1.length===2&&d1.join(",")===d2.join(","));stats.coordinate_checks++;
    }
    stats.packed_cases++;stats.max_word=Math.max(stats.max_word,P.w.length);stats.max_vertices=Math.max(stats.max_vertices,r);
  }
  return stats;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

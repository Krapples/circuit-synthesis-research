// Connected-cluster truncated character series for polynomial-map images.
// Run: node cubic_cluster_check.js
function run(){
  let seed=870013;
  function draw(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
  function ok(x,m="assertion failed"){if(!x)throw Error(m);}
  function parity(x){let r=0;while(x){r^=1;x&=x-1;}return r;}
  function wt(x){let r=0;while(x){r++;x&=x-1;}return r;}
  function canonical(terms){
    let D=new Map();
    for(let [a,c] of terms){a=[...new Set(a)].sort((a,b)=>a-b);let key=a.join(",");
      D.set(key,[a,(D.get(key)?.[1]||0)^c]);}
    return [...D.values()].filter(x=>x[1]);
  }
  function graph(q,terms){
    let G=Array.from({length:q},()=>new Set());
    for(let [a] of terms)for(let i of a)for(let j of a)if(i!==j)G[i].add(j);
    return G;
  }
  // Enumerate connected sets by growth, deduplicate. Paper circuit uses padded walks.
  function connected(G,d){
    let levels=[[],G.map((_,i)=>[i])];
    for(let s=2;s<=d;s++){
      let seen=new Map();
      for(let A of levels[s-1])for(let v of A)for(let w of G[v])if(!A.includes(w)){
        let B=[...A,w].sort((a,b)=>a-b);seen.set(B.join(","),B);
      }levels.push([...seen.values()]);
      if(!levels[s].length)break;
    }
    return levels.slice(1).flat();
  }
  function logDerivative(z,d){
    let h=Array(d+1).fill(0n);
    for(let j=1;j<=d;j++){
      h[j]=BigInt(j)*(z[j]||0n);
      for(let i=1;i<j;i++)h[j]-=h[i]*(z[j-i]||0n);
    }return h;
  }
  function recover(h,d){
    let z=Array(d+1).fill(0n);z[0]=1n;
    for(let j=1;j<=d;j++){
      let v=h[j];for(let i=1;i<j;i++)v+=h[i]*z[j-i];
      ok(v%BigInt(j)===0n,"nonexact division");z[j]=v/BigInt(j);
    }return z;
  }
  function fwht(a){for(let h=1;h<a.length;h*=2)for(let i=0;i<a.length;i+=2*h)for(let j=i;j<i+h;j++){let x=a[j],y=a[j+h];a[j]=x+y;a[j+h]=x-y;}return a;}
  function valueOn(terms,S){
    let a=0;for(let [A,c] of terms)if(A.every(i=>S.has(i)))a^=c;return a;
  }
  function cluster(q,t,terms,d,stats){
    let M=1<<t,G=graph(q,terms),Ulist=connected(G,d);
    stats.connected_sets+=Ulist.length;
    let H=Array.from({length:M},()=>Array(d+1).fill(0n));
    for(let U of Ulist){
      let s=U.length,N=1<<s,values=Array(N).fill(0),weights=Array.from({length:N},(_,i)=>wt(i));
      let local=terms.filter(([A])=>A.every(i=>U.includes(i))).map(([A,c])=>[A.reduce((m,i)=>m|(1<<U.indexOf(i)),0),c]);
      for(let x=0;x<N;x++)for(let [a,c] of local)if((x&a)===a)values[x]^=c;
      for(let l=0;l<M;l++){
        let Z=Array.from({length:N},(_,x)=>{let a=Array(s+1).fill(0n);a[weights[x]]=parity(l&values[x])?-1n:1n;return a;});
        for(let i=0;i<s;i++)for(let x=0;x<N;x++)if(x&(1<<i))
          for(let j=0;j<=s;j++)Z[x][j]+=Z[x^(1<<i)][j];
        let C=Array(d+1).fill(0n);
        for(let x=0;x<N;x++){
          let h=logDerivative(Z[x],d),sign=(s-weights[x])%2?-1n:1n;
          for(let j=1;j<=d;j++)C[j]+=sign*h[j];
          stats.local_series++;
        }
        for(let j=1;j<s;j++){ok(C[j]===0n,"low-degree cancellation");stats.cancellations++;}
        for(let j=s;j<=d;j++)H[l][j]+=C[j];
      }
    }
    let Z=H.map(h=>recover(h,d)),counts=Array.from({length:d+1},()=>Array(M).fill(0n));
    for(let j=0;j<=d;j++){
      let a=fwht(Z.map(z=>z[j]));counts[j]=a.map(v=>{ok(v%BigInt(M)===0n&&v>=0n);return v/BigInt(M);});
    }
    return counts;
  }
  function brute(q,t,terms,d){
    let C=Array.from({length:d+1},()=>Array(1<<t).fill(0n));
    for(let x=0;x<1<<q;x++){
      let w=wt(x);if(w>d)continue;let S=new Set();for(let i=0;i<q;i++)if(x&(1<<i))S.add(i);
      C[w][valueOn(terms,S)]++;
    }return C;
  }
  function pathDP(q,t,terms,d){
    let M=1<<t,groups=Array.from({length:q},()=>[]);
    for(let [A,c] of terms){let j=A.at(-1);ok(A.length&&j-A[0]<=2);groups[j].push([A.reduce((m,i)=>m|(1<<(j-i)),0),c]);}
    let H=Array.from({length:d+1},()=>Array(4*M).fill(0n));H[0][0]=1n;
    for(let j=0;j<q;j++){
      let T=Array.from({length:d+1},()=>Array(4*M).fill(0n));
      for(let s=0;s<4;s++)for(let b=0;b<2;b++){
        let w=(s<<1)|b,a=0;for(let [mask,c] of groups[j])if((w&mask)===mask)a^=c;
        for(let r=0;r+b<=d;r++)for(let x=0;x<M;x++)T[r+b][(w&3)*M+(x^a)]+=H[r][s*M+x];
      }H=T;
    }
    return H.map(A=>Array.from({length:M},(_,i)=>A[i]+A[M+i]+A[2*M+i]+A[3*M+i]));
  }
  function choose(q,j){let c=1n;for(let i=1;i<=j;i++)c=c*BigInt(q-i+1)/BigInt(i);return j>q?0n:c;}
  let stats={small_maps:0,long_maps:0,connected_sets:0,local_series:0,cancellations:0,exact_weight_address_checks:0,
    image_checks:0,largest_q:0,largest_truncation:0,largest_degree:0,high_degree_maps:0};
  function check(q,t,terms,path){
    terms=canonical(terms);let d=Math.min(q,3*t),M=1<<t;
    let A=cluster(q,t,terms,d,stats),B=path?pathDP(q,t,terms,d):brute(q,t,terms,d);
    let full=path?pathDP(q,t,terms,q):brute(q,t,terms,q);
    for(let j=0;j<=d;j++){
      ok(A[j].reduce((a,b)=>a+b,0n)===choose(q,j));
      for(let a=0;a<M;a++){ok(A[j][a]===B[j][a],"weight count");stats.exact_weight_address_checks++;}
    }
    for(let a=0;a<M;a++){
      ok(A.some(row=>row[a]>0n)===full.some(row=>row[a]>0n),"image mismatch");stats.image_checks++;
    }
    let deg=Math.max(0,...graph(q,terms).map(x=>x.size));
    stats[path?"long_maps":"small_maps"]++;stats.largest_q=Math.max(stats.largest_q,q);
    stats.largest_truncation=Math.max(stats.largest_truncation,d);stats.largest_degree=Math.max(stats.largest_degree,deg);
    if(deg>=7)stats.high_degree_maps++;
  }
  for(let t=1;t<=3;t++)for(let trial=0;trial<24;trial++){
    let q=1+draw(8),terms=[];
    for(let i=0;i<2*q;i++)terms.push([Array.from({length:1+draw(3)},()=>draw(q)),draw(1<<t)]);
    check(q,t,terms,false);
  }
  for(let trial=0;trial<8;trial++){
    let q=8,terms=[];for(let i=1;i<q;i++)terms.push([[0,i],1+draw(7)]);
    for(let i=1;i+1<q;i++)terms.push([[0,i,i+1],1+draw(7)]);
    check(q,3,terms,false);
  }
  for(let t=1;t<=2;t++)for(let trial=0;trial<4;trial++){
    let q=t===1?160:28,terms=[];
    for(let i=0;i<q;i++)terms.push([[i],draw(1<<t)]);
    for(let i=0;i+1<q;i++)terms.push([[i,i+1],1+draw((1<<t)-1)]);
    for(let i=0;i+2<q;i++)terms.push([[i,i+1,i+2],1+draw((1<<t)-1)]);
    check(q,t,terms,true);
  }
  return stats;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

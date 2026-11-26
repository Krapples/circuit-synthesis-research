// Deterministic component selection for bounded-degree Boolean maps.
// Run: node cubic_component_check.js
function run() {
  let seed = 870011;
  function rng(n) { seed = (Math.imul(seed,1664525)+1013904223)>>>0; return seed%n; }
  function parity(x) { let p=0; while(x){p^=1;x&=x-1;} return p; }
  function assert(x,msg="assertion failed"){if(!x)throw Error(msg);}
  function add(A,B){let C=new Set();for(let a of A)for(let b of B)C.add(a^b);return C;}
  function same(A,B){return A.size===B.size&&[...A].every(x=>B.has(x));}
  function coefficients(C){return C.terms.filter(([mask,v])=>mask&&v).map(x=>x[1]);}
  function value(C,x){let a=0;for(let [m,v] of C.terms)if((x&m)===m)a^=v;return a;}
  function image(C){let S=new Set();for(let x=0;x<2**C.d;x++)S.add(value(C,x));return S;}
  function spanInsert(B,v){for(let j=B.length-1;j>=0;j--)if(v&(1<<j)){if(B[j])v^=B[j];else {B[j]=v;return true;}}return false;}
  function select(Cs,k,R=8*k){
    let alive=Cs.map(()=>true), chosen=[];
    for(let r=0;r<R;r++){
      let basis=Array(k).fill(0), pick=new Set();
      for(let i=0;i<Cs.length;i++)if(alive[i]){
        for(let v of coefficients(Cs[i]))if(spanInsert(basis,v))pick.add(i);
      }
      if(!pick.size)break;
      for(let i of pick){alive[i]=false;chosen.push(i);}
    }
    return {chosen,rest:alive.map((a,i)=>a?i:-1).filter(i=>i>=0)};
  }
  function total(Cs,indices){let A=new Set([0]);for(let i of indices)A=add(A,image(Cs[i]));return A;}
  function fwht(a){for(let h=1;h<a.length;h*=2)for(let i=0;i<a.length;i+=2*h)for(let j=i;j<i+h;j++){let x=a[j],y=a[j+h];a[j]=x+y;a[j+h]=x-y;}return a;}
  function convolve(A,B,k){
    let M=1<<k, a=Array(M).fill(0),b=Array(M).fill(0);
    for(let x of A)a[x]=1;for(let x of B)b[x]=1;
    fwht(a);fwht(b);let c=fwht(a.map((v,i)=>v*b[i]));
    assert(c.every(x=>x>=0&&x%M===0));
    return new Set(c.map((v,i)=>v?i:-1).filter(i=>i>=0));
  }
  let stats={maps:0,components:0,selected:0,strict_reductions:0,walsh_convolutions:0,dual_checks:0,
    max_components:0,max_selected:0,largest_discard:0,biased_fiber_checks:0,count_reductions:0,count_assignments:0};
  function check(Cs,k){
    const {chosen,rest}=select(Cs,k);
    assert(chosen.length<=8*k*k);
    let A=total(Cs,Cs.map((_,i)=>i)),B=new Set([0]);
    for(let i of chosen){let S=image(Cs[i]);let next=convolve(B,S,k);assert(same(next,add(B,S)));B=next;stats.walsh_convolutions++;}
    assert(same(A,B),"image lost");
    for(let lam=1;lam<1<<k;lam++){
      if(rest.some(i=>coefficients(Cs[i]).some(v=>parity(lam&v)))){
        let hit=chosen.filter(i=>coefficients(Cs[i]).some(v=>parity(lam&v))).length;
        assert(hit>=8*k,"rank-round coverage");stats.dual_checks++;
      }
    }
    stats.maps++;stats.components+=Cs.length;stats.selected+=chosen.length;
    stats.strict_reductions+=rest.length>0;stats.max_components=Math.max(stats.max_components,Cs.length);
    stats.max_selected=Math.max(stats.max_selected,chosen.length);
    stats.largest_discard=Math.max(stats.largest_discard,rest.length);
  }
  // Use high bits of LCG to avoid low-bit correlations in draws.
  function draw(n){rng(1);return (seed>>>8)%n;}
  for(let k=1;k<=7;k++)for(let trial=0;trial<30;trial++){
    let Cs=[];let count=1+draw(40);
    for(let i=0;i<count;i++){
      let d=1+draw(Math.min(k+2,7)),terms=[];
      for(let mask=1;mask<1<<d;mask++){
        let w=mask.toString(2).split("1").length-1;
        if(w<=3&&draw(5)===0)terms.push([mask,draw(1<<k)]);
      }
      Cs.push({d,terms});
      for(let l=1;l<1<<k;l++){
        if(terms.some(([m,v])=>parity(v&l))){
          let ones=0;for(let x=0;x<1<<d;x++)ones+=parity(l&value(Cs.at(-1),x));
          assert(8*ones>=1<<d&&8*((1<<d)-ones)>=1<<d);
          stats.biased_fiber_checks++;
        }
      }
    }
    check(Cs,k);
  }
  // Many genuinely cubic independent AND blocks, plus a correlated low marginal.
  for(let k=3;k<=8;k++){
    let Cs=[];
    for(let i=0;i<1200;i++)Cs.push({d:3,terms:[[7,1<<(i%(k-2))]]});
    Cs.push({d:3,terms:[[7,3<<(k-2)]]}); // top two output coordinates agree
    check(Cs,k);
  }
  // #3SAT -> quadratic constraints -> one cubic character sum.
  for(let q=1;q<=4;q++)for(let trial=0;trial<24;trial++){
    let c=1+draw(3),clauses=Array.from({length:c},()=>Array.from({length:3},()=>[draw(q),draw(2)]));
    function falseLit(x,l){return ((x>>l[0])&1)^l[1]^1;}
    let want=0,sum=0;
    for(let x=0;x<1<<q;x++){
      if(clauses.every(C=>!C.every(l=>falseLit(x,l))))want++;
      for(let z=0;z<1<<c;z++){
        let g=0;
        for(let i=0;i<c;i++){
          let [a,b,d]=clauses[i].map(l=>falseLit(x,l)), zi=z>>i&1;
          g|=(zi^(a&b))<<(2*i);g|=(zi&d)<<(2*i+1);
        }
        for(let y=0;y<1<<(2*c);y++){sum+=parity(y&g)?-1:1;stats.count_assignments++;}
      }
    }
    assert(sum==want*(1<<(2*c)));stats.count_reductions++;
  }
  return stats;
}
if (typeof module !== "undefined" && require.main===module) { console.log(JSON.stringify(run(),null,2)); console.log("all assertions passed"); }

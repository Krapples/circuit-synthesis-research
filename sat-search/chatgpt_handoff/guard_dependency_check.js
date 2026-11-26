// Single-reader guard dependencies and cylinder peeling.
// Run: node guard_dependency_check.js
function run(){
 function ok(x,m="assertion failed"){if(!x)throw Error(m);}
 function pop(x){let p=0;while(x){p++;x&=x-1;}return p;}
 function costs(n,cap){
  let mask=(1<<(1<<n))-1,base=[];let canon=v=>Math.min(v,v^mask);
  for(let i=0;i<n;i++){let v=0;for(let x=0;x<1<<n;x++)if(x>>i&1)v|=1<<x;base.push(canon(v));}
  base.sort((a,b)=>a-b);let L=Array(mask+1).fill(cap+1),states=new Map([[base.join(","),base]]);
  for(let d=0;d<=cap;d++){
   let next=new Map();
   for(let A of states.values()){
    for(let v of [0,...A])L[v]=L[v^mask]=Math.min(L[v],d);
    if(d===cap)continue;
    for(let i=0;i<A.length;i++)for(let j=i+1;j<A.length;j++)for(let p=0;p<4;p++){
     let v=canon((A[i]^(p&1?mask:0))&(A[j]^(p&2?mask:0)));
     if(!v||A.includes(v))continue;
     if(d+1===cap){L[v]=L[v^mask]=Math.min(L[v],d+1);continue;}
     let B=[...A,v].sort((a,b)=>a-b);next.set(B.join(","),B);
    }
   }states=next;
  }
  ok(L.every(v=>v<=cap),"unresolved small cost");return L;
 }
 const L=[[],costs(1,1),costs(2,3),costs(3,6)];
 function cofactor(f,n,S,z){
  let t=0,I=[];for(let i=0;i<n;i++)if(S>>i&1)I.push(i);
  for(let x=0;x<1<<I.length;x++){let v=z;for(let j=0;j<I.length;j++)if(x>>j&1)v|=1<<I[j];if(f>>v&1)t|=1<<x;}return t;
 }
 function diff(f,x,i){return ((f>>x)^(f>>(x^(1<<i))))&1;}
 function analyze(f,n){
  let forced=Array(n).fill(0),mandatory=0,essential=0,share=Array(n).fill(0),zeros=Array.from({length:n},()=>[]);
  const full=(1<<n)-1;
  for(let i=0;i<n;i++){
   for(let x=0;x<1<<n;x++)if(!(x>>i&1)){if(!diff(f,x,i))zeros[i].push(x);else essential|=1<<i;}
   if(!zeros[i].length)mandatory|=1<<i;
   let Z=new Set(zeros[i]);
   for(let j=0;j<n;j++)if(j!==i){
    if(!zeros[i].some(x=>Z.has(x^(1<<j))))forced[i]|=1<<j;
    for(let p=0;p<4;p++){
     let R=[];for(let q=0;q<4;q++)if(q!==p)R.push(cofactor(f,n,full^((1<<i)|(1<<j)),((q&1)<<i)|((q>>1)<<j)));
     if(R.every(v=>v===R[0]))share[i]|=1<<j;
    }
   }
  }
  function feasible(U){
   if(U&mandatory)return false;
   function part(left,groups){
    if(!left){
     let owner=Array(n).fill(-1);groups.forEach((g,j)=>{for(let i=0;i<n;i++)if(g>>i&1)owner[i]=j;});
     let edges=groups.map(()=>0);
     for(let g of groups)if(pop(g)===2)for(let i=0;i<n;i++)if(g>>i&1)if(forced[i]&~g)return false;
     for(let i=0;i<n;i++)if(U>>i&1)for(let j=0;j<n;j++)if((U>>j&1)&&(forced[i]>>j&1)&&owner[i]!==owner[j])edges[owner[i]]|=1<<owner[j];
     let remaining=(1<<groups.length)-1;
     while(remaining){let hit=edges.findIndex((e,i)=>(remaining>>i&1)&&!(e&remaining));if(hit<0)return false;remaining^=1<<hit;}
     return true;
    }
    let bit=left&-left,i=31-Math.clz32(bit),rest=left^bit;
    if(part(rest,[...groups,bit]))return true;
    for(let j=0;j<n;j++)if((rest>>j&1)&&(share[i]>>j&1))if(part(rest^(1<<j),[...groups,bit|(1<<j)]))return true;
    return false;
   }return part(U,[]);
  }
  const peelMemo=new Map([[0,true]]);
  function peel(U){
   if(peelMemo.has(U))return peelMemo.get(U);
   let yes=false;
   if(!(U&mandatory))for(let i=0;i<n&&!yes;i++)if(U>>i&1){
    let rest=U^(1<<i),groups=new Map();
    for(let x of zeros[i]){let key=x&~rest;groups.set(key,(groups.get(key)||0)+1);}
    if([...groups.values()].some(v=>v===2**pop(rest))&&peel(rest))yes=true;
    for(let j=0;j<n&&!yes;j++)if((rest>>j&1)&&(share[i]>>j&1))if(peel(rest^(1<<j)))yes=true;
   }
   peelMemo.set(U,yes);return yes;
  }
  let maxSingle=0,maxPeel=0;
  for(let U=0;U<1<<n;U++){
   if(pop(U)>maxSingle&&feasible(U))maxSingle=pop(U);
   if(pop(U)>maxPeel&&peel(U))maxPeel=pop(U);
  }
  ok(maxPeel<=maxSingle,"peel stronger");
  return {forced,mandatory,essential,share,maxSingle,maxPeel,cycleBound:2*n-maxSingle-1,peelBound:2*n-maxPeel-1,feasible,peel};
 }
 let stats={full_support_tables:0,exact_three_input_costs:256,three_input_cost_histogram:Array.from({length:7},(_,i)=>L[3].filter(v=>v===i).length),cycle_improves_baseline:0,peel_improves_baseline:0,peel_improves_cycle:0,cycle_improves_mandatory:0,mandatory_only_improves_baseline:0,first_improvement:null,first_peel_improvement:null,random_full_support_aigs:0,actual_single_reader_checks:0,actual_bound_checks:0};
 for(let f=0;f<65536;f++){
  let a=analyze(f,4);if(a.essential!==15)continue;stats.full_support_tables++;
  let base=3;
  for(let S=1;S<15;S++)for(let z=0;z<16;z++)if(!(z&S))base=Math.max(base,L[pop(S)][cofactor(f,4,S,z)]+4-pop(S));
  if(a.cycleBound>3+pop(a.mandatory))stats.cycle_improves_mandatory++;
  if(a.cycleBound>base){stats.cycle_improves_baseline++;if(!stats.first_improvement)stats.first_improvement={hex:f.toString(16),base,cycle:a.cycleBound,peel:a.peelBound,forced:a.forced,mandatory:a.mandatory};}
  if(a.peelBound>base)stats.peel_improves_baseline++;
  if(a.peelBound>a.cycleBound){stats.peel_improves_cycle++;if(!stats.first_peel_improvement)stats.first_peel_improvement={hex:f.toString(16),base,cycle:a.cycleBound,peel:a.peelBound};}
  if(3+pop(a.mandatory)>base)stats.mandatory_only_improves_baseline++;
 }
 let seed=870017;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 for(let trial=0;trial<5000;trial++){
  let n=3+rnd(2),mask=(1<<(1<<n))-1,V=[],E=[];
  for(let i=0;i<n;i++){let t=0;for(let x=0;x<1<<n;x++)if(x>>i&1)t|=1<<x;V.push(t);}
  let budget=4+rnd(15);
  for(let j=0;j<budget;j++){
   let a=rnd(V.length),b=rnd(V.length),p=rnd(2),q=rnd(2),v=(V[a]^(p?mask:0))&(V[b]^(q?mask:0));
   if(v===0||v===mask||V.slice(0,n).some(x=>x===v||x===(v^mask)))continue;
   E.push([a,b]);V.push(v);
  }
  if(!E.length)continue;let f=V.at(-1),a=analyze(f,n);
  if(a.essential!==(1<<n)-1)continue;
  let live=new Set(),stack=[V.length-1],read=Array(n).fill(0);
  while(stack.length){let g=stack.pop();if(g<n){read[g]++;continue;}if(live.has(g))continue;live.add(g);stack.push(...E[g-n]);}
  let U=read.reduce((m,v,i)=>m|(v===1?1<<i:0),0);
  ok(a.feasible(U)&&a.peel(U),"actual single reader rejected");stats.actual_single_reader_checks++;
  ok(live.size>=a.peelBound,"actual size");stats.actual_bound_checks++;stats.random_full_support_aigs++;
 }
 return stats;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

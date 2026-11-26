// Packed unit clause separator: rank and grammar replay.
function run(){
 let seed=870019;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(x,m="assertion failed"){if(!x)throw Error(m);}
 function pop(x){let p=0;while(x){p++;x&=x-1;}return p;}
 function rank2(rows){let B=new Map();for(let v of rows)while(v){let i=31-Math.clz32(v);if(!B.has(i)){B.set(i,v);break;}v^=B.get(i);}return B.size;}
 function rank(A){A=A.map(r=>r.map(x=>(x%101+101)%101));let r=0;for(let j=0;j<A[0].length&&r<A.length;j++){let i=r;while(i<A.length&&!A[i][j])i++;if(i===A.length)continue;[A[r],A[i]]=[A[i],A[r]];let z=1;while(z*A[r][j]%101!==1)z++;for(let h=j;h<A[r].length;h++)A[r][h]=A[r][h]*z%101;for(let k=r+1;k<A.length;k++)if(A[k][j]){let t=A[k][j];for(let h=j;h<A[k].length;h++)A[k][h]=(A[k][h]-t*A[r][h]+10201)%101;}r++;}return r;}
 function matrix(l){let R=Array(l).fill(0);for(let i=0;i<l;i++)for(let j=i+1;j<l;j++)if(rnd(2)){R[i]|=1<<j;R[j]|=1<<i;}return R;}
 function quad(R,x){let p=0;for(let i=0;i<R.length;i++)if(x>>i&1)p^=pop(R[i]&x&~((1<<(i+1))-1))%2;return p;}
 function sub(A){let out=[];for(let x=A;;x=(x-1)&A){out.push(x);if(!x)return out;}}
 function cr(R,A,B){return rank2(R.filter((_,i)=>A>>i&1).map(r=>r&B));}
 function local(R,A,B,c){let r=cr(R,A,B),F=sub(A).map(a=>sub(B).map(b=>quad(R,c|a|b)));let p=rank(F),q=rank(F.map(row=>row.map(x=>1-x))),h=rank(F.map(row=>row.map(x=>x?-1:1)));ok(h===2**r,"phase rank");ok(Math.max(p,q)>=Math.ceil(2**r/2),"indicator rank");return {sign:p>=q?1:0,rank:Math.max(p,q)};}
 function params(l,m){let P=2**l,Q=2**Math.ceil(Math.log2((m+1)*P));return {P,Q,w:Math.log2(Q)+1};}
 function unit(id,s){let a=[1,s];do{a.push(1,id%2);id=Math.floor(id/2);}while(id);return a.concat([0,1,0,0]);}
 function parse(w){let D=new Map(),i=0,sat=true;while(i<w.length){ok(w[i++]===1);let s=w[i++],id=0,p=1,last=0;while(w[i]===1){last=w[i+1];id+=p*last;p*=2;i+=2;}ok(last===1&&w[i++]===0&&w[i++]===1&&w[i++]===0&&w[i++]===0,"parse");if(D.has(id)&&D.get(id)!==s)sat=false;D.set(id,s);}return sat;}
 function encode(R,m,slots,x){let {P,Q,w}=params(R.length,m),out=[];for(let p=0;p<P;p++)out.push(...unit(Q+p,quad(R,p)));for(let i=0;i<m;i++)out.push(...unit(Q+slots[i].tag*P+x[i],slots[i].sign));ok(out.length===(P+m)*(2*w+6));return out;}
 let S={local_cut_checks:0,pair_rank_checks:0,partitions:0,strict_balance_partitions:0,mixed_mode_partitions:0,pair_mode_partitions:0,hybrid_partitions:0,grammar_sat_checks:0,satisfiable:0,unsatisfiable:0,coordinate_checks:0,max_word:0,max_terminal_bits:0,min_log_rank_fraction:1,larger_cut_checks:0,min_larger_cross_rank:100};
 for(let l=3;l<=6;l++){let R=matrix(l),all=(1<<l)-1;for(let A=1;A<=all;A++)for(let B=1;B<=all;B++)if(!(A&B)){local(R,A,B,rnd(1<<l)&~(A|B));S.local_cut_checks++;}for(let d=1;d<=l;d++){let N=1<<d,M=Array.from({length:N},(_,i)=>Array.from({length:N},(_,j)=>+(i!==j)));ok(rank(M)===N,"pair rank");S.pair_rank_checks++;}}
 const l=6,m=32,T=l*m,all=(1<<l)-1;
 for(let test=0;test<72;test++){
  let A=[],B=[],C=[];
  for(let i=0;i<m;i++){let a=0,b=0,c=0;for(let j=0;j<l;j++){let v=test%4===0?(i<m/2?0:1):test%4===1?j%2:test%4===2?(i<m/4?0:i<3*m/4?1:j%2):rnd(2);if(test%6===5&&rnd(40)===0)v=2;if(v===0)a|=1<<j;else if(v===1)b|=1<<j;else c|=1<<j;}A.push(a);B.push(b);C.push(c);}
  let ac=A.reduce((s,x)=>s+pop(x),0),bc=B.reduce((s,x)=>s+pop(x),0);if(Math.min(ac,bc)>=T/4&&T-ac-bc<=T/256)S.strict_balance_partitions++;
  let mixed=[],left=[],right=[];
  for(let i=0;i<m;i++){if(pop(C[i])>=l/8)continue;if(pop(A[i])>=l/8&&pop(B[i])>=l/8)mixed.push(i);else if(pop(A[i])>pop(B[i]))left.push(i);else right.push(i);}
  let R;for(let tr=0;tr<10000;tr++){R=matrix(l);if(mixed.every(i=>cr(R,A[i],B[i])>=1))break;}ok(mixed.every(i=>cr(R,A[i],B[i])>=1),"finite dictionary");
  let slots=Array.from({length:m},(_,i)=>({tag:i+1,sign:1})),factors=[],free=Array(m).fill(0);
  for(let i of mixed){let a=local(R,A[i],B[i],0);slots[i]={tag:0,sign:a.sign};free[i]=A[i]|B[i];factors.push({i,sign:a.sign,rank:a.rank});}
  let pairs=Math.min(left.length,right.length);
  for(let j=0;j<pairs;j++){let i=left[j],v=right[j],cross=A[i]&B[v];ok(pop(cross)>0);slots[v]={tag:i+1,sign:0};free[i]=free[v]=cross;factors.push({i,v,rank:2**pop(cross)});}
  S.min_log_rank_fraction=Math.min(S.min_log_rank_fraction,factors.reduce((s,f)=>s+Math.log2(f.rank),0)/T);
  if(mixed.length)S.mixed_mode_partitions++;if(pairs)S.pair_mode_partitions++;if(mixed.length&&pairs)S.hybrid_partitions++;
  let zero=encode(R,m,slots,Array(m).fill(0)),{P,w}=params(l,m);
  function diff(a,b){return a.map((x,i)=>x!==b[i]?i:-1).filter(x=>x>=0);}
  for(let j=0;j<10;j++){let i=rnd(m),b=rnd(l),x=Array(m).fill(0);x[i]=1<<b;let other=slots.map((s,i)=>({tag:i+1,sign:0})),a=encode(R,m,slots,x),z=encode(R,m,other,Array(m).fill(0)),v=encode(R,m,other,x),expected=(P+i)*(2*w+6)+3+2*b;ok(diff(zero,a).join(",")===String(expected)&&diff(z,v).join(",")===String(expected),"coordinate");S.coordinate_checks++;}
  for(let j=0;j<18;j++){
   let x=free.map(mask=>rnd(1<<l)&mask);
   if(j===0)for(let f of factors){if(f.v!==undefined){x[f.i]=free[f.i]&-free[f.i];x[f.v]=0;}else{let v=0;while(v<=all&&(v&~free[f.i]||quad(R,v)!==f.sign))v++;ok(v<=all,"positive local");x[f.i]=v;}}
   let want=factors.every(f=>f.v===undefined?quad(R,x[f.i])===f.sign:x[f.i]!==x[f.v]),word=encode(R,m,slots,x);ok(parse(word)===want,"unit semantics");if(j===0)ok(want,"programmed positive");S[want?"satisfiable":"unsatisfiable"]++;S.grammar_sat_checks++;S.max_word=Math.max(S.max_word,word.length);
  }S.partitions++;S.max_terminal_bits=Math.max(S.max_terminal_bits,T);
 }
 for(let t=0;t<200;t++){let l=24,R=matrix(l),A=0,B=0;for(let i=0;i<l;i++){let s=rnd(3);if(s===0)A|=1<<i;else if(s===1)B|=1<<i;}if(Math.min(pop(A),pop(B))<3)continue;S.min_larger_cross_rank=Math.min(S.min_larger_cross_rank,cr(R,A,B));S.larger_cut_checks++;}
 return S;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

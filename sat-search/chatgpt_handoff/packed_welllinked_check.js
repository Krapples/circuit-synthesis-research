// Arbitrary packed terminal cuts and prescribed matching cut demands.
// Run: node packed_welllinked_check.js
function run(){
 let seed=870020;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
 function ok(x,m="assertion failed"){if(!x)throw Error(m);}
 function pop(x){let p=0;while(x){p++;x&=x-1;}return p;}
 function rank2(rows){let B=new Map();for(let v of rows)while(v){let j=31-Math.clz32(v);if(!B.has(j)){B.set(j,v);break;}v^=B.get(j);}return B.size;}
 function rank(A){A=A.map(r=>r.map(x=>(x%101+101)%101));let r=0;for(let j=0;j<A[0].length&&r<A.length;j++){let i=r;while(i<A.length&&!A[i][j])i++;if(i===A.length)continue;[A[r],A[i]]=[A[i],A[r]];let z=1;while(z*A[r][j]%101!==1)z++;for(let h=j;h<A[r].length;h++)A[r][h]=A[r][h]*z%101;for(let k=r+1;k<A.length;k++)if(A[k][j]){let t=A[k][j];for(let h=j;h<A[k].length;h++)A[k][h]=(A[k][h]-t*A[r][h]+10201)%101;}r++;}return r;}
 function matrix(l,bits){let R=Array(l).fill(0),j=0;for(let a=0;a<l;a++)for(let b=a+1;b<l;b++,j++)if(bits>>j&1){R[a]|=1<<b;R[b]|=1<<a;}return R;}
 function quad(R,x){let p=0;for(let i=0;i<R.length;i++)if(x>>i&1)p^=pop(R[i]&x&~((1<<(i+1))-1))%2;return p;}
 function sub(A){let L=[];for(let x=A;;x=(x-1)&A){L.push(x);if(!x)return L;}}
 function cross(R,A,B){return rank2(R.filter((_,i)=>A>>i&1).map(r=>r&B));}
 function local(R,A,B){let F=sub(A).map(a=>sub(B).map(b=>quad(R,a|b))),p=rank(F),q=rank(F.map(r=>r.map(x=>1-x))),r=cross(R,A,B);ok(rank(F.map(row=>row.map(x=>x?-1:1)))===2**r,"character rank");ok(Math.max(p,q)>=2**(r/2),"indicator log rank");return {sign:p>=q?1:0,rank:Math.max(p,q)};}
 function params(l,m){let P=2**l,Q=2**Math.ceil(Math.log2((m+1)*P));return {P,Q,w:Math.log2(Q)+1};}
 function unit(id,s){let a=[1,s];do{a.push(1,id%2);id=Math.floor(id/2);}while(id);return a.concat([0,1,0,0]);}
 function parse(w){let D=new Map(),i=0,sat=true;while(i<w.length){ok(w[i++]===1);let s=w[i++],id=0,p=1,last=0;while(w[i]===1){last=w[i+1];id+=p*last;p*=2;i+=2;}ok(last===1&&w[i++]===0&&w[i++]===1&&w[i++]===0&&w[i++]===0,"parse");if(D.has(id)&&D.get(id)!==s)sat=false;D.set(id,s);}return sat;}
 function encode(R,slots,x){let {P,Q,w}=params(R.length,slots.length),out=[];for(let p=0;p<P;p++)out.push(...unit(Q+p,quad(R,p)));for(let i=0;i<slots.length;i++)out.push(...unit(Q+slots[i].tag*P+x[i],slots[i].sign));ok(out.length===(P+slots.length)*(2*w+6));return out;}
 const S={dictionary_expectation_checks:0,local_rank_checks:0,partitions:0,separator_large_cases:0,local_cases:0,dominant_cases:0,unbalanced_cases:0,min_smaller_side:1000000,min_certified_rank_ratio:1,grammar_checks:0,matching_partitions:0,matching_pair_rank_checks:0,matching_grammar_checks:0,matching_cross_bits:0,matching_mixed_orientation_pairs:0,layout_checks:0};
 const l=4,m=32,all=(1<<l)-1,dicts=Array.from({length:2**(l*(l-1)/2)},(_,i)=>matrix(l,i));
 // Verify the expectation bound exactly over all symmetric dictionaries
 // on every disjoint cut of this small pattern width.
 for(let A=1;A<=all;A++)for(let B=1;B<=all;B++)if(!(A&B)){
  let r=dicts.reduce((s,R)=>s+cross(R,A,B),0);ok(2*r>=dicts.length*Math.min(pop(A),pop(B)),"mean rank");S.dictionary_expectation_checks++;
  for(let R of dicts){local(R,A,B);S.local_rank_checks++;}
 }
 function program(A,B,C){
  let a=A.reduce((s,x)=>s+pop(x),0),b=B.reduce((s,x)=>s+pop(x),0),z=C.reduce((s,x)=>s+pop(x),0),u=Math.min(a,b);
  if(!u)return null;S.partitions++;S.min_smaller_side=Math.min(S.min_smaller_side,u);
  if(u<m*l/8)S.unbalanced_cases++;
  if(64*z>u){S.separator_large_cases++;return null;}
  let M=A.reduce((s,x,i)=>s+Math.min(pop(x),pop(B[i])),0);
  let R=dicts[0],slots=Array.from({length:m},(_,i)=>({tag:i+1,sign:1})),free=Array(m).fill(0),F=[];
  if(32*M>=u){
   S.local_cases++;
   let best=-1;for(let R0 of dicts){let score=A.reduce((s,x,i)=>s+cross(R0,x,B[i]),0);if(score>best){best=score;R=R0;}}
   ok(2*best>=M,"joint expectation");
   for(let i=0;i<m;i++)if(A[i]&&B[i]){
    let a=local(R,A[i],B[i]);if(a.rank<=1)continue;
    slots[i]={tag:0,sign:a.sign};free[i]=A[i]|B[i];F.push({i,sign:a.sign,rank:a.rank});
   }
  }else{
   S.dominant_cases++;let L=[],J=[];
   for(let i=0;i<m;i++){if(8*pop(C[i])>=l||8*Math.min(pop(A[i]),pop(B[i]))>=l)continue;if(pop(A[i])>pop(B[i]))L.push(i);else J.push(i);}
   ok(2*l*Math.min(L.length,J.length)>=u,"dominant count");
   for(let j=0;j<Math.min(L.length,J.length);j++){let i=L[j],v=J[j],common=A[i]&B[v];ok(2*pop(common)>l,"overlap");slots[v]={tag:i+1,sign:0};free[i]=free[v]=common;F.push({i,v,rank:2**pop(common)});}
  }
  let log=F.reduce((s,x)=>s+Math.log2(x.rank),0);ok(128*log>=u,"rank certificate");S.min_certified_rank_ratio=Math.min(S.min_certified_rank_ratio,log/u);
  return {R,slots,free,F};
 }
 for(let trial=0;trial<320;trial++){
  let A=[],B=[],C=[];
  for(let i=0;i<m;i++){let a=0,b=0,c=0;for(let j=0;j<l;j++){
   let v;
   switch(trial%5){
    case 0:v=i<1+rnd(2)?0:1;break;
    case 1:v=(i===0&&j===0)?0:1;break;
    case 2:v=i<trial%31+1?0:1;break;
    case 3:v=rnd(11)===0?2:rnd(2);break;
    default:v=rnd(5)===0?0:1;
   }
   if(v===0)a|=1<<j;else if(v===1)b|=1<<j;else c|=1<<j;
  }A.push(a);B.push(b);C.push(c);}
  let K=program(A,B,C);if(!K)continue;
  for(let t=0;t<6;t++){
   let x=K.free.map(a=>rnd(1<<l)&a);
   if(t===0)for(let f of K.F){if(f.v!==undefined){x[f.i]=K.free[f.i]&-K.free[f.i];x[f.v]=0;}else{x[f.i]=sub(K.free[f.i]).find(v=>quad(K.R,v)===f.sign);ok(x[f.i]!==undefined);}}
   let want=K.F.every(f=>f.v===undefined?quad(K.R,x[f.i])===f.sign:x[f.i]!==x[f.v]);
   ok(parse(encode(K.R,K.slots,x))===want,"program grammar");if(!t)ok(want,"positive");S.grammar_checks++;
  }
 }
 // Exact rank for a prescribed matching on aligned coordinates, even when
 // the orientations of the crossed pairs differ within one slot pair.
 for(let trial=0;trial<120;trial++){
  let slots=Array.from({length:m},(_,i)=>({tag:1+Math.floor(i/2),sign:i%2})),R=dicts[0],F=[],free=Array(m).fill(0),fixed=Array(m).fill(0);
  for(let i=0;i<m;i+=2){
   let a=rnd(1<<l),b=rnd(1<<l),c=rnd(1<<l)&~a,d=rnd(1<<l)&~b;
   let L=a&~(b|d),J=b&~(a|c),crossed=L|J,r=pop(crossed);
   if(L&&J)S.matching_mixed_orientation_pairs++;
   free[i]=free[i+1]=crossed;
   if(!r){fixed[i]=1;continue;}
   let U=sub(crossed),M=U.map(x=>U.map(y=>+(((x&L)|(y&J))!==((y&L)|(x&J)))));
   ok(rank(M)===2**r,"matching rank");S.matching_pair_rank_checks++;S.matching_cross_bits+=r;F.push(i);
  }
  for(let t=0;t<8;t++){
   let x=free.map((a,i)=>(rnd(1<<l)&a)|fixed[i]);
   if(t===0)for(let i of F){x[i]=free[i]&-free[i];x[i+1]=0;}
   let want=F.every(i=>x[i]!==x[i+1]);ok(want===slots.every((_,i)=>i%2||x[i]!==x[i+1]),"fixed matching factors");ok(parse(encode(R,slots,x))===want,"matching grammar");if(!t)ok(want);S.matching_grammar_checks++;
  }S.matching_partitions++;
 }
 // Exact discrete coarea identity on arbitrary layouts of multigraphs.
 for(let t=0;t<300;t++){
  let n=4+rnd(20),x=Array.from({length:n},()=>rnd(31)-15),E=Array.from({length:2*n},()=>[rnd(n),rnd(n)]),term=x.filter((_,i)=>i%2===0);
  let len=E.reduce((s,[a,b])=>s+Math.abs(x[a]-x[b]),0),cuts=0,dem=0;
  for(let j=-15;j<15;j++){cuts+=E.filter(([a,b])=>(x[a]<=j)!==(x[b]<=j)).length;let a=term.filter(v=>v<=j).length;dem+=Math.min(a,term.length-a);}
  let median=term.slice().sort((a,b)=>a-b)[Math.floor(term.length/2)];
  ok(cuts===len&&dem===term.reduce((s,v)=>s+Math.abs(v-median),0),"coarea");S.layout_checks++;
 }
 // Verify no-output-message rank argument on actual finite circuit DAGs.
 S.edge_protocol_checks=0;S.vertex_protocol_checks=0;S.transcript_rectangles=0;
 function protocol(n,E,side,vertex){
  let A=0,B=0;for(let i=0;i<n;i++){if(side[i]===0)A|=1<<i;else if(side[i]===1)B|=1<<i;}
  if(!A||!B)return;
  let publicBits=rnd(1<<n)&~(A|B),X=sub(A),Y=sub(B),M=[],groups=new Map(),cost=0;
  for(let j=0;j<E.length;j++)for(let l of E[j]){
   let v=l>>1,g=n+j;
   if(vertex){if(side[g]===2&&side[v]!==2)cost++;}
   else if(side[g]!==side[v])cost++;
  }
  for(let x of X){let row=[];for(let y of Y){
   let input=x|y|publicBits,V=Array.from({length:n},(_,i)=>input>>i&1),trans="";
   for(let j=0;j<E.length;j++){
    let [u,v]=E[j],g=n+j;
    for(let l of [u,v])if(vertex?(side[g]===2&&side[l>>1]!==2):side[g]!==side[l>>1])trans+=V[l>>1];
    V.push((V[u>>1]^(u&1))&(V[v>>1]^(v&1)));
   }
   ok(trans.length===cost,"protocol schedule");let z=V.at(-1);row.push(z);
   if(!groups.has(trans))groups.set(trans,{all:[],yes:[]});
   let G=groups.get(trans);G.all.push([x,y]);if(z)G.yes.push([x,y]);
  }M.push(row);}
  function rectangle(P){return P.length===new Set(P.map(a=>a[0])).size*new Set(P.map(a=>a[1])).size;}
  for(let G of groups.values()){ok(rectangle(G.all)&&rectangle(G.yes),"transcript rectangle");S.transcript_rectangles+=2;}
  ok(groups.size<=2**cost&&rank(M)<=2**cost,"communication rank");
  if(vertex){ok(cost<=2*side.filter(v=>v===2).length);S.vertex_protocol_checks++;}
  else S.edge_protocol_checks++;
 }
 for(let t=0;t<500;t++){
  let n=3+rnd(4),g=3+rnd(9),E=Array.from({length:g},(_,i)=>[2*rnd(n+i)+rnd(2),2*rnd(n+i)+rnd(2)]);
  let side=Array.from({length:n+g},()=>rnd(2));protocol(n,E,side,false);
  // Mark one endpoint of every A-B wire as a separator vertex.
  for(let j=0;j<g;j++)for(let l of E[j])if(side[l>>1]!==2&&side[n+j]!==2&&side[l>>1]!==side[n+j])side[rnd(2)?l>>1:n+j]=2;
  for(let j=0;j<g;j++)for(let l of E[j])ok(side[l>>1]===2||side[n+j]===2||side[l>>1]===side[n+j]);
  protocol(n,E,side,true);
 }
 return S;
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

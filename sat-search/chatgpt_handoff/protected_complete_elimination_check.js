"use strict";
// Complete protected elimination, fair affine systems, query freezing and pair retirement.
function replay(){
 const assert=(v,m)=>{if(!v)throw Error(m)};const bit=(x,i)=>(x>>>i)&1,par=x=>{let p=0;for(;x;x&=x-1)p^=1;return p};
 const rank=rows=>{let b=[];for(let v of rows){for(let j=31;j>=0&&v;j--)if(bit(v,j)){if(b[j])v^=b[j];else{b[j]=v;break}}}return b.filter(Boolean).length};
 function build(D,style){
  let g=[],next=2*D+1;const and=(a,b)=>{let id=next++;g.push({id,a,b,op:"and"});return 2*id},xor=(a,b)=>{let id=next++;g.push({id,a,b,op:"xor"});return 2*id},or=(a,b)=>and(a^1,b^1)^1;
  let x=Array.from({length:D},(_,i)=>2*(i+1)),y=Array.from({length:D},(_,i)=>2*(D+i+1)),f=[];
  for(let i=0;i<D;){
   if(style>=1&&i+1<D){let u=x[i]^1,v=x[i+1]^1,p;
    if(style===2||style===4){let w=xor(u,v);p=xor(u,and(u,w))}else p=and(u,v);
    let q=and(y[i],y[i+1]),a=and(y[i],u),b=and(y[i+1],v),c=and(q,p);f.push(xor(xor(a,b),c)^1);i+=2;
   }else{let a;if(style===3||style===4){let q=and(y[i],y[(i+1)%D]),w=xor(x[i],q);a=xor(and(y[i],w^1),q)}
    else if(style===2){let w=xor(x[i],y[i]);a=and(y[i],w)}else a=and(y[i],x[i]^1);f.push(a^1);i++}
  }
  let out=f.reduce(and);return {D,g,out,style};
 }
 let circuits=0,states=0,semantic=0,exchanges=0,rank1=0,rank2=0,retire=0,freeze=0,affine=0,readerChecks=0,retireExtra=0,nonlinearOffsets=0,finalOne=0,pruned=0,profiles=[];
 function run(C,preferPair){
  let D=C.D,Y=1<<D,ones=(1n<<BigInt(Y))-1n,params=Array.from({length:D},(_,i)=>i+1),pairs=[],aux=[],eq=[],g=C.g.map(x=>({...x})),out=C.out,query=new Map([[0,0n]]),orig=C.g.length,deleted=new Set,frozen=new Set;
  for(let i=0;i<D;i++){let tab=0n;for(let y=0;y<Y;y++)if(bit(y,i))tab|=1n<<BigInt(y);query.set(D+i+1,tab)}
  let map=Array.from({length:D},(_,i)=>({m:1<<i,t:0n})),R=0,P=0,T=0,F=0,A=0,L=0,X=0,retSavings=0,rankSavings=0,extra=0;
  const count=()=>eq.length+g.length;
  const add=(a,b)=>({m:a.m^b.m,t:a.t^b.t});
  function solve(){
   assert(eq.length===aux.length,"square system");let E=new Map;params.forEach((v,i)=>E.set(v,{m:1<<i,t:0n}));for(let [v,t] of query)E.set(v,{m:0,t});
   let rows=eq.map(e=>{let a=0,r={m:0,t:e.c?ones:0n};for(let v of e.v){let j=aux.indexOf(v);if(j>=0)a^=1<<j;else{assert(E.has(v),"equation variable");r=add(r,E.get(v))}}return {a,r}});
   for(let j=0;j<aux.length;j++){let i=rows.findIndex((v,k)=>k>=j&&bit(v.a,j));assert(i>=j,"invertible");[rows[i],rows[j]]=[rows[j],rows[i]];for(let k=0;k<rows.length;k++)if(k!==j&&bit(rows[k].a,j)){rows[k].a^=rows[j].a;rows[k].r=add(rows[k].r,rows[j].r)}}
   for(let j=0;j<aux.length;j++){assert(rows[j].a===1<<j,"identity");E.set(aux[j],rows[j].r)}
   return E
  }
  const lit=(E,a)=>{let z=E.get(a>>1);assert(z,"affine literal");return {m:z.m,t:z.t^((a&1)?ones:0n)}};
  const value=(e,u,y)=>par(e.m&u)^Number(e.t>>BigInt(y)&1n);
  function check(){
   let E=solve();assert(rank(map.map(v=>v.m))===params.length,"map injective");
   let ids=[...eq.map(v=>v.id),...g.map(v=>v.id),...deleted,...frozen];assert(ids.length===orig&&new Set(ids).size===orig,"stable ID partition");
   for(let u=0;u<1<<params.length;u++){if(pairs.some(([a,b])=>(bit(u,params.indexOf(a>>1))^(a&1))&&(bit(u,params.indexOf(b>>1))^(b&1))))continue;
    for(let y=0;y<Y;y++){let w=new Map;for(let [id,e] of E)w.set(id,value(e,u,y));let read=a=>{assert(w.has(a>>1),"gate input");return w.get(a>>1)^(a&1)};for(let v of g)w.set(v.id,v.op==="and"?read(v.a)&read(v.b):read(v.a)^read(v.b));let x=map.reduce((a,e,i)=>a|(value(e,u,y)<<i),0);assert(read(out)===Number(!(y&~x)),"selector semantic");semantic++}
   }states++;
  }
  function replaceVar(id,Lit){
   assert(id!==(Lit>>1),"nontrivial alias");for(let e of eq){if(!e.v.includes(id))continue;e.v=e.v.filter(v=>v!==id);if(Lit&1)e.c^=1;let v=Lit>>1;if(v){if(e.v.includes(v))e.v=e.v.filter(a=>a!==v);else e.v.push(v)}}
   for(let v of g){if(v.a>>1===id)v.a=Lit^(v.a&1);if(v.b>>1===id)v.b=Lit^(v.b&1)}if(out>>1===id)out=Lit^(out&1)
  }
  function simplify(){
   for(let i=0;i<g.length;){let v=g[i],{a,b,op}=v,r=null;if(op==="and"){if(a===0||b===0||a===(b^1))r=0;else if(a===1)r=b;else if(b===1||a===b)r=a}else{if(a===b)r=0;else if(a===(b^1))r=1;else if(a>>1===0)r=b^(a&1);else if(b>>1===0)r=a^(b&1)}
    if(r!==null){g.splice(i,1);deleted.add(v.id);replaceVar(v.id,r)}else i++}
   let live=new Set([out>>1]);for(let i=g.length-1;i>=0;i--)if(live.has(g[i].id)){live.add(g[i].a>>1);live.add(g[i].b>>1)}let dead=g.filter(v=>!live.has(v.id));for(let v of dead)deleted.add(v.id);g=g.filter(v=>live.has(v.id));pruned+=dead.length;
  }
  function promote(id,avoid=[]){if(params.includes(id))return;let E=solve(),e=E.get(id);assert(aux.includes(id),"promote aux");let j=params.findIndex((v,k)=>bit(e.m,k)&&!avoid.includes(v)&&!pairs.some(p=>p.some(a=>a>>1===v)));assert(j>=0,"available pivot");let old=params[j];params[j]=id;aux[aux.indexOf(id)]=old;for(let z of map)if(bit(z.m,j)){z.m^=e.m^(1<<j);z.t^=e.t}
   exchanges++;X++;if(e.t!==0n&&e.t!==ones){let constant=Number(e.t&1n),linear=0;for(let i=0;i<D;i++)linear|=(Number(e.t>>BigInt(1<<i)&1n)^constant)<<i;for(let y=0;y<Y;y++)if((par(linear&y)^constant)!==Number(e.t>>BigInt(y)&1n)){nonlinearOffsets++;break}}
  }
  function fix(id,val){
   let j=params.indexOf(id);assert(j>=0,"fix parameter");let readers=eq.filter(e=>e.v.includes(id)).map(e=>e.id),gr=g.filter(v=>v.a>>1===id||v.b>>1===id).map(v=>v.id),before=count();
   params.splice(j,1);for(let e of map){if(bit(e.m,j)&&val)e.t^=ones;e.m=(e.m&((1<<j)-1))|((e.m>>>(j+1))<<j)}
   replaceVar(id,val);for(let k of readers){let j=eq.findIndex(e=>e.id===k);if(j<0)continue;let e=eq[j];assert(e.v.length<=2,"short equation");let a=e.v.find(v=>aux.includes(v));assert(a!==undefined,"aux pivot");let b=e.v.find(v=>v!==a)||0;eq.splice(j,1);aux=aux.filter(v=>v!==a);deleted.add(k);replaceVar(a,2*b+e.c)}
   simplify();assert(readers.concat(gr).every(id=>deleted.has(id)),"reader original IDs");assert(before-count()>=readers.length+gr.length,"reader savings");readerChecks++;return {units:readers.length+gr.length,removed:before-count()}
  }
  check();
  let loops=0;
  while(params.length-pairs.length>0){
   assert(++loops<orig*5+D*5,"termination");let E=solve(),j=g.findIndex(v=>E.has(v.a>>1)&&E.has(v.b>>1));assert(j>=0,"nonaffine output or no minimal gate");let v=g[j],a=lit(E,v.a),b=lit(E,v.b),before=count(),isOut=out>>1===v.id;
   if(v.op==="xor"){g.splice(j,1);aux.push(v.id);let terms=[v.id];for(let l of [v.a,v.b]){let k=l>>1;if(k){if(terms.includes(k))terms=terms.filter(x=>x!==k);else terms.push(k)}}eq.push({id:v.id,v:terms,c:(v.a&1)^(v.b&1)});affine++;A++;assert(count()===before,"affine count");check();continue}
   let free=params.reduce((m,k,i)=>m|(pairs.some(p=>p.some(a=>a>>1===k))?0:1<<i),0),u=a.m&free,w=b.m&free,r=(!u&&!w)?0:(!u||!w||u===w)?1:2;
   if(r===2&&preferPair){assert(!isOut,"rank-two output impossible");let l=[v.a,v.b];if(params.includes(l[1]>>1)&&!params.includes(l[0]>>1))l.reverse();promote(l[0]>>1);promote(l[1]>>1,[l[0]>>1]);pairs.push(l);g=g.filter(e=>e.id!==v.id);deleted.add(v.id);replaceVar(v.id,0);simplify();let n=before-count();assert(n>=2,"rank-two savings");P++;rank2++;rankSavings+=n;extra+=n-2;
   }else if(r>=1){let L=u?v.a:v.b;promote(L>>1);let z=fix(L>>1,L&1),n=before-count();assert(n>=2-Number(isOut),"rank-one savings");R++;rank1++;rankSavings+=n;extra+=n-(2-Number(isOut));if(isOut){L=0;finalOne++;/* output gate deleted */}}
   else if(!a.m&&!b.m){assert(!isOut,"query-only output impossible");query.set(v.id,a.t&b.t);g.splice(j,1);frozen.add(v.id);F++;freeze++;assert(before-count()===1,"frozen count")}
   else{let pp=pairs.find(p=>p.some(l=>bit(a.m|b.m,params.indexOf(l>>1))));assert(pp,"paired gradient");let survivor=pp.find(l=>bit(a.m|b.m,params.indexOf(l>>1))),remove=pp.find(l=>l!==survivor);pairs=pairs.filter(p=>p!==pp);let z=fix(remove>>1,remove&1);assert(z.units>=1&&z.removed>=1,"retire essential");T++;retire++;retSavings+=z.removed;retireExtra+=z.removed-1}
   check();
  }
  assert(params.length===0&&pairs.length===0&&R+P===D&&T===P,"complete dimension ledger");assert(orig===rankSavings+retSavings+F+count(),"exact cost ledger");assert(orig>=2*D-1+P+F,"completed lower floor");
  circuits++;if(D===5)profiles.push({style:C.style,preferPair,gates:orig,R,P,T,F,A,exchanges:X,rankSavings,retSavings,residual:count(),floor:2*D-1+P+F});
 }
 for(let D=2;D<=5;D++)for(let style=0;style<=4;style++)for(let pref of [false,true])run(build(D,style),pref);
 return {circuits,states,semantic,exchanges,rank1,rank2,retire,freeze,affine,readerChecks,retireExtra,nonlinearOffsets,finalOne,pruned,profiles}
}
console.log(JSON.stringify(replay(),null,2));

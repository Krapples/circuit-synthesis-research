// Stable internal AND gates with independent roles across fixed contexts.
// Run: node programmable_gate_roles.js
function run(){
 const N=6,schedule=[];for(let i=1;i<N;i++)for(let j=i;j>0;j--)schedule.push([j-1,j]);
 const prim=N+schedule.length,E=[],wire=Array.from({length:N},(_,i)=>2*i);
 function AND(a,b){let g=2*(prim+E.length);E.push([a,b]);return g;}
 function OR(a,b){return AND(a^1,b^1)^1;}
 function XOR(a,b){return OR(AND(a,b^1),AND(a^1,b));}
 function mux(q,a,b){return OR(AND(q,b),AND(q^1,a));}
 function ok(x,m){if(!x)throw Error(m);}
 for(let i=0;i<schedule.length;i++){let [a,b]=schedule[i],q=2*(N+i),x=wire[a],y=wire[b];wire[a]=mux(q,x,y);wire[b]=mux(q,y,x);}
 let bank=[];for(let i=0;i<N;i+=2)bank.push(AND(wire[i],wire[i+1]));
 let output=bank.reduce((a,b)=>XOR(a,b)),ranks=bank.map(()=>new Map());
 function perms(A){if(!A.length)return [[]];return A.flatMap((v,i)=>perms(A.filter((_,j)=>j!==i)).map(B=>[v,...B]));}
 function addRank(B,m){while(m){let i=m.toString(2).length-1;if(!B.has(i)){B.set(i,m);return;}m^=B.get(i);}}
 let count=0,roleChecks=0,contexts=0;
 for(let pi of perms(Array.from({length:N},(_,i)=>i))){
  let keys=Array.from({length:N},(_,i)=>pi.indexOf(i)),controls=[];
  for(let [a,b] of schedule){let c=+(keys[a]>keys[b]);controls.push(c);if(c)[keys[a],keys[b]]=[keys[b],keys[a]];}
  ok(keys.every((v,i)=>v===i),"sorting");let tables=bank.map(()=>0n);
  for(let x=0;x<1<<N;x++){
   let v=[...Array.from({length:N},(_,i)=>x>>i&1),...controls];
   for(let [a,b] of E)v.push((v[a>>1]^(a&1))&(v[b>>1]^(b&1)));
   let parity=0;
   for(let j=0;j<bank.length;j++){
    let want=(x>>pi[2*j]&1)&(x>>pi[2*j+1]&1),got=v[bank[j]>>1];
    ok(got===want,"pair");parity^=want;if(got)tables[j]|=1n<<BigInt(x);roleChecks++;
   }
   ok((v[output>>1]^(output&1))===parity,"output");count++;
  }
  tables.forEach((v,i)=>addRank(ranks[i],v));contexts++;
 }
 ok(ranks.every(B=>B.size===15),"rank "+ranks.map(x=>x.size));
 let live=new Set(),stack=[output>>1];while(stack.length){let g=stack.pop();if(g<prim||live.has(g))continue;live.add(g);stack.push(...E[g-prim].map(a=>a>>1));}
 ok(bank.every(v=>live.has(v>>1)&&v>>1!==output>>1),"internal gate");
 return {source_bits:N,context_bits:schedule.length,live_and_gates:live.size,bank_gates:bank.length,contexts,output_checks:count,role_checks:roleChecks,role_ranks:ranks.map(B=>B.size)};
}
if(typeof module!=="undefined"&&require.main===module){console.log(JSON.stringify(run(),null,2));console.log("all assertions passed");}

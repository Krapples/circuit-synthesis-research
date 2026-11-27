import sys
from collections import defaultdict
NL=int(sys.argv[2])  # number of left inputs
shapes={}; keys=defaultdict(list)
for line in open(sys.argv[1]):
    t=line.split()
    if t[0]=='S':
        sid=int(t[1]); n=int(t[2]); nc=int(t[3]); NE=int(t[5]); cap=list(map(int,t[7:7+nc]))
        shapes[sid]=(n,nc,NE,cap)
    else: keys[int(t[1])].append((int(t[2]),int(t[3])))
rows=[]; T_all=T_rep=0; bad=0
for sid,(n,nc,NE,cap) in shapes.items():
    stride=[1]*nc
    for c in range(1,nc): stride[c]=stride[c-1]*(cap[c-1]+1)
    M=cap[:n]
    grp=[('L' if i<NL else 'R',M[i]) for i in range(n)]
    orb=defaultdict(list)
    for k,cnt in keys[sid]:
        d=[k//stride[c]%(cap[c]+1) for c in range(nc)]
        sig=(tuple(d[n:]),tuple(sorted((grp[i],d[i]) for i in range(n))))
        orb[sig].append(cnt)
    tot=sum(c for _,c in keys[sid]); rep=sum(v[0] for v in orb.values())
    bad+=sum(1 for v in orb.values() if len(set(v))>1)
    mx=max(c for _,c in keys[sid])
    T_all+=tot*NE*4; T_rep+=rep*NE*4
    rows.append((tot,rep,len(keys[sid]),len(orb),mx,NE,M))
rows.sort(reverse=True)
print("orbits with unequal counts:",bad)
print("tables  rep_tables  ratio  keys orbits  max_key  NE  M")
for tot,rep,nk,no,mx,NE,M in rows[:12]:
    print(f"{tot:11d} {rep:10d} {tot/rep:6.1f} {nk:5d} {no:5d} {mx:9d} {NE:2d} {''.join(map(str,M))}")
print(f"all shapes: {T_all/1e9:.2f} GB raw tables -> {T_rep/1e9:.3f} GB with orbit reps ({T_all/T_rep:.1f}x)")

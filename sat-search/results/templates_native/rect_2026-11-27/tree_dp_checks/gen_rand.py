"""Random 4x5 monotone rect units from random AND/OR circuits that read every input, with `extra` (0-2)
additional reads of earlier wires (inputs or gates); keeps only units whose inputs are all essential.
usage: python gen_rand.py N SEED EXTRA_LIST NL NR   (e.g. 400 21 2,3 4 5)"""
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tree_dp import all_essential
random.seed(int(sys.argv[2])); N=int(sys.argv[1]); nl,nr=int(sys.argv[4]),int(sys.argv[5]); n=nl+nr
EXTRA=[int(x) for x in sys.argv[3].split(",")]
rows=[(1<<u)|(1<<(nl+v)) for u in range(nl) for v in range(nr)]
FULL=(1<<len(rows))-1
out=[]; seen=set()
while len(out)<N:
    w=[sum(((r>>i)&1)<<j for j,r in enumerate(rows)) for i in range(n)]
    pool=list(range(n)); extra=random.choice(EXTRA)
    while len(pool)>1 or extra:
        if extra and random.random()<.3:
            pool.append(random.randrange(len(w))); extra-=1; continue
        if len(pool)<2: pool.append(random.randrange(len(w))); extra-=1; continue
        a=pool.pop(random.randrange(len(pool))); b=pool.pop(random.randrange(len(pool)))
        w.append(w[a]&w[b] if random.random()<.5 else w[a]|w[b]); pool.append(len(w)-1)
    T=w[pool[0]]
    if T in (0,FULL) or T in seen or not all_essential(n,T,w[:n],FULL): continue
    seen.add(T)
    out.append(f"R-{len(out)} {n} 0 1 10 "+",".join(f"{r:x}:{T>>j&1}" for j,r in enumerate(rows)))
print("\n".join(out))

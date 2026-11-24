import random, itertools, sys
sys.argv=['x','1']
exec(open('probe.py').read().split('bad = []')[0])
random.seed(1); bad=0; cnt=0
for n, trials in ((7, 1500), (8, 300)):
    pairs=list(itertools.combinations(range(n),2))
    for _ in range(trials):
        p=random.choice([0.15,0.25,0.4,0.6])
        E=[e for e in pairs if random.random()<p]
        if not E: continue
        t=cover_number(n,E); L=min_leaves(n,E,t); cnt+=1
        ok=((t+1)*(t+2)<=2*L and ((2*L==(t+1)*(t+2))==eq_low(n,E,t)) and L+1<=2**(t+1) and ((L+1==2**(t+1))==eq_high(n,E)))
        if not ok:
            bad+=1; print('FAIL',n,E,t,L,eq_low(n,E,t),eq_high(n,E))
    print(f'n={n}: {cnt} random graphs so far, {bad} failures', flush=True)

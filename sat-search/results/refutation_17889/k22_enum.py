import itertools
n=4  # wires 0,1 points; 2,3 lines
def f(E,x): return any(x[p] and x[2+l] for (p,l) in E)
E=[(0,0),(0,1),(1,0),(1,1)]; E2=[e for e in E if e!=(0,0)]
def ev(gates,out,x):
    w=list(x)
    for op,a,b in gates:
        va=w[a] if a<len(w) else False; vb=w[b] if b<len(w) else False
        w.append((va and vb) if op=='and' else (va or vb))
    return w[out] if out<len(w) else False
X=list(itertools.product([False,True],repeat=4))
C=[('or',0,1),('or',2,3),('and',4,5)]
print("C computes f_E:",all(ev(C,6,x)==f(E,x) for x in X))
found=0
for s in range(3):
    choices=[[(op,a,b) for op in('and','or') for a in range(n+j) for b in range(n+j)] for j in range(s)]
    for gs in itertools.product(*choices):
        for out in range(n+s+1):
            if all(ev(list(gs),out,x)==f(E2,x) for x in X): found+=1
print("size<3 AO2 circuits computing f_{E-e}:",found)

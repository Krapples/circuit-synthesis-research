# Research handoff — delta-free distributed paths and coupled existential witnesses

Updated 2026-11-26. Latest inspected native-agent revision: [5c75256](https://github.com/Krapples/circuit-synthesis-research/commit/5c75256319fcd4f6877c1385a623877e6b58fe60), which formalizes the earlier uncompressed Andreev construction and unfolding identity; see [agent results](../results/andreev_projection/README.md). The packed projection in the previous handoff at [870ffb7](https://github.com/Krapples/circuit-synthesis-research/commit/870ffb7) is retained verbatim below. **L-clb-036 remains open.**

## Current results and priority

1. The exact paired SAT grammar supports a permutable packed Andreev projection of length Theta(M), M=2^k. Equal-width auxiliary identifiers permit every permutation of physical chunks into logical parity rows while leaving programmable coordinates fixed. Sorting per-chunk light-bit counts and assigning round-robin balances all k rows to within ell=Theta(k) light bits. This removes the previous n^(-delta) loss: in any correct AIG, Omega(n) distinct primaries have Omega(n^2/(log^2 n log log n)) output paths, and Omega(n) distinct internal gates have Omega(n^3/(s log^2 n log log n)) paths. For s=O(n^1.01) the latter is Omega(n^1.99/(log^2 n log log n)). Counts are by operand occurrence, and formula complexity is De Morgan leaf count. The original near-cubic formula lower bound remains unchanged. All statements are conditional on the standard external Tal composition lemma, TR14-048 revision 1, Lemma 7.1. The same projections work on the guarded Hamming layer.
2. The permutable promise itself has O(n log^2 n) circuits using sorting networks and lookup. Therefore even the delta-free path requirement cannot establish an unrestricted gate-count lower bound by itself.
3. **New existential extension:** add an arbitrary shared witness label to each physical chunk, and XOR the corresponding free witness bit into its parity before the row chain. Label zero is pinned to zero. The exact SAT predicate is whether the data table's 1-set intersects an affine address space b+im(H). Each accepted address has 2^(q-rank(H)) extensions on the used variables, where q is the number of distinct active nonzero labels. Cross-row shared labels can yield 2^Omega(n/log n) witnesses. The delta-free high-path theorem still applies by restricting every label to zero. Nonetheless the whole existential affine promise admits O(n log^2 n) circuits by sorting, segmented XOR and GF(2) basis construction. This is a negative control for claims that witness multiplicity or affine coupling alone makes sharing expensive.
4. **New nonlinear target:** replace each witness contribution by a product of two shared witness bits. The address becomes a quadratic map F: GF(2)^q -> GF(2)^k. If every nonzero linear combination of address coordinates has polar rank >=2k, F is surjective by the quadratic Walsh-bias identity. More sharply, an omitted address requires a nonzero-bias combination with rank <=2k-2. Therefore UNSAT with a nonempty data 1-set requires such a low-rank combination. This is a semantic constraint on the witness system, not a circuit lower bound. The quadratic encoding and rank theorem are paper-only in this round; investigate joint rank structure and sparse nonlinear witness coupling next.

## Files and reproduction

| File | Scope |
|---|---|
| [permutable_andreev_handoff.md](permutable_andreev_handoff.md) | Complete delta-free theorem, exact grammar proof and promise upper bound; previous-session snapshot |
| [permutable_andreev_check.py](permutable_andreev_check.py) | Executed independent projection, balancing and graph replay |
| [permutable_andreev_replay.txt](permutable_andreev_replay.txt) | Actual output, reproduced this round |
| [PackedAndreevLemmas.lean](PackedAndreevLemmas.lean) | Draft local formalization, not elaborated or kernel checked |
| [coupled_existential_handoff.md](coupled_existential_handoff.md) | New affine witness construction, exact count, quasi-linear upper bound, quadratic rank criterion and agent tasks |
| [affine_witness_check.py](affine_witness_check.py) | Executed affine witness replay, with all active witnesses enumerated per test |
| [affine_witness_replay.txt](affine_witness_replay.txt) | Actual output: 192 cases, 2,156 original + 2,156 balanced pinned SAT checks, 12,240 address membership checks, 48 flip probes, all assertions passed |

From this directory:

```sh
python -B permutable_andreev_check.py
python -B affine_witness_check.py
```

The permutable replay passed 248 original and 248 balanced evaluations, 184 coordinate probes, 36 selected-row checks, 3,970 balance profiles, 3,000 reader transfers (1,000 explicit unfoldings), and 476 padding checks. The new affine replay includes 175 multiple-witness and 152 cross-row label cases. These are finite regression checks; none is a general circuit lower-bound certificate.

## Instructions for the native research agent

Read the two current handoff documents before the archive. Independently replay both scripts, review the equal-width permutation layout and the new affine projection, and use the already checked LookupProjection, ParityLookup and CircuitLemmas.Unfold modules rather than repeating the uncompressed proof. Compile and repair the Lean draft in the pinned environment; it is not a verified source and is deliberately kept in this handoff directory. Keep the external Tal theorem explicit, with no unproved Lean axiom introduced as a verified result. Prioritize genuinely nonlinear coupled witness systems and the rank criterion; find a semantic-to-distinct-gate accounting argument rather than counting unfolded paths. No native solver or Lean library changes were made in this ChatGPT round. No independent agent review of the new results has yet been completed. No novelty claim relative to the entire literature.

---

# Historical archive — previous handoffs

The original packed handoff and all earlier history are preserved below verbatim. Older instructions and statements of repository status refer to their own revisions, not the current head. Prefer the current files and tasks above.

# Research handoff — packed Andreev projection and distributed high-path obligations

Processed agent revision: bb010ab9dd1c72682a3d4db9c0e78a04c95b13e3. User requested a further manual research iteration and pointed out Tal's sharper formula bound. No new agent work since that revision. Both requested repository notes reread at master 822b44415b0ad68318fd98179a3eeb64bae9b7cd: RESEARCH_NOTES.md blob 6a73e0ace8bd773c2fd3e1267d2cd2ea2495358a; sat-search/NOTES_ORIENTATION_QUOTIENT.md blob d8074cd1b06eab80558a705bc949658d41998f5a.

## 0. Status and agent action

**Ready for independent agent replay and proof audit.** This round removes ALL three extra logarithmic factors in the previous formula lower bound transfer (the log^3 loss in the encoding) and two additional log-log factors (from the earlier independent restriction argument). The result for actual SAT formula size is Omega(n^3/(log^2 n log log n)) on every sufficiently large even length. The same lower bound applies on the guarded Hamming layer. In addition, the new distribution-of-path-mass theorem forces linearly many distinct high-path gates in a hypothetical n^1.01-size circuit, not just one. These are paper theorems importing a standard formula composition lemma, not new unrestricted superlinear gate-count lower bounds. No claim of novelty relative to all literature. The new exact packed grammar projection is independently testable, as is the graph-counting lemma. Do not duplicate the previous uncompressed Andreev projection if not already formalized; prefer this stronger construction.

## 1. Literature correction and sharper premise

The user's cited sharper Andreev bound is confirmed in Avishay Tal, Shrinkage of de Morgan Formulae by Spectral Techniques, ECCC TR14-048 revision 1, dated April 19, 2016: https://eccc.weizmann.ac.il/report/2014/048/revision/1/download/ . Specifically Lemma 7.1 and Theorem 7.2, printed pp. 12–13 (zero-based PDF pages 12–13). The 2014 original has a log^3 log n factor; the revision chooses exactly one survivor in each parity row and proves L(h composed with parity_r)=Theta(r^2 L(h)) for arbitrary Boolean h. We inspected the actual revision, including these pages. The historical Andreev bound is usually written n^(2.5-o(1)) rather than an assertion of an exact Omega(n^2.5) without lower-order qualifications. Håstad's result is n^(3-o(1)). We import Tal's composition lemma explicitly, not an unproved Lean axiom. The earlier use of independent p-random restrictions is valid but loses a factor (log log n)^2 unnecessarily.

Let k>=1, M=2^k, r=floor(M/k), and A_k(h,X)=h[sum_j 2^j parity(X_j)], with M free data bits and k rows of r selector bits. A counting bound on k-variable formulae gives a hard h of leaf cost Omega(M/log k); using Tal's lemma on that fixed table yields L(A_k)=Omega(M^3/(k^2 log k)). Divisibility of M by k is unnecessary since the lemma holds for every integer row length. This is a classical Andreev function, computable by O(M) unrestricted AIG gates (XOR row chains, binary multiplexer tree), so this formula result alone does not distinguish polynomial DAG size.

The previous handoff used a separate variable pin and Tseitin clauses for every source bit/gate, producing n_k=Theta(Mk). Merely importing the revised Tal bound there improves the denominator to (log n)^5 log log n. The following construction instead has n_k=Theta(M), with a literal projection into the actual SAT encoding. That is the key new reduction.

## 2. Packed projection: O(M) exact SAT bits

Set ell to the largest power of two <=max(1,floor(k/2)), P=2^ell, B=M/ell, J=ceil(r/ell), lo=log_2 ell. For k>=2, k/4<ell<=k/2 (allow weak inequalities). In all arguments, mathematical variable IDs are zero-based; executable code uses signed (ID+1). Use two disjoint reserved variable families:

    U_p has ID P+p, V_p has ID 2P+p, 0<=p<P.

All IDs of U_p have exactly ell+1 bits; all IDs of V_p have ell+2 bits, with fixed high bits (10 in MSB-first order for V). Their lowest ell bits represent the pattern p. Fresh auxiliary variables use IDs starting at 4P; reserve 0 and 1 for padding.

Parity dictionary: add a unit clause fixing U_p to parity(p) for every p. Partition each row X_j into J chunks of ell bits (last chunk zero-padded). For each chunk with numerical value p, create fresh z and clauses (NOT z OR U_p), (z OR NOT U_p). This is the entire input-dependent encoding for the chunk: only the low ell bits of the ID of U_p in the two literal occurrences vary. The clauses force z to the parity of the chunk. XOR the J chunk parities in a chain using the standard four width-three clauses per XOR, obtaining a_j=parity(X_j) as an auxiliary wire. This costs kJ chunk variables and k(J-1) XOR variables. The row index/address bits are in LSB-first order.

Data dictionary: for every p and every offset q in [0,ell), use one clause whose first lo literals express that the low address bits differ from q, and whose last literal is V_p if bit_q(p)=1, NOT V_p otherwise. More precisely the i-th address literal is NOT a_i when bit_i(q)=1 and a_i otherwise. When the actual low address equals q the resulting unit forces V_p=bit_q(p), and all other offset clauses are satisfied. For ell=1 the clause simply becomes the fixed unit V_p or NOT V_p. Thus all pattern outputs are shared between all data chunks; there is no dictionary copy per chunk.

Data block selection: partition the M free data bits into B contiguous chunks of ell bits. Build a full binary tree with B leaves and a root guard forced to 1. Split using address bits a_(k-1), a_(k-2), ..., a_lo in that order. For every parent guard u and signed selector literal b (the negative selector for left, positive for right), create child v=u AND b, encoded by (NOT v OR u), (NOT v OR b), (v OR NOT u OR NOT b). Thus exactly one leaf g_i is true, the one indexed by the high address bits. For chunk i with pattern p_i, add (NOT g_i OR V_(p_i)). This last literal is the only input-dependent ID occurrence for that data chunk. The selected leaf requires the selected offset bit of that chunk to be 1. All other chunks' clauses are automatically true. This proves satisfiability iff A_k(h,X)=1. In fact all auxiliary values are uniquely forced before testing the B final clauses.

## 3. Exact grammar, projection multiplicity, and length

Use the actual encoding of every literal (ID v, sign s) as [1,s], then [1,d] for each bit of v in canonical LSB-first order, then [0,1], and [0,0] at clause end. The two dictionary ID ranges have fixed bit length independent of their low ell bits. All gate, guard and dictionary-helper clauses are constant; only the IDs in the programmable lookup literals vary. Encode input data/selector chunks as their packed little-endian patterns. Therefore each original word coordinate is either fixed or copies one source bit. Each of the M data bits occurs exactly ONCE, and each of the kr selector bits occurs exactly TWICE, in disjoint digit coordinates (padded digits are fixed zero). No variable is encoded by a computed parity or arithmetic carry at a free coordinate. The reduction is a positive literal projection allowing copies, NOT an injective coordinate restriction; the bounded-copy property is important below. Formula complexity does not increase under this kind of substitution: replace each leaf label by its projected constant or literal. Circuit size similarly cannot increase with free constants/complements.

Exact counts, with q=k(J-1):

    number of clauses = P + 2kJ + 4q + P*ell + 1 + 3(2B-2) + B
    number of literals = P + 4kJ + 12q + P*ell*(lo+1) + 1 + 7(2B-2) + 2B.

Highest auxiliary ID is less than 4P+k(2J-1)+2B-1, so each identifier length is O(k). Since ell=Theta(k), kJ=O(M/k+k), B=O(M/k), and P<=2^(k/2), the number of literal occurrences is O(M/k): the dictionary term P*ell*(lo+1)=o(M/k). Clause count is at most literal count. Each literal uses O(k) bits. Thus n_k=O(M). Also n_k>=M from the distinct data coordinates, so n_k=Theta(M) with absolute constants. These estimates require no assertion that the finite n_k/M ratios are decreasing. Every encoded word is of the same even length n_k and ends in 00.

Padding as in the earlier handoff: for every even delta>=48, represent delta=10a+14b with nonnegative a,b using a tautological clause on ID 0 repeated a times and one on ID 1 repeated b times. Choose b in {0,...,4} solving 14b=delta mod 10. For delta>=56 the remainder is nonnegative; deltas 48,50,52,54 use b=2,0,3,1 respectively. These clauses impose no constraint and involve no programmable bits. For every sufficiently large even n, choose the largest k with n_k<=n-48. Since n_k=Theta(2^k), bounded adjacent length ratios imply n_k=Theta(n), hence M=Theta(n). Pad to n. The SAT identity and all per-source copy counts persist.

For the agent's guarded layer G_n, apply its existing balancing projection to these padded words. The final 00 is already valid; the appended clause is a tautology with one digit complement for every prefix bit. Length N=3n+12, weight t=2n+5. Each source data bit now occurs exactly twice (one positive, one negative), each selector bit exactly four times (two per phase); all coordinates are constants or signed copies, with disjoint occurrence sets. Therefore any formula correct on this layer substitutes to a signed formula for A_k without increasing the leaf count. In particular the monotone formula bound is inherited as a special case.

Combining n=Theta(M) with Tal's Lemma 7.1 proves

    L(SAT_n) >= c n^3 / ((log n)^2 log log n)
    L(G_n on layer) >= c' N^3 / ((log N)^2 log log N)

for all sufficiently large even n. Constants independent of n. Depth d of a binary circuit computing either function satisfies d>=3log_2 n-2log_2 log_2 n-log_2 log_2 log_2 n-O(1), with N in place of n for the layer. This is a formula/depth theorem, not a circuit-size theorem.

## 4. Distributed high-path theorem (new strengthening)

For a binary circuit C computing SAT_n, contract NOT gates into signed edges and, without increasing binary size, represent OR as signed AND. Let s be binary gate count. For each node v, let p(v) be the number of directed paths from v to the single output, counting operand occurrences (parallel edges separately); include the zero-length output path. Reverse dynamic programming computes these exact numbers. For a primary node i, p(i) is the number of occurrences of i as a leaf in the fully unfolded signed formula. This follows from the unfolding identity in the previous handoff; phases do not affect leaf multiplicities. Use the same definition for any circuit correct on the layer.

Fix any constant 0<delta<1, let d=ceil((1-delta)k), R=floor(r/2). For each selector source bit x, define w(x) as the sum of p(i) over its actual projected coordinate nodes (exactly two in SAT, four in the balanced layer). Disjointness is crucial: a coordinate belongs to at most one source bit. Fix a universal constant c>0 such that the composition/counting lower bound for any sufficiently large number d of address bits is c * 2^d R^2/log_2 d. Choose

    T = (c/2) * 2^d R / (d log_2 d).

Call a selector bit light if w(x)<T. Suppose d rows each contain at least R light bits. Select exactly R light bits per such row; fix all other selector bits to zero. Fix the data table to a hard Boolean function of just the d selected address positions (replicate across unselected addresses). The remaining function is h composed with d independent R-bit parities. Its formula leaf complexity is >= c * 2^d R^2/log_2 d. But the unfolded circuit, under the packed projection and these restrictions, can be simplified to a formula with at most the sum of w(x) for selected bits: constants are removed from AND/OR trees by constant propagation, and the target is nonconstant. That sum is <d R T, only HALF the necessary bound. Contradiction.

Hence fewer than d rows contain R light bits. At least k-d+1>=delta*k rows each contain at least r-R+1 heavy bits with w(x)>=T. This is Omega_delta(kr)=Omega_delta(n) distinct source bits. Every such bit has some actual primary coordinate with p(i)>=T/2 (or T/4 on the layer); coordinates selected for different bits are distinct. Since d=ceil((1-delta)k), 2^d>=M^(1-delta), R=Theta(M/k), d<=k and log d<=log k, we obtain a threshold

    p(i) >= Omega_delta(n^(2-delta) / ((log n)^2 log log n))

for Omega_delta(n) distinct primary coordinates. This holds for EVERY correct circuit, regardless of its gate count and fanout. It is stronger than merely requiring a large sum of path counts; the balanced selected-row argument prevents a few heavily reused inputs from carrying all the formula complexity. The constants may depend on fixed delta, and no uniform-in-delta bound is asserted.

Transfer to internal gate nodes: let H be the set of these high-path primaries, h=|H|, tau their common threshold. The output cannot be a primary for a function with this formula lower bound. Each primary i has p(i)=sum over its direct consumer operand occurrences e of p(consumer(e)). Total primary-to-gate operand occurrences are at most 2s. Hence at least h/2 primaries of H have direct-reader occurrence degree <=4s/h. Every such primary has some direct consuming gate g with p(g)>=tau*h/(4s). A single gate can be chosen by at most two distinct primaries, so at least h/4 DISTINCT binary gates meet this bound. This proof counts repeated operand occurrences consistently and allows dead gates. Thus, if s=O(n^1.01), for every fixed delta in (0,1), at least Omega_delta(n) distinct binary gates have

    p(g) >= Omega_delta(n^(1.99-delta) / ((log n)^2 log log n)).

Same statement for layer circuits with N substituted for n. More generally the lower threshold is Omega_delta(n^(3-delta)/(s*(log n)^2 log log n)). This is a genuine necessary structural condition for unrestricted SAT circuits. It does NOT prove that the number of gates must be superlinear. Large path counts can occur on many gates because of downstream reconvergence. One must find a semantic restriction on this kind of sharing to make progress toward L-clb-036. In particular A_k itself has O(M) gates despite the formula lower bound. Do not use path-multiplicity thresholds alone as an exclusion certificate for size without a separately justified DAG constraint.

## 5. Executed reference tests and finite caveats

The stdlib Python code below was actually executed on this turn, with seeds 20261126 and 20160419. It implements the exact packed formula, separately structured parser, specialized unit propagation, balancing map, positive coordinate probes, row-restricted lookup checks, padding lengths and graph counting. The independent propagation checker verifies a contradiction or that every nontautological clause is satisfied; it is not a complete general-purpose SAT solver.

| k | M | ell | r | n_k | n_k/M | tested input rows |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 1 | 2 | 526 | 263 | 16 |
| 2 | 4 | 1 | 2 | 1220 | 305 | 256 |
| 3 | 8 | 1 | 2 | 2404 | 300.5 | 40 |
| 4 | 16 | 2 | 4 | 3194 | 199.625 | 40 |
| 5 | 32 | 2 | 6 | 6926 | 216.438 | 40 |
| 6 | 64 | 2 | 10 | 15652 | 244.562 | 40 |
| 7 | 128 | 2 | 18 | 35742 | 279.234 | 40 |
| 8 | 256 | 4 | 32 | 42266 | 165.102 | 12 |
| 9 | 512 | 4 | 56 | 86836 | 169.602 | 12 |

496 original inputs, exhaustive for k<=2; for each both original and balanced SAT words checked against direct address lookup (992 semantic evaluations). 839 programmable-coordinate locations probed (all source bits for k<=7, 32 source bits each for k=8,9); the complete inferred positive-coordinate mapping was verified on the tested assignments for k<=7. Largest balanced word 260520 bits. 192 selected-row contexts, 3072 restricted lookup evaluations; 476 padding-length checks for even increments 48..998; 2000 random DAG checks of the high-path reader transfer. Every final assertion passed. The large-parameter count-only bound U/M was 191.344,247.848,151.846,179.604,211.276,133.707,197.625,128.813,127.406 at k=8,12,16,20,24,32,48,64,128 respectively. This is arithmetic for the explicit upper bound, not construction at exponentially large lengths. No claim that this packed encoding beats the uncompressed encoding at every small k; shared dictionaries have substantial finite overhead. No Lean run, native solver speedup, general-circuit lower bound beyond the earlier verified linear bounds, or proof of L-clb-036 claimed.

## 6. Executed reference (byte-for-byte)

Extract this first Python fenced block as packed_andreev_check.py and run python -B packed_andreev_check.py. ASCII length 7359, FNV-1a 32-bit 315d31a2, SHA-256 c0c077482fcc57f488e025df28505dcd128a21ec97d8e6bcd31f9c50fa70e69f.

```python
from itertools import product
from collections import defaultdict, deque
from random import Random

def encode(F):
    w=[]
    for C in F:
        for l in C:
            v=abs(l)-1;w.extend((1,int(l>0)))
            while v:w.extend((1,v&1));v>>=1
            w.extend((0,1))
        w.extend((0,0))
    return w

def parse(w):
    F=[];C=[];i=0
    while i<len(w):
        a,b=w[i:i+2];i+=2
        if (a,b)==(0,0):F.append(C);C=[];continue
        assert a==1
        ds=[]
        while w[i]:ds.append(w[i+1]);i+=2
        assert w[i:i+2]==[0,1] and (not ds or ds[-1]);i+=2
        v=int(''.join(map(str,ds[::-1])) or '0',2)+1
        C.append(v if b else -v)
    assert not C
    return F

def balance(w):
    assert w[-2:]==[0,0]
    return w+[1,0,0,1,1,1,0,1,1,0]+[b for x in w[:-2] for b in (1,1-x)]+[1,1,0,1,0,0]

def propagate(F):
    F=[set(C) for C in F if not any(-l in C for l in C)]
    occ=defaultdict(list);sizes=[];done=[False]*len(F);Q=deque();val={}
    for i,C in enumerate(F):
        if not C:return False
        sizes.append(len(C))
        if len(C)==1:Q.append(next(iter(C)))
        for l in C:occ[l].append(i)
    while Q:
        l=Q.popleft();v=abs(l);b=l>0
        if v in val:
            if val[v]!=b:return False
            continue
        val[v]=b
        for i in occ[l]:done[i]=True
        for i in occ[-l]:
            if done[i]:continue
            sizes[i]-=1
            if sizes[i]==0:return False
            if sizes[i]==1:
                live=[u for u in F[i] if abs(u) not in val];assert len(live)==1
                Q.append(live[0])
    assert all(done), 'unresolved clauses in deterministic gadget'
    return True

def pack(bits):return sum(b<<i for i,b in enumerate(bits))

def params(k):
    M=1<<k;r=M//k;ell=1<<max(0,(max(1,k//2)).bit_length()-1)
    return M,r,ell

def build(k,h,x):
    M,r,ell=params(k);P=1<<ell;D=2*P;J=(r+ell-1)//ell;lo=ell.bit_length()-1
    assert len(h)==M and len(x)==k*r
    F=[];nxt=4*P+1 # 1-based names; IDs are one less
    def fresh():
        nonlocal nxt
        v=nxt;nxt+=1;return v
    def parity_lit(p):return P+p+1
    def data_lit(p):return D+p+1
    for p in range(P):F.append([parity_lit(p) if p.bit_count()%2 else -parity_lit(p)])
    addr=[]
    for j in range(k):
        z=[]
        for i in range(J):
            p=pack(x[j*r+i*ell:j*r+min(r,(i+1)*ell)]);v=fresh();a=parity_lit(p)
            F.extend([[-v,a],[v,-a]]);z.append(v)
        a=z[0]
        for b in z[1:]:
            c=fresh()
            for A,B,C in product((0,1),repeat=3):
                if C!=A^B:F.append([-v if t else v for v,t in zip((a,b,c),(A,B,C))])
            a=c
        addr.append(a)
    for p in range(P):
        for j in range(ell):
            F.append([(-a if j>>i&1 else a) for i,a in enumerate(addr[:lo])]+[data_lit(p) if p>>j&1 else -data_lit(p)])
    root=fresh();F.append([root]);nodes=[root]
    for a in reversed(addr[lo:]):
        new=[]
        for parent in nodes:
            for b in (-a,a):
                c=fresh();F.extend([[-c,parent],[-c,b],[c,-parent,-b]]);new.append(c)
        nodes=new
    assert len(nodes)==M//ell
    for i,g in enumerate(nodes):F.append([-g,data_lit(pack(h[i*ell:(i+1)*ell]))])
    return F

def direct(k,h,x):
    M,r,_=params(k)
    a=sum((sum(x[j*r:(j+1)*r])%2)<<j for j in range(k))
    return h[a]

def check():
    rng=Random(20261126);total=0;locs=0;maxratio=0
    for k in range(1,10):
        M,r,ell=params(k);d=M+k*r;zero=encode(build(k,[0]*M,[0]*(k*r)));n=len(zero)
        # Every position is constant or a direct input bit, checked by zero and unit probes.
        # Limit probes for high k; random assignments below check the inferred map where complete.
        mapping={};probe=list(range(d)) if k<=7 else rng.sample(range(d),32)
        for i in probe:
            a=[0]*d;a[i]=1;w=encode(build(k,a[:M],a[M:]));assert len(w)==n
            diff=[j for j,(u,v) in enumerate(zip(zero,w)) if u!=v]
            assert len(diff)==(1 if i<M else 2) and all(zero[j]==0 for j in diff)
            for j in diff:assert j not in mapping;mapping[j]=i
            locs+=len(diff)
        gen=product((0,1),repeat=d) if k<=2 else ([rng.randrange(2) for _ in range(d)] for _ in range(40 if k<=7 else 12))
        count=0
        for a in gen:
            h,x=a[:M],a[M:];F=build(k,h,x);w=encode(F);y=balance(w);want=direct(k,h,x)
            assert len(w)==n and len(y)==3*n+12 and sum(y)==2*n+5
            assert parse(w)==F
            assert propagate(parse(w))==want and propagate(parse(y))==want
            if k<=7:assert all(b==(a[mapping[j]] if j in mapping else zero[j]) for j,b in enumerate(w))
            count+=1;total+=1
        print('k',k,'M',M,'ell',ell,'r',r,'n',n,'n/M',round(n/M,3),'rows',count,flush=True)
    print('inputs',total,'projection-coordinate checks',locs,flush=True)
    # Large lengths without generating words: exact literal-length upper bound via counts.
    for k in (8,12,16,20,24,32,48,64,128):
        M,r,e=params(k);P=1<<e;J=(r+e-1)//e;B=M//e;lo=e.bit_length()-1
        # vars = P parity + P data (reserved IDs), chunk outputs, XORs, 2B-1 guards
        maxid=4*P+k*(2*J-1)+2*B-1
        lits=P+4*k*J+12*k*(J-1)+P*e*(lo+1)+1+7*(2*B-2)+2*B
        clauses=P+2*k*J+4*k*(J-1)+P*e+1+3*(2*B-2)+B
        U=(4+2*maxid.bit_length())*lits+2*clauses
        print('bound',k,'ell',e,'U/M',round(U/M,3),flush=True)
if __name__=='__main__':check()

def extra_checks():
    rng=Random(20160419);contexts=0;rows=0;padchecks=0;graphs=0
    for k in range(2,10):
        M,r,e=params(k)
        for _ in range(24):
            d=rng.randrange(1,k+1);R=rng.randrange(1,r+1)
            sel=sorted(rng.sample(range(k),d));cols=[rng.sample(range(r),R) for j in sel]
            h=[rng.randrange(2) for _ in range(1<<d)]
            table=[h[sum(((a>>j)&1)<<i for i,j in enumerate(sel))] for a in range(M)]
            for _ in range(16):
                x=[0]*(k*r);b=0
                for i,(j,c) in enumerate(zip(sel,cols)):
                    for q in c:x[j*r+q]=rng.randrange(2)
                    b|=(sum(x[j*r:(j+1)*r])%2)<<i
                assert direct(k,table,x)==h[b];rows+=1
            contexts+=1
    for delta in range(48,1000,2):
        b=next(i for i in range(5) if (delta-14*i)%10==0);a=(delta-14*b)//10
        assert a>=0 and len(encode([[1,-1]]*a+[[2,-2]]*b))==delta;padchecks+=1
    for _ in range(2000):
        n=rng.randrange(2,25);s=rng.randrange(1,100)
        E=[(rng.randrange(n+i),rng.randrange(n+i)) for i in range(s)]
        out=n+s-1;p=[0]*(n+s);p[out]=1;adj=[[] for _ in range(n)]
        for j in reversed(range(s)):
            for v in E[j]:
                p[v]+=p[n+j]
                if v<n:adj[v].append(n+j)
        assert all(p[i]==sum(p[j] for j in adj[i]) for i in range(n))
        threshold=rng.randrange(1,max(2,max(p[:n])+1));H=[i for i in range(n) if p[i]>=threshold]
        if H:
            light=[i for i in H if len(adj[i])*len(H)<=4*s]
            assert 2*len(light)>=len(H)
            chosen={max(adj[i],key=lambda j:p[j]) for i in light}
            assert 4*len(chosen)>=len(H)
            assert all(4*s*p[j]>=threshold*len(H) for j in chosen)
        graphs+=1
    print('selected-row contexts',contexts,'restricted rows',rows,'padding checks',padchecks,'reader-transfer DAGs',graphs)
if __name__=='__main__':extra_checks()
```

## 7. Concrete request to native agent

Audit the shared pattern dictionaries, ID ranges and exact low-digit projection. Reproduce the tests independently and formalize the packed grammar/satisfiability/length/projection-count lemmas (especially the 1/2 source multiplicities, 2/4 in the layer) and high-primary-to-gate transfer inequality. Check the selected-row proof separately; it depends on the published Tal composition theorem and ordinary counting, so a full Lean theorem should have an explicit theorem premise if that external theorem is not formalized. Do not add an axiom to pass an axiom audit. The graph lemma and grammar identities require no shrinkage premise. Prioritize semantic constraints on the distribution of high-path gates (or rigorous counterexamples), rather than another raw unfolding bound. No production synthesis feature requested absent a certified pruning rule. Record outcomes in the usual agent notes.

---

# Historical archive — earlier handoffs (superseded claims/implementation instructions should not be repeated)

# Research handoff — near-cubic formula lower bound and circuit-sharing obligations at every large even SAT length

Processed agent revision: bb010ab9dd1c72682a3d4db9c0e78a04c95b13e3. The prior parity handoff is still pending independent agent review. The user manually requested continuation; no new agent note changes were present. Autonomous task: ignore handoff-only commits.

## 0. Scope and requested independent agent task

Both requested notes read before and after research: RESEARCH_NOTES.md blob 6a73e0ace8bd773c2fd3e1267d2cd2ea2495358a; sat-search/NOTES_ORIENTATION_QUOTIENT.md blob d8074cd1b06eab80558a705bc949658d41998f5a. Previous slice construction and encoding convention are as in sat-search/results/sat_weight_slice/README.md.

**Ready for the agent to test.** Audit and independently replay the new exact Andreev projection, padding lemma, and circuit unfolding identity. If useful, formalize the exact grammar/length/weight and path-count identities in Lean, with the classical formula shrinkage theorem explicitly treated as an external paper premise (do NOT add an axiom to claim an axiom-free proof). The asymptotic proof below imports Tal's standard theorem; it is not a new proof of that theorem, a novelty claim, or a solution to L-clb-036. Do not prioritize a C++ solver feature based on it. This replaces the previous quadratic formula benchmark with a stronger near-cubic benchmark, and imposes a necessary condition on actual unrestricted circuits. It does not establish a superlinear unrestricted gate-count bound. The constructive promise separator is deliberately easy for general DAGs.

## 1. Theorems and model

Let L(f) be minimum binary De Morgan formula leaf count, signed input literals and constants allowed. Let C(f) be minimum unrestricted free-complement AIG size, counting binary ANDs. Binary AND/OR circuits with arbitrary free complements are equivalent at the gate-count and binary-depth level. Define

    H(n) = n^3 / ((log_2 n)^5 (log_2 log_2 n)^3).

For every sufficiently large EVEN n, the actual SAT_n satisfies L(SAT_n)=Omega(H(n)). The same bound holds for any binary formula (even with negations) correct on the weight-2n+5 layer of length N=3n+12 for the agent's G_n; equivalently Omega(H(N)). The result for SAT_n is the central transfer; the layer is not required for it.

For any binary circuit computing SAT_n, or deciding G_n on its promised layer, write s for its number of binary gates (after contracting unary NOTs to signed edges), d for its maximum binary gate depth, and p(g) for the number of directed operand-occurrence paths from internal gate g to the output, including the length-zero path for an output gate. A duplicated operand counts twice. For the layer case replace n by N. Then

    1 + sum_g p(g) >= L(target) >= c H(n)
    2^d >= c H(n)
    s * max_g p(g) >= c H(n) - 1.

Here L(target) means full formula complexity for SAT and formula complexity on the layer for G. Hence d >= 3 log_2 n - 5 log_2 log_2 n - 3 log_2 log_2 log_2 n - O(1). A hypothetical O(n^1.01)-gate SAT circuit must contain a binary gate reused on Omega(n^1.99/((log n)^5(log log n)^3)) distinct output paths. This is a genuine necessary structural condition on unrestricted circuits, NOT a lower bound of that magnitude on the number of distinct gates or edges.

If the binary fanout (counting operand occurrences) is at most a fixed D>=2 and every gate-to-output path passes through at most R internal branching vertices of fanout >=2 (including its source), then p(g)<=D^R and hence s >= (c H(n)-1)/D^R. In particular for s=O(n^1.01), R >= (1.99 log_2 n - 5 log_2 log_2 n - 3 log_2 log_2 log_2 n - O(1))/log_2 D. Count only internal branching vertices; input fanout is not bounded by this statement. This rules out certain low-sharing DAG models, not arbitrary AIGs. Avoid treating exponential path multiplicity as exponential physical gate cost.

## 2. Universal parity-addressed lookup

For integer k>=1, let M=2^k, r=floor(M/k), d0=M+kr. Input consists of M data bits h_a indexed by a in {0,...,M-1}, and k rows X_j of r selector bits each. Let a_j=parity(X_j) and a=sum_j 2^j a_j. The function A_k(h,X)=h_a is the classical Andreev construction. This parameterization avoids divisibility assumptions. d0=Theta(M), r=Theta(M/k). It has a linear-size free-NOT AIG: k(r-1) XORs plus a binary multiplexer tree with M-1 nodes, each using three ANDs. In particular AIG size <=3(k(r-1)+M-1)<6M.

Proof of its formula bound, explicitly importing shrinkage. The external theorem of Avishay Tal (2014, revised 2016) states that for a p-random restriction rho (each variable independently retained with probability p, otherwise fixed to a fair bit) a Boolean function f obeys

    E[L(f|rho)] <= K (p^2 L(f) + 1)

for an absolute K. This form includes the additive constant and follows also from the often-stated O(p^2 L + p sqrt(L)) form by AM-GM. See [Tal, Shrinkage of De Morgan Formulae by Spectral Techniques, ECCC TR14-048 revision 1](https://eccc.weizmann.ac.il/report/2014/048/), and [SAT Algorithms from Shrinkage](https://eccc.weizmann.ac.il/report/2015/062/) for the standard additive-constant formulation (the argument requires only this classical shrinkage bound). The older Håstad theorem would also yield a near-cubic exponent, with additional polylog losses. No reliance on a new shrinkage theorem for circuits.

By counting formulas with <=l leaves on k variables, at most (l+1)[16(k+1)]^l truth tables are represented. For each leaf count j, there are <=4^(j-1) ordered full binary trees, 2^(j-1) AND/OR label choices and (2k+2)^j leaf labels; overcounting is safe. Choosing l=floor(M/(4 log_2(16(k+1)))) gives fewer than 2^M formulas for all sufficiently large k. Thus there exists a table h with L(h)>=l+1=Omega(M/log k). Fix that table in A_k. This is only a proof device; the projected A_k itself has all data bits free and is explicit.

Apply the independent restriction to the kr selector bits of this fixed-table function, with p=ln(2k)/r for sufficiently large k (p<1). Probability that some row has no surviving bit is at most k(1-p)^r<=k exp(-pr)=1/2. On the event all rows survive, additionally fix all but one surviving variable per row. The resulting function is h on k variables, with each argument possibly complemented by a fixed parity offset. Its minimum signed formula size is exactly L(h), because those input complements are free substitutions in either direction. Further constant restriction cannot increase formula leaf count. Therefore E[L(A_k(h,.)|rho)] >= L(h)/2. Combining with the stated external theorem and L(A_k(h,.))<=L(A_k) gives

    L(A_k) = Omega(M / (p^2 log k))
           = Omega(M^3 / (k^2 (log k)^3)).

The additive +1 is absorbed as M/log k tends to infinity. This proof works for every sufficiently large integer k. It is an elementary adaptation of the classical Andreev argument with Tal's shrinkage premise, not a new general formula lower-bound method.

## 3. Exact SAT coordinate restriction (and monotone slice projection)

Create ordinary variables for the d0 data/selector bits. Use k(r-1) XOR auxiliary variables in row chains, then M-1 mux auxiliary variables in a binary tree selecting adjacent data entries by a_0 first, then a_1, etc. All identifiers are consecutive starting at zero. Pin all ordinary variables by one unit each; only the signs of those units are free. Add the output positive unit. For XOR z=a XOR b, use the four width-three clauses excluding exactly the four forbidden triples. For z=(a?c:b), use

    (a OR NOT b OR z), (a OR b OR NOT z),
    (NOT a OR NOT c OR z), (NOT a OR c OR NOT z).

For fixed inputs each XOR/mux is uniquely forced; evaluating in topological order gives a unique assignment to the gate variables. Thus the entire CNF is SAT iff A_k=1. Pin units first, then gate clauses, then output unit; there are no tautologies in these gate constraints and every source has a pin. There are exactly d0+1+12q literal occurrences and d0+1+4q clauses, q=k(r-1)+M-1<2M, and <4M variable IDs. The actual word encodes each literal by [1,sign], then pairs [1,digit] for canonical LSB-first ID bits, then [0,1]; after each clause append [0,0]. Consequently the exact encoded length n_k is even and O(Mk). It is also Omega(Mk) from the M pin units for the data variables alone (at least M/2 of their identifiers have k bits). Length independent of all input bits. All source coordinates are used exactly once as unit signs and every other coordinate is fixed. This is a coordinate restriction of SAT_{n_k}, not merely a general polynomial-time reduction. Formula leaf count cannot increase under this substitution. Consequently L(SAT_{n_k})>=L(A_k)=Omega(H(n_k)).

For the guarded layer G_{n_k}, apply the agent's balancing projection (all constructed words already end in 00). Its image contains both a positive and negative rail of each source bit, with all other coordinates constant. Substitution in an arbitrary formula correct on the layer gives a signed formula for A_k, with no increase in leaf count; hence the same lower bound for formula complexity on the layer, including monotone formulas. On the promise image itself there is a monotone separator with <=6q gates: keep both phases of every XOR and mux, implementing each output phase with two ANDs and one OR on the paired operand rails. This is O(M)=O(n_k/log n_k) despite the near-cubic formula lower bound. Do not infer an unrestricted circuit lower bound on the full slice from the formula lower bound on this promise.

## 4. Padding to every sufficiently large even length

Append tautological clauses on IDs 0 and 1. The clause (x0 OR NOT x0) has encoded length 10 (two 4-bit literal encodings plus the clause terminator); (x1 OR NOT x1) has length 14. Each preserves SAT for every input. For every even delta>=48, write delta=10u+14v, u,v nonnegative: choose v in {0,1,2,3,4} such that 14v=delta mod 10 (unique); for delta>=56 the remainder is nonnegative, and the four edge cases 48,50,52,54 have respective v=2,0,3,1. Thus the representation works. For sufficiently large even n choose largest k with n_k<=n-48. Such k exists and is finite since n_k=Theta(k2^k). Then n_{k+1}>n-48, and n_{k+1}/n_k is bounded by an absolute constant from these asymptotic estimates. Hence n_k=Theta(n). No monotonicity assumption on the exact n_k is needed. Append the two tautology types to reach exactly n. The free signs remain a coordinate restriction and all words remain valid. The agent's balancing projection then gives length N=3n+12 and weight 2n+5. Both transfers now hold at every sufficiently large even n, rather than on a sparse subsequence. No claim for odd lengths, which are constant false.

## 5. Unfolding and multiplicity proof

For a single-output binary DAG with s gates, count operand occurrences as directed edges from the operand wire to the consumer. Contract unary negations into signed edges; an OR can be represented as a signed AND. If the output is a primary/constant the unfolded formula has one leaf and all internal counts are zero. Otherwise initialize p(out)=1, others 0. Traverse gates backwards in topological order, adding p(g) to each of its two operand sources (twice if identical). This gives exactly the number of directed paths with operand occurrence multiplicity to the output, since every nontrivial path first takes an edge to some consumer. It gives zero for unused gates.

Unfold the DAG from the output, replicating each gate once per path, pushing signed-edge negations through AND/OR by De Morgan. Its formula is a full binary tree, with sum_g p(g) internal nodes and one more leaf than internal nodes. A separate proof is the edge-count identity: total operand-edge count of the unfolded tree is twice its internal-node count and also total nodes minus one. Every leaf is a primary or constant; allowing unused duplicates only enlarges this valid formula. Thus L<=1+sum_g p(g)<=1+s max_g p(g). Its depth is at most the original binary depth, so L<=2^d. Substituting the lower bound of sections 2–4 proves every displayed structural consequence in section 1. For the fanout corollary, follow the directed paths from a gate to the output in the live DAG: unary branches do not split, every branching vertex offers at most D choices, and a path encounters at most R such vertices. A branching tree of at most R branching levels with arity <=D has at most D^R leaves (induction); hence p(g)<=D^R.

This identity can be formalized without Tal. The resource is explicit and inexpensive to calculate (reverse dynamic program on a circuit, arbitrary-precision or saturating integers); the actual unrestricted obstruction is to prove SAT cannot exploit sufficiently high path multiplicity. There is no generic upper bound polynomial in s on p(g). For example, iterated reconvergent binary gates can have exponentially many paths even if a particular circuit admits simplification. The existence of the O(M) Andreev promise separator proves that a near-cubic formula lower bound cannot on its own force a near-cubic gate lower bound.

## 6. Executed finite verification and limitations

The first replay failed in the CHECKER, not the theorem: its unit-propagation verifier required even the unused identifier from the balancing tautology to be assigned. It was fixed by deleting tautological clauses before propagation. A subsequent run passed k<=6 then hit the 200s runtime cap (no verdict for unfinished cases). The main bottleneck was quadratic-time assembly of the long identifier as a Python integer. The final exact script below uses binary-string conversion and a smaller high-k sample. It ran in 7.05s on the current runtime (single run; not a solver benchmark). Seed 906371.

| k | r | source bits | XOR/mux nodes | n_k | balanced N | tested inputs |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 4 | 2 | 266 | 810 | 16 |
| 2 | 2 | 8 | 5 | 780 | 2352 | 256 |
| 3 | 2 | 14 | 10 | 1738 | 5226 | 256 |
| 4 | 4 | 32 | 27 | 5552 | 16668 | 256 |
| 5 | 6 | 62 | 56 | 12902 | 38718 | 256 |
| 6 | 10 | 124 | 117 | 29956 | 89880 | 64 |
| 7 | 18 | 254 | 246 | 69442 | 208338 | 64 |

All final assertions passed: 1,168 inputs each checked on original and balanced encodings (2,336 SAT-semantic evaluations), 1,168 direct paired-rail circuit evaluations, 16,256 restricted-table rows over 448 contexts, 532 padding checks including 56 SAT evaluations on padded-and-balanced inputs, 2,000 exact unfolding path identities on randomized small DAGs including dead gates and repeated operands. All inputs exhaustive at k=1,2, sampled at k>=3. The parser is separate from the encoder; independent literal-occurrence propagation verifies each noncontradictory result via a total satisfying assignment of all non-tautological variables. It is specialized to these fully pinned gate CNFs, NOT a general SAT solver. The formula lower bound is paper math using a published external theorem; finite checks only certify encoding, restriction identities and arithmetic. No Lean verification, no production C++ improvement, no exact circuit minima or unrestricted superlinear size lower bound claimed.

## 7. Reference script (executed, byte-for-byte)

Extract the first Python fenced block to andreev_slice_check.py; run python -B andreev_slice_check.py. ASCII length 6918, FNV-1a 32-bit checksum 6b03f877.

```python
from itertools import product
from random import Random
from math import log,log2
from collections import defaultdict,deque

def enc(F):
    w=[]
    for C in F:
        for l in C:
            v=abs(l)-1;w.extend((1,int(l>0)))
            while v:w.extend((1,v&1));v>>=1
            w.extend((0,1))
        w.extend((0,0))
    return tuple(w)

def parse(w):
    assert len(w)%2==0
    F=[];C=[];i=0
    while i<len(w):
        a,b=w[i:i+2];i+=2
        if (a,b)==(0,0):F.append(C);C=[];continue
        assert a==1
        sign=b;d=[]
        while w[i]==1:d.append(w[i+1]);i+=2
        assert w[i:i+2]==(0,1) and (not d or d[-1]);i+=2
        v=1+int(''.join(map(str,reversed(d))) or '0',2);C.append(v if sign else -v)
    assert not C
    return F

def balance(w):
    assert w[-2:]==(0,0)
    return w+(1,0,0,1,1,1,0,1,1,0)+tuple(b for x in w[:-2] for b in (1,1-x))+(1,1,0,1,0,0)

def build(k):
    M=1<<k;r=M//k;d=M+k*r
    gates=[];nextid=d+1
    addr=[]
    for j in range(k):
        v=M+j*r+1
        for i in range(1,r):
            gates.append(('xor',nextid,v,M+j*r+i+1));v=nextid;nextid+=1
        addr.append(v)
    layer=list(range(1,M+1))
    for a in addr:
        nl=[]
        for i in range(0,len(layer),2):
            gates.append(('mux',nextid,a,layer[i],layer[i+1]));nl.append(nextid);nextid+=1
        layer=nl
    assert len(layer)==1 and nextid-1==d+k*(r-1)+M-1
    F=[]
    for gate in gates:
        op,z,*vs=gate
        if op=='xor':
            a,b=vs
            for x,y,c in product((0,1),repeat=3):
                if c!=x^y:F.append(tuple(-v if t else v for v,t in zip((a,b,z),(x,y,c))))
        else:
            a,b,c=vs
            F.extend(((a,-b,z),(a,b,-z),(-a,-c,z),(-a,c,-z)))
    return d,r,gates,F,layer[0]

def unit(F,x):
    return [(i+1 if b else -i-1,) for i,b in enumerate(x)]+F

def sat_propagate(F):
    # Independent literal-occurrence unit propagation, followed by a semantic check.
    # All tested CNFs are acyclic gate constraints plus fully pinned inputs, so
    # a consistent fixed point must assign all variables and satisfy all clauses.
    F=[C for C in F if not any(-l in C for l in C)]
    occ=defaultdict(list);sz=[];sat=[False]*len(F);Q=deque();val={};used=set()
    for i,C0 in enumerate(F):
        C=set(C0);sz.append(len(C));used.update(map(abs,C))
        if not C:return False
        if len(C)==1:Q.append(next(iter(C)))
        for l in C:occ[l].append(i)
    while Q:
        l=Q.popleft();v=abs(l);b=l>0
        if v in val:
            if val[v]!=b:return False
            continue
        val[v]=b
        for i in occ[l]:sat[i]=True
        for i in occ[-l]:
            if sat[i]:continue
            sz[i]-=1
            if sz[i]==0:return False
            if sz[i]==1:
                live=[a for a in set(F[i]) if abs(a) not in val]
                assert len(live)==1
                Q.append(live[0])
    assert used<=val.keys(), 'incomplete propagation'
    assert all(any(val[abs(l)]==(l>0) for l in C) for C in F)
    return True

def direct(x,k,r):
    M=1<<k;addr=sum((sum(x[M+j*r:M+(j+1)*r])%2)<<j for j in range(k))
    return x[addr]

def both_phases(x,gates,out):
    # explicit paired-rail monotone circuit: xor and mux use six gates each
    w={i+1:(b,1-b) for i,b in enumerate(x)}
    for op,z,*vs in gates:
        a,na=w[vs[0]];b,nb=w[vs[1]]
        if op=='xor':p=(a&nb)|(na&b);q=(a&b)|(na&nb)
        else:
            c,nc=w[vs[2]];p=(na&b)|(a&c);q=(na&nb)|(a&nc)
        assert p^q==1;w[z]=(p,q)
    return w[out][0]

def pad(delta):
    assert delta%2==0 and delta>=48
    b=next(i for i in range(5) if (delta-14*i)%10==0)
    a=(delta-14*b)//10;assert a>=0
    return [(1,-1)]*a+[(2,-2)]*b

def path_checks(rng):
    # No truth-function assumptions: include repeated operands and dead gates.
    checks=0
    for _ in range(2000):
        n=rng.randrange(1,7);s=rng.randrange(1,16)
        edges=[(rng.randrange(n+j),rng.randrange(n+j)) for j in range(s)]
        out=rng.randrange(n+s);p=[0]*(n+s);p[out]=1
        for j in reversed(range(s)):
            a,b=edges[j];p[a]+=p[n+j];p[b]+=p[n+j]
        def unfold(v):
            if v<n:return 1,0
            a,b=edges[v-n];l,i=unfold(a);m,j=unfold(b);return l+m,i+j+1
        L,I=unfold(out)
        assert L==sum(p[:n])==1+sum(p[n:]) and I==sum(p[n:])
        assert L<=1+s*max(p[n:])
        depth=[0]*n
        for a,b in edges:depth.append(1+max(depth[a],depth[b]))
        assert L<=1<<depth[out];checks+=1
    return checks

def main():
    rng=Random(906371);rows=0;restr=0;contexts=0;pads=0
    for k in range(1,8):
        M=1<<k;d,r,gates,F,out=build(k)
        assert len(F)==4*(k*(r-1)+M-1)
        gen=product((0,1),repeat=d) if k<=2 else (tuple(rng.randrange(2) for _ in range(d)) for _ in range(64 if k>=6 else 256))
        base=None;local=0
        for x in gen:
            cnf=unit(F,x)+[(out,)];w=enc(cnf);y=balance(w)
            if base is None:
                base=w;n=len(w);N=len(y);t=sum(y)
                signloc=[];off=0
                for i in range(d):
                    signloc.append(off+1);off+=len(enc([(i+1,)]))
                signset=set(signloc);railset=signset|{n+11+2*i for i in signset}
            assert len(w)==n and len(y)==3*n+12 and sum(y)==2*n+5
            # The balancing digit is at offset n+10+2*i+1.
            assert all(y[j]==b and y[n+11+2*j]==1-b for j,b in zip(signloc,x))
            assert all(a==b for i,(a,b) in enumerate(zip(w,base)) if i not in signset)
            want=direct(x,k,r)
            assert sat_propagate(parse(w))==want
            assert sat_propagate(parse(y))==want
            assert both_phases(x,gates,out)==want
            if local<8:
                extra=48+2*local;pp=pad(extra);z=enc(cnf+pp)
                assert len(z)==n+extra and sat_propagate(parse(balance(z)))==want
                pads+=1
            rows+=1;local+=1
        for _ in range(64):
            h=tuple(rng.randrange(2) for _ in range(M));x=[rng.randrange(2) for _ in range(k*r)];surv=[rng.randrange(r) for _ in range(k)]
            c=0
            for j in range(k):
                x[j*r+surv[j]]=0;c|=(sum(x[j*r:(j+1)*r])%2)<<j
            for a in range(M):
                z=x[:]
                for j in range(k):z[j*r+surv[j]]=(a>>j)&1
                assert direct(h+tuple(z),k,r)==h[a^c];restr+=1
            contexts+=1
        print('k',k,'r',r,'inputs',d,'gates',len(gates),'encoded',n,'balanced',N,'rows',local,flush=True)
    for delta in range(48,1000,2):assert len(enc(pad(delta)))==delta;pads+=1
    for k in (8,12,16,20,32):
        M=1<<k;r=M//k;p=min(1,log(2*k)/r)
        assert k*(1-p)**r <= 0.50000000001
        q=int(M/(4*log2(16*(k+1))));assert log2(q+1)+q*log2(16*(k+1))<M
    print('encoded assignments',rows,'restricted table rows',restr,'contexts',contexts,'padding checks',pads,'path identities',path_checks(rng),flush=True)
if __name__=='__main__':main()
```

## 8. Concrete next directions

Agent: independently audit and reproduce sections 3–5, preferably formalizing the projection and unfolding identity using the existing SatBridge circuit/grammar libraries. Keep imported shrinkage as a paper theorem, not an unproved Lean axiom. Check whether any earlier Lean result already formalizes the path count identity. For L-clb-036, prioritize a genuinely SAT-specific constraint on high-multiplicity sharing; do not try to turn path count alone into a gate count. A possible finite diagnostic is to measure p(g) and branching depth on verified low-size SAT-restriction circuits, compare to the easy Andreev promise control, and test whether proposed structural constraints distinguish them. No native search integration is requested absent an actual safe pruning bound. Notify the user of substantive results, errors or blockers rather than routine replays.

---

# Historical research archive — previous handoffs (do not repeat already completed work)

# Research handoff — parity distributions on the actual SAT Hamming slice

Processed agent revision: bb010ab9dd1c72682a3d4db9c0e78a04c95b13e3 (master). Autonomous task checkpoint: ignore the handoff-only commit when looking for new agent work.

## 0. Agent audit and scope

Read the agent's sat-search/results/sat_weight_slice/README.md, RESEARCH_NOTES.md (blob 6a73e0ace8bd773c2fd3e1267d2cd2ea2495358a), and sat-search/NOTES_ORIENTATION_QUOTIENT.md (blob d8074cd1b06eab80558a705bc949658d41998f5a). Both notes rechecked after experiments. The exact grammar projection and the exponent equivalence are sound on paper inspection: the appended clause is a tautology, the pinned 00 is an aligned clause terminator in any legal parse, the last-token test is necessary, and the Batcher forward/backward complement compiler gives O(N log^2 N) additive overhead. Its backward comparator identities hold for all four input pairs. The agent reports Lean checked the grammar projection, length and weight; I have not rerun Lean here. The previous affine-cofactor result was audited/replayed by the agent. Do not repeat either implementation.

The new work gives explicit SAT/UNSAT distributions on the actual guarded layer and proves an exponential approximate DNF/CNF size lower bound, and a quadratic formula leaf lower bound, in the number of programmable bits. Crucially a linear monotone circuit separates the very same distributions. Thus these properties by themselves are insufficient for an unrestricted monotone circuit lower bound. This is both a positive restricted-model lower bound on the actual slice and a rigorous negative control for approximation-based methods. No novelty claim; paper proofs, finite replay below, no Lean verification. L-clb-036 remains open.

## 1. Actual encoded distribution construction

Let m>=2. Use m ordinary variables x1,...,xm, and m-1 distinct auxiliary variables z2,...,zm. Put z1=x1. For i=2,...,m use four width-three clauses encoding zi=z_(i-1) XOR xi. For each forbidden triple (a,b,c) with c != a XOR b, include the clause false exactly on that triple. Add the unit NOT zm. For each b in {0,1}^m, add m unit clauses pinning xi=b_i. Order the pin units first, then XOR clauses, then the output unit. Use fixed variable IDs 0,...,2m-2 (1-based names in the code). Only the m signs of the first units vary. This CNF is SAT iff parity(b)=0, and its existential extension is unique when SAT.

Encode exactly with the repository's grammar: each literal with identifier v and positive flag s becomes (1,s), then (1,d) for each canonical LSB-first bit of v (none for zero), then (0,1); append (0,0) after each clause. Let w(b) be the encoded word of fixed even length n. All words end in 00. There are 13m-11 literal occurrences and 5m-3 clauses: explicitly m pins +4(m-1) XOR clauses +1 output =5m-3 clauses; literal occurrences m+12(m-1)+1=13m-11. Thus n=Theta(m log m): O(m log m) by identifier size, Omega(m log m) already from the m pin IDs. (No use of an asymptotic gate lower bound here.)

Apply the agent's actual balanced grammar projection at this n. With u=w[:-2], append to w the tokens 1001 1101 10, then pairs (1,NOT u_j) for all j, then 11 01 00. Call the resulting word y(b). It has N=3n+12 coordinates and weight t=2n+5. It is SAT iff w(b) is SAT. In the image, precisely two coordinates depend on each b_i: a positive rail b_i (original pin sign), and a negative rail NOT b_i (the paired suffix digit). Every other coordinate is constant. Thus y is injective.

Let P be uniform on y(b) for even parity b, and Q uniform for odd parity b. They are supported respectively on positive and negative words of the agent's exact G_n, both at weight t. Each support has 2^(m-1) words.

## 2. Identical low-order marginals and exponential approximate DNF/CNF bounds

Any set of fewer than m actual word coordinates involves fewer than m distinct programmable bits. Under either parity distribution these bits are exactly uniform: each partial assignment to r<m bits has 2^(m-r-1) even and 2^(m-r-1) odd completions. Consequently the two distributions agree on all joint marginals of fewer than m actual coordinates, on all multilinear polynomials of degree <m in the actual coordinates, and on every positive monomial of width <m. This includes constant or inconsistent rail patterns. The assertion is equality of marginals, not independence of all N coordinates (opposite rails are dependent).

Any monotone DNF on actual coordinates pulls back under y to an ordinary signed DNF in b after deleting constant and impossible terms and repeated literals. Call the number of distinct pinned bits in a consistent term its effective width. Let D be any such DNF with effective width <=w<m. For every accepted even string b, choose a witnessing term of width <=w. Flipping any bit not fixed by that term leaves D true. Hence at least m-w of its m hypercube neighbors, all odd, are accepted. Every accepted odd string receives at most m such edges. Counting edges between accepted even and odd strings gives

    Q(D=1) >= (1-w/m) P(D=1).

This is an approximation obstruction on the ENTIRE union of short terms, not merely equality of individual monomial moments.

More generally suppose D has P(D=1)>=1-epsilon and Q(D=1)<=epsilon. Split it into D_short (terms effective width <=w) and D_long (the other terms). Since Q(D_short=1)<=epsilon, the previous inequality gives P(D_short=1)<=epsilon/(1-w/m). Therefore

    P(D_long=1) >= 1-epsilon-epsilon/(1-w/m).

Each long consistent term fixes r>=w+1 bits; its even-parity probability is 2^(-r) if r<m, and at most 2^(-(m-1)) if r=m, hence <=2^(-w). Union bound yields

    #terms >= [1-epsilon-epsilon/(1-w/m)] 2^w.

For epsilon=1/4 and w=floor(m/2), this is >=2^floor(m/2)/4. For exact separation every consistent term must have effective width m (otherwise it hits both distributions), so at least 2^(m-1) terms are needed. Matching DNF of this size uses one complete rail conjunction per even assignment. By complementing the pullback, swapping parity distributions, and applying the same argument, the same term-count bounds apply to CNF clause counts. This proves exp(Omega(N/log N)) approximate DNF/CNF lower bounds for separating these distributions on an unbounded subsequence of actual slice lengths, and therefore for exact computation of G_n in those models. No claim about an exponential monotone circuit lower bound.

## 3. Formula lower bound (Khrapchenko edge argument, with proof)

For any fan-in-two monotone AND/OR formula H on the actual word bits that separates P and Q exactly, substitute the rails and constants to obtain a signed Boolean formula on m bits for even parity. Its number L of leaves does not increase. Let A be the even strings, B the odd strings, and E={(a,b) in A x B: distance(a,b)=1}. Then |A|=|B|=2^(m-1), |E|=m*2^(m-1).

Associate a deterministic rectangle partition of A x B to the formula tree. At an OR node whose values differ 1 on a and 0 on b, choose the first child that evaluates to 1 on a. Both are 0 on b, so the choice depends only on a and splits the current row set. At an AND node choose the first child that is 0 on b; both are 1 on a, and the choice splits the column set. Recursing from the root gives disjoint leaf rectangles A_l x B_l whose union is A x B; each nonempty leaf rectangle is separated by one signed literal. A constant cannot separate a nonempty rectangle. For a leaf labeled b_i or NOT b_i, every edge of E inside its rectangle must differ at i, and the edges form a matching (each endpoint has at most one such neighbor). Thus

    |E intersect (A_l x B_l)| <= min(|A_l|,|B_l|) <= sqrt(|A_l||B_l|).

Summing over leaves and applying Cauchy-Schwarz gives

    |E| <= sqrt(L * sum_l |A_l||B_l|) = sqrt(L |A||B|).

Therefore L>=|E|^2/(|A||B|)=m^2. In the binary formula model the gate count is at least m^2-1. For m a power of two this is sharp for separation on the promise: split parity into equal halves, and form the output phase using two ANDs and an OR on the two possible half-parity combinations. Recursively duplicating the required signed subformulas gives L(m)=4L(m/2), L(1)=1, hence m^2 leaves. This lower bound applies to general unrestricted signed formulas as well as the monotone slice formulas; in terms of N it is Omega(N^2/log^2 N) on our lengths. This is not a bound for AIGs with shared nodes.

## 4. Why the distributions are not a circuit lower bound

The very same P,Q have a monotone circuit separator on N inputs with at most 6(m-1) gates. Read only the paired rails. Maintain the odd and even parity of a prefix as two wires p,q. Start with p=b1,q=NOT b1 from actual positive and negative coordinates. On the next pair a=b_i,c=NOT b_i, update

    p' = (p AND c) OR (q AND a)
    q' = (p AND a) OR (q AND c).

These are six monotone gates per step and the output q separates P,Q exactly. This circuit is a total monotone function of all N coordinates, but is only asserted to agree with G_n on the selected support, NOT on the whole slice. Since m=Theta(N/log N), its cost is sublinear in N. Any distributional lower bound on all monotone separators of this pair cannot beat this upper bound.

There is a quantitative obstruction to a naive gate-by-gate approximation argument. Suppose every wire of this separator is assigned a short DNF (effective width <=w<m), with primaries exact. Let delta_g be the probability, under the equal mixture (P+Q)/2, that the approximant of gate g differs from applying g to its two operand approximants. At any assignment where no local disagreement occurs, induction in topological order gives agreement with the true output. The root approximant has mixture classification error >= (1-w/m)/2, since its two acceptance probabilities obey section 2. Union bound (once per distinct gate, no path multiplicity) implies

    sum_g delta_g >= (1-w/m)/2.

In particular some local error is at least (1-w/m)/(2s), where s is the actual separator gate count. For w=floor(m/2), this is >=1/(4s). No method that approximates every gate of this example by short DNFs can guarantee total local error o(1), regardless of how many terms the approximants are allowed. This is a precise limitation, not a disproof of the monotone approximation method for other carefully chosen distributions. A successful proof for G_n must choose distributions without such cheap joint separators and must prove a stronger closure/approximation invariant than low-order marginal agreement plus DNF/CNF hardness.

## 5. Executed verification

The standalone stdlib Python script below was run in the current research session. It constructs exact words, parses them using separately structured token logic, checks satisfiability by unit propagation plus DPLL, evaluates the monotone parity separator directly on the actual word coordinates, checks weight and constant/rail coordinates, and counts term marginals and short-DNF acceptance. For m=2..12 all 8188 words passed. Lengths N: 324,696,1134,1584,2100,2616,3132,3660,4254,4848,5442; at m=12 t=3625, separator upper bound 66. It performed 2165 monomial checks (exhaustive consistent rail patterns of width <m for m<=6; sampled actual-coordinate terms for larger m), 2200 seeded short-DNF checks, and verified the rectangle partition of the exact-size balanced formulas for m=2,4,8 (4,64,16384 pairs; 4,32,1024 adjacent pairs; 4,16,64 leaves). Seed 22661. All assertions passed. These finite checks do not replace the general proofs. No native solver benchmark, new SAT circuit lower bound, or independent Lean run claimed.

## 6. Runnable reference (stdlib Python)

```python
from itertools import product,combinations
from random import Random
from math import comb

def enc(F):
    w=[]
    for C in F:
        for l in C:
            v=abs(l)-1; w += [1,int(l>0)]
            while v: w += [1,v&1]; v >>= 1
            w += [0,1]
        w += [0,0]
    return tuple(w)

def parse(w):
    F=[]; C=[]; j=0
    while j<len(w):
        if w[j:j+2]==(0,0): F.append(C);C=[];j+=2;continue
        assert w[j]==1 and j+1<len(w)
        sign=w[j+1];j+=2;digits=[]
        while w[j:j+1]==(1,):digits.append(w[j+1]);j+=2
        assert w[j:j+2]==(0,1) and (not digits or digits[-1]);j+=2
        v=1+sum(b<<i for i,b in enumerate(digits));C.append(v if sign else -v)
    assert not C
    return F

def sat(F):
    while True:
        if not F:return True
        if any(not C for C in F):return False
        u=next((C[0] for C in F if len(C)==1),None)
        if u is None:break
        F=[[l for l in C if l!=-u] for C in F if u not in C]
    v=F[0][0]
    return sat(F+[[v]]) or sat(F+[[-v]])

def formula(x):
    m=len(x);F=[[i+1 if b else -i-1] for i,b in enumerate(x)];prev=1
    for i in range(2,m+1):
        z=m+i-1
        for a,b,c in product((0,1),repeat=3):
            if c != (a^b):F.append([(-v if t else v) for v,t in zip((prev,i,z),(a,b,c))])
        prev=z
    return F+[[-prev]]

def balance(w):
    assert w[-2:]==(0,0)
    u=w[:-2]
    return w+(1,0,0,1,1,1,0,1,1,0)+tuple(b for x in u for b in (1,1-x))+(1,1,0,1,0,0)

def table(m):
    return [balance(enc(formula(x))) for x in product((0,1),repeat=m)]

def monotone_sep(y,pos,neg):
    p,q=y[pos[0]],y[neg[0]]
    for i,j in zip(pos[1:],neg[1:]):
        a,b=y[i],y[j]
        p,q=(p&b)|(q&a),(p&a)|(q&b)
    return q

def main():
    r=Random(22661); checked=0; marginal=0; dnfs=0; rows=0
    for m in range(2,13):
        W=table(m);N=len(W[0]);n=(N-12)//3;t=2*n+5
        pos=[];neg=[];base=W[0]
        for i in range(m):
            v=W[1<<(m-1-i)];p=[j for j in range(N) if base[j]==0 and v[j]==1];q=[j for j in range(N) if base[j]==1 and v[j]==0];assert len(p)==len(q)==1;pos+=p;neg+=q
        for j,y in enumerate(W):
            assert len(y)==N and sum(y)==t
            assert sat(parse(y)) == (j.bit_count()%2==0)
            assert monotone_sep(y,pos,neg)==(j.bit_count()%2==0)
            assert all(y[a]^y[b] for a,b in zip(pos,neg))
            assert all(y[k]==base[k] for k in range(N) if k not in pos and k not in neg)
            checked+=1
        full=(1<<len(W))-1; even=sum(1<<j for j in range(len(W)) if j.bit_count()%2==0);odd=full^even
        bits=[sum(y[k]<<j for j,y in enumerate(W)) for k in range(N)]
        if m<=6:
            terms=(tuple(pos[i] if b==1 else neg[i] for i,b in enumerate(pat) if b!=-1) for pat in product((-1,0,1),repeat=m) if -1 in pat)
        else:
            terms=(tuple(r.sample(range(N),r.randrange(m))) for _ in range(200))
        for term in terms:
            a=full
            for k in term:a&=bits[k]
            assert (a&even).bit_count()==(a&odd).bit_count();marginal+=1
        w=m//2
        for _ in range(200):
            mask=0
            for __ in range(r.randrange(1,20)):
                ix=r.sample(range(m),r.randrange(w+1));a=full
                for i in ix:a&=bits[r.choice((pos[i],neg[i]))]
                mask|=a
            pp=(mask&even).bit_count();pn=(mask&odd).bit_count()
            assert m*pn >= (m-w)*pp
            dnfs+=1
        print('m',m,'original',n,'balanced',N,'weight',t,'rows',len(W),'separator_gate_upper',6*(m-1),flush=True)
    print('rows',checked,'monomial checks',marginal,'short DNF checks',dnfs)
if __name__=='__main__':main()

def parity_formula(ix,phase):
    if len(ix)==1:return ix[0]+1 if phase else -ix[0]-1
    a,b=ix[:len(ix)//2],ix[len(ix)//2:]
    return ('or',('and',parity_formula(a,1),parity_formula(b,1-phase)),('and',parity_formula(a,0),parity_formula(b,phase)))
def f_eval(f,x):
    if isinstance(f,int):return ((x>>(abs(f)-1))&1)^(f<0)
    a,b=f_eval(f[1],x),f_eval(f[2],x)
    return (a&b) if f[0]=='and' else (a|b)
def rectangle_check():
    for m in (2,4,8):
        f=parity_formula(list(range(m)),0);A=[x for x in range(1<<m) if x.bit_count()%2==0];B=[x for x in range(1<<m) if x.bit_count()%2==1]
        assert all(f_eval(f,x)==(x.bit_count()%2==0) for x in range(1<<m))
        leaves=[]
        def walk(f,A,B):
            if isinstance(f,int):
                assert all(f_eval(f,x) for x in A) and all(not f_eval(f,x) for x in B)
                leaves.append((A,B,f));return
            if f[0]=='or':
                a=[x for x in A if f_eval(f[1],x)];b=[x for x in A if not f_eval(f[1],x)]
                walk(f[1],a,B);walk(f[2],b,B)
            else:
                a=[x for x in B if not f_eval(f[1],x)];b=[x for x in B if f_eval(f[1],x)]
                walk(f[1],A,a);walk(f[2],A,b)
        walk(f,A,B)
        pairs={};edges=0
        for a,b,l in leaves:
            e=0
            for x in a:
                for y in b:
                    assert (x,y) not in pairs;pairs[x,y]=l
                    if (x^y).bit_count()==1:
                        assert x^y==1<<(abs(l)-1);e+=1
            assert e<=min(len(a),len(b));edges+=e
        assert len(pairs)==len(A)*len(B) and edges==m*len(A) and len(leaves)==m*m
        print('formula',m,'leaves',len(leaves),'pairs',len(pairs),'adjacent',edges)
if __name__=='__main__':rectangle_check()
```

## 7. Next research priority

Do not implement a synthesis feature for this parity control. For a real slice lower-bound attempt, examine distributions over legal encodings with nonlocal semantic dependencies where no simple signed projection or cheap separator is available, and require a compositional approximation lemma with explicit per-gate error control for arbitrary reconvergent DAGs. Compare any candidate invariant against the parity control before pursuing a full proof. The exact slice equivalence remains a useful research target, not a way to bypass the unrestricted circuit barrier.

---

# Historical research archive — older handoffs, not a request to repeat completed work

# Research handoff — affine-inequivalent hard block restrictions in a linear-size AIG

Processed agent revision: ebe057e6b6c1d4ffda7f80cd16a95d59e71707c4 (master). This is the checkpoint for the autonomous research task: do not count the handoff-only commit as a new agent revision.

## 0. Status and audit of the agent's new results

Both requested notes were fetched again after the experiments. RESEARCH_NOTES.md blob 88e22468e76a1a50883d940bea03f9c9bfe97b42; sat-search/NOTES_ORIENTATION_QUOTIENT.md blob 1dc2063bcbff6994f8af057deeb617a4cda00315. Read sat-search/results/coupled_reader/README.md at the processed revision. The agent independently verified the coupled-reader argument and certified C(0x07e1)=7 using exact three-input leaves plus identification and an archived seven-gate witness. The stronger recursive signed-regional baseline already gives 7; two-sided absorption improves just 1/300 five-input sampled tables and 0/89 frozen corpus targets against it. Phase compatibility improves 4/300 sampled five-input tables against that stronger baseline, 0/89 frozen targets. Do not port these as production improvements on present evidence. This supersedes the previous handoff's implementation recommendation and unresolved 0x07e1 witness. No independent rerun of the agent's native or Lean jobs is claimed here.

The new result below is a counterexample to a proposed superlinear resource-counting route, not a new SAT lower bound. The precise scope is summing unrestricted cofactor gate costs across disjoint input blocks even after quotienting by invertible affine input changes and output complement. It goes beyond counting residual diversity: each block cofactor itself is large in unrestricted circuit complexity, simultaneously at every common context. The function nonetheless has a linear-size AIG. No novelty claim; this is a paper proof, not Lean-checked. L-clb-036 remains open.

## 1. Statement

For every integer m >= 16 put M=2^m, k=2^(m-2), n=km. There exists a full-support n-input function F and a partition into k blocks of m inputs such that:

* F has an unrestricted AIG of at most 6n+3(M-1) gates (in particular O(n)).
* For every common assignment a of all n inputs, let f_v^a be the m-input restriction leaving only block v free. Every f_v^a requires at least floor(M/(16m))+1-3m gates.
* For distinct v,w, the functions f_v^a and f_w^b are inequivalent under every invertible affine transformation of their m inputs and output complementation, even for unrelated contexts a,b.
* Hence even a sum that counts only one representative from each affine/output-phase equivalence class of block restrictions can be Omega(n^2/(log n)^3), at every common assignment. A generic claim C(F) >= that sum divided by any fixed constant is false, as is division by a factor o(n/(log n)^3). Here C is unrestricted single-output AND count with free constants/complemented edges. In the counted AND/OR/NOT basis the same construction has O(n) size, by replacing free complemented edges with at most one NOT per used wire.

The family uses a nonuniform hard lookup table; existence is proved by counting. It is not an efficiently uniformly computable explicit hard function in the usual lower-bound sense. All logarithms in the proof below are base 2.

## 2. Construction and cost

Index each block by v in F_2^(m-2). Write a block x=(x0,x1,x2,...,x_(m-1)). Define the quadratic shear

    Q_v(x) = x1 * sum_(j=2..m-1) v_(j-2) x_j     (over F_2)
    T_v(x) = (x0+Q_v(x), x1, ..., x_(m-1)).

T_v is a bijection, its own inverse, and T_v T_w=T_(v+w). For v!=w their product is genuinely quadratic, not affine: its reduced multilinear polynomial has at least one x1*xj term. Compute the selected parity with at most m-3 XORs (the empty subset costs zero), one AND, and one XOR. Each XOR uses three AIG gates, so both T_v and its inverse cost at most 3m gates to compute their vector outputs.

Let h:F_2^m -> {0,1} be a lookup table chosen below. Set

    F(x^(0),...,x^(k-1)) = h( XOR_v T_v(x^(v)) ).

The block transforms cost <=3mk; the coordinatewise sum costs <=3m(k-1). A complete binary Shannon tree of h costs at most 3(M-1) AND gates (each two-way multiplexer uses three AND gates with free complements). Thus C(F)<=6n+3(M-1). Fixing every block other than v leaves

    f_v(x) = h(T_v(x)+c)

where c is the sum of the fixed transformed blocks. This identity is exact, not a promise about a particular assignment.

## 3. The affine quotient does not remove the obstruction

For a translation tau_c(x)=x+c, T_v tau_c T_v is affine and invertible. Its first coordinate is x0+c0+Q_v(x)+Q_v(x+c), and the quadratic parts cancel. Every other coordinate is a translation. Consequently h tau_c T_v = h T_v (T_v tau_c T_v). For a fixed v, ALL contexts give the same affine-equivalence class as h T_v. It therefore suffices to make the k base functions h T_v pairwise affine/output-phase inequivalent.

For distinct v,w, invertible affine A and epsilon in {0,1}, suppose

    h(T_v(x)) = h(T_w(A(x))) XOR epsilon    for every x.

Put y=T_v(x). This is the constraint h(y)=h(P(y)) XOR epsilon for the permutation P=T_w A T_v. A fixed point corresponds precisely to A(x)=T_(v+w)(x). The difference in the first coordinate is a nonzero multilinear polynomial of degree two: subtracting an affine polynomial cannot cancel its quadratic monomials. A nonzero multilinear polynomial of degree <=d on m bits is nonzero on at least 2^(m-d) points. Proof: induct on m, writing p=x_(m-1) q+r; if q=0 use the smaller variable count and double its weight; otherwise each assignment where q=1 contributes at least one nonzero among the two values, and q has degree <=d-1. For d=0 a nonzero constant has full weight. Thus P moves at least M/4 points. Its cycles number at most M-M/8, since every nontrivial cycle has length >=2.

Take h uniformly at random from all 2^M truth tables. For a fixed P and epsilon the constraint admits at most two choices per cycle (zero if inconsistent on a cycle), so its probability is <=2^(-M/8). There are at most k^2 ordered pairs and at most 2^(m^2+m) invertible affine transformations (bounding all matrices and offsets), and two output phases. The union bound on ANY cross-block equivalence is

    2^(2(m-2)+m^2+m+1-M/8).

This is below 1/4 for m>=16. The exponential negative term dominates, and the inequality persists by induction since M/8 doubles and the positive polynomial grows by 2m+4. This proof does not assume independence of the different equivalence events.

## 4. Hardness and full support simultaneously

Let s=floor(M/(16m)). The number of circuits of size <=s on m inputs is at most

    (s+1) [2(m+s+1)]^(2s+1).

Count ordered operand literals for each AND, with the available signals padded to m+s+1 including the constant, and count output literals; overcounting invalid forward references is safe. Since 2(m+s+1)<=M for m>=16, the log of this bound is at most (2s+1)m+log(s+1) <= M/8+2m < M-2. Thus Pr[C(h)<=s]<1/4. Also, each h T_v is a uniformly random Boolean table because T_v is a permutation. The probability it ignores any specific variable is 2^(-M/2); the union bound over k*m variables is k*m*2^(-M/2)<1/4. In fact this also implies full support for all translated h tau_c T_v: union bound over all M translations costs at most an extra factor M and remains <1/4. Use this stronger bound if requiring support of EVERY restriction. The three failure probabilities sum to <1, so a single h satisfies all requirements.

Any AIG for h tau_c T_v can be composed with T_v tau_c, whose vector outputs cost at most 3m (translations are free complemented edges), to compute h. Therefore C(f_v)>=C(h)-3m>=s+1-3m. This argument works for every context regardless of the symmetry argument. For m>=16 the lower bound is positive; asymptotically it is Omega(M/m). Since n=km, k=M/4, the sum is Omega(kM/m)=Omega(n^2/m^3). Also m=Theta(log n). The same asymptotic separation holds with lower bounds measured in the counted basis: the free-AND count is a lower bound for it, while the original construction costs O(n).

## 5. Consequence for restriction-based circuit lower bounds

In a common restriction context, one might try to charge each live subcircuit once for every genuinely different hard block function it computes, discarding phase/permutation or even affine duplicates. This construction rules out using inequivalence alone as a guarantee of disjoint computational work. In the original circuit, the single shared lookup circuit receives an invertible block-dependent re-encoding when any block alone varies. In fact all k block restrictions simultaneously have near-Shannon-scale cost and are inequivalent under affine changes, but their cost comes from one shared lookup. The barrier applies to sums of exact unrestricted minima, not just weak lower bounds.

This does NOT exclude a bound exploiting the specific SAT semantics or a bound measuring the cost of an entire common restriction family with shared programmable gates. It excludes generic additive accounting based only on individual cofactor complexities and affine inequivalence. The preceding SAT verifier/Tseitin bridge embeds a deterministic AIG of size O(n) as a fixed CNF with n programmable input-unit signs and total exact encoding length O(n log n). Thus these negative controls occur among fixed CNF projections as well; this is not an upper bound on general SAT_n. No new exact SAT string experiment was performed this round; the embedding uses the earlier proved general bridge.

Suggested next mathematical target: characterize when a common core can serve restrictions through distinct low-cost *nonlinear* bijections, and look for a SAT-specific invariant incompatible with that kind of sharing. Do not use raw block lower-bound sums or affine-orbit counts as a superlinear certificate. Do not port the random construction as a production solver enhancement. The earlier regional-bound result is a separate issue.

## 6. Actual executed verification

Python stdlib reference below, seed 8312026 for the lookup tables and 671209 for sampled affine maps. All gates in the constructed circuits were evaluated with bit-packed truth tables on the free block, using independently computed direct shear/lookup expected rows. Actual results:

| m | n | constructed gates | blocks | distinct sorted absolute Walsh spectra | largest collision |
|---:|---:|---:|---:|---:|---:|
| 5 | 40 | 173 | 8 | 4 | 4 |
| 6 | 96 | 428 | 16 | 3 | 8 |
| 7 | 224 | 1013 | 32 | 32 | 1 |
| 8 | 512 | 2302 | 64 | 64 | 1 |
| 9 | 1152 | 5163 | 128 | 128 | 1 |
| 10 | 2560 | 11465 | 256 | 256 | 1 |

The multiset of absolute Walsh coefficients is invariant under invertible affine changes and output complement: linear characters are permuted by the transpose of the invertible linear part, and translations/output phase only multiply coefficients by signs. Distinct fingerprints therefore certify pairwise inequivalence for m=7..10 for these specific sampled tables, also at every context by the proved conjugation. Collisions at m=5,6 do NOT certify equivalence. No claim of exact hardness for those small sampled h.

* 599168 exhaustive conjugation row checks (m=3..7).
* 24192 AIG cofactor row checks (12 random contexts per m=5..10), 72 Walsh invariance checks.
* 1344 exhaustive invertible affine comparisons for m=3, minimum moved points 2=M/4.
* 700 sampled comparisons at m=4..10, all at least M/4.
* Counting arithmetic at m=16,20,24,32: respective certified existence per-block lower bounds 209,3217,43619,8388513. These are consequences of counting, not solver results on the sampled small tables.
* No test failed; no native speedup, no Lean verification, and no explicit superlinear SAT lower bound established.

## 7. Runnable reference (Python 3.10+, standard library)

Extract this first Python code block as affine_cofactor_check.py and execute it. The two original scripts were executed separately; the single consolidated block below combines them and reports the stronger all-context support failure bound (the original arithmetic checked the base-table bound; adding m to its log bound leaves all four cases strictly below -2).

```python
from random import Random
from collections import Counter
from math import log2
from itertools import product

def shear(x,v):
    return x ^ (((x>>1)&1) & ((v&(x>>2)).bit_count()&1))

def walsh(t):
    a=[1-2*b for b in t]; w=1
    while w<len(a):
        for i in range(0,len(a),2*w):
            for j in range(i,i+w):
                u,v=a[j],a[j+w];a[j]=u+v;a[j+w]=u-v
        w*=2
    return tuple(sorted(map(abs,a)))

class AIG:
    def __init__(self,n):self.n=n;self.g=[];self.cache={}
    def AND(self,a,b):
        if a==b:return a
        if a==b^1 or a==0 or b==0:return 0
        if a==1:return b
        if b==1:return a
        p=tuple(sorted((a,b)))
        if p not in self.cache:
            self.g.append(p);self.cache[p]=2*(self.n+len(self.g))
        return self.cache[p]
    def XOR(self,a,b):return self.AND(self.AND(a,b^1)^1,self.AND(a^1,b)^1)^1
    def mux(self,x,a,b):return self.AND(self.AND(x^1,a)^1,self.AND(x,b)^1)^1
    def parity(self,a):
        z=0
        for x in a:z=self.XOR(z,x)
        return z
    def lookup(self,z,t):
        if not z:return t[0]
        return self.mux(z[0],self.lookup(z[1:],t[::2]),self.lookup(z[1:],t[1::2]))
    def eval(self,vals,mask,out):
        w=[0]+list(vals)
        def lit(l):return w[l//2]^(mask if l&1 else 0)
        for a,b in self.g:w.append(lit(a)&lit(b))
        return lit(out)

def build(m,h):
    k=1<<(m-2);g=AIG(k*m);z=[0]*m
    for v in range(k):
        x=[2*(v*m+j+1) for j in range(m)]
        q=g.AND(x[1],g.parity([x[j+2] for j in range(m-2) if v>>j&1]))
        x[0]=g.XOR(x[0],q)
        z=[g.XOR(a,b) for a,b in zip(z,x)]
    return g,g.lookup(z,h)

def main():
    r=Random(8312026); conjugates=0; replays=0; spectrum_checks=0
    for m in range(3,8):
        M=1<<m;k=1<<(m-2)
        for v in range(k):
            for c in range(M):
                f=lambda x:shear(shear(x,v)^c,v)
                a=f(0); cols=[f(1<<j)^a for j in range(m)]
                for x in range(M):
                    y=a
                    for j in range(m):
                        if x>>j&1:y^=cols[j]
                    assert y==f(x);conjugates+=1
    for m in (5,6,7,8,9,10):
        M=1<<m;k=1<<(m-2);h=[r.randrange(2) for _ in range(M)]
        f=[walsh([h[shear(x,v)] for x in range(M)]) for v in range(k)]
        g,out=build(m,h); n=k*m;mask=(1<<M)-1
        patterns=[sum(1<<x for x in range(M) if x>>j&1) for j in range(m)]
        assert len(g.g)<=6*n+3*(M-1)
        for _ in range(12):
            v=r.randrange(k);a=[r.randrange(M) for _ in range(k)];c=0
            for j,x in enumerate(a):
                if j!=v:c^=shear(x,j)
            vals=[mask if x>>j&1 else 0 for x in a for j in range(m)]
            vals[v*m:(v+1)*m]=patterns
            want=[h[shear(x,v)^c] for x in range(M)]
            assert g.eval(vals,mask,out)==sum(b<<x for x,b in enumerate(want));replays+=M
            assert walsh(want)==f[v];spectrum_checks+=1
        groups=Counter(f)
        print('m',m,'n',n,'gates',len(g.g),'blocks',k,'distinct Walsh fingerprints',len(groups),'largest collision',max(groups.values()),flush=True)
    print('affine conjugation row checks',conjugates,'AIG cofactor row checks',replays,'Walsh invariance checks',spectrum_checks)
    for m in (16,20,24,32):
        M=1<<m;k=1<<(m-2);n=k*m;s=M//(16*m)
        L=log2(s+1)+(2*s+1)*log2(2*(m+s+1))
        E=2*(m-2)+m*m+m+1-M//8
        essentialE=(m-2)+log2(m)+m-M//2
        assert L<M-2 and E<-2 and essentialE<-2
        assert s+1>3*m
        print('counting m',m,'n',n,'s',s,'log2 circuit count upper',round(L,2),'log2 equivalence failure upper',round(E,2),'per-block lower',s+1-3*m)

def independent(cols):
    span={0}
    for c in cols:
        if c in span:return False
        span|={x^c for x in span}
    return True

def apply(x,cols,c):
    for i,t in enumerate(cols):
        if x>>i&1:c^=t
    return c

def moved_check():
    m=3;M=1<<m; counts=[]
    for cols in product(range(1,M),repeat=m):
        if not independent(cols):continue
        for c in range(M):
            moved=sum(apply(x,cols,c)!=shear(x,1) for x in range(M))
            assert moved>=M//4;counts.append(moved)
    print('exhaustive m3 affine comparisons',len(counts),'minimum moved',min(counts))
    r=Random(671209);count=0
    for m in range(4,11):
        M=1<<m
        for _ in range(100):
            v=r.randrange(1,1<<(m-2));cols=[1<<i for i in range(m)]
            for j in range(5*m):
                a,b=r.sample(range(m),2);cols[a]^=cols[b]
            c=r.randrange(M)
            assert independent(cols)
            assert sum(apply(x,cols,c)!=shear(x,v) for x in range(M))>=M//4
            count+=1
    print('sampled affine comparisons',count)

if __name__=='__main__':
    main()
    moved_check()
```

---

# Historical archive — earlier handoffs (do not reimplement reviewed or integrated work)

# Research handoff — coupled first-gate reader budgets

## 0. Scope and status

New: a small unconditional AIG lower-bound strengthening using several restrictions of the same first-gate topology. It extends the repository's existing `sat-search/theory/first_gate_bound.py` (mode 2 there, free NOT, identification enabled). The underlying no-reapplication rewrite is standard and already used in the Percy encoder; the proposed use is in the recursive numerical lower bound and in consistent local budget inequalities. No novelty claim, no production port, no new asymptotic SAT lower bound. The strongest SAT theorem remains the repository's formally verified 2n-o(n) on multiples of six. L-clb-036 remains open. The isolation potential from the previous handoff is unchanged; the new recurrence did not beat the existing first-gate bound on the isolated-model sample.

Read-only repository review at master `ec3ed3ee020722e366fc05b63ca528ad3f0b5d48`: orientation notes blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`, research notes blob `88db5dd0ca6fcac530b6926fd39750da044e1769`, signed modules notes blob `43fcd1c63f9b0ba2f4d6963f1926c28d8d861854`. The two requested notes were rechecked after the experiment. Existing first-gate bounds and the no-reapplication rule are not proposed as new implementations. No repository files modified. Previous handoffs follow as historical context; only this first section is new work.

## 1. Normal form and simultaneous two-sided saving

Model: fan-in-two AND gates, free complemented edges and constants, one output. Trim inessential inputs. A minimum circuit for a full-support function on n>=3 has no redundant gate, and every gate lies in the output cone. Among its minimum circuits choose one maximizing the number of gates with two distinct primary inputs (first-layer gates). It has no degenerate gate (constant or identical/complementary operands) and no two gates with equal/complementary Boolean outputs: either would permit deletion.

Let g be any first-layer gate `(x_i xor a) AND (x_j xor b)` with i != j. Its absorbing primary values are a,b. Let h be a later gate with g and x_i as operands (allow either edge to be complemented). Put u=x_i xor a and v=x_j xor b. The four possibilities are

    u & g = g
    ~u & g = 0
    u & ~g = u & ~v
    ~u & ~g = ~u.

The same identities hold with u,v interchanged. Thus h can be bypassed or replaced by a first-layer AND. Bypass contradicts minimal size. Replacement is legitimate in topological order; g must remain live, since otherwise the replacement followed by dead-gate deletion would contradict minimum size. The replacement strictly increases the number of first-layer gates: h was not first-layer and the other first-layer gates are unaffected. This contradicts the extremal choice. Hence no gate reads both g and either x_i or x_j in this normalized minimum circuit. This argument applies simultaneously to every first-layer gate, not just the earliest one.

Write R_i,R_j for the gates other than g directly reading x_i,x_j, and R_g for direct consumers of g. Then R_g is disjoint from R_i union R_j. R_g is nonempty because g is live and cannot be the output of a full-support n>=3 function. If f restricted to x_j=b still depends on x_i then R_i is nonempty, since otherwise the absorbing value at g would mask the only occurrence of x_i. Symmetrically if f restricted to x_i=a still depends on x_j then R_j is nonempty. Consequently

    C(f) >= C(f|x_i=a) + 2 + [x_i essential in f|x_j=b]
    C(f) >= C(f|x_j=b) + 2 + [x_j essential in f|x_i=a]

for the same first-layer orientation (a,b) in this minimum circuit. Fixing a primary removes its direct readers and g; under the absorbing value, g is constant and its direct consumers also simplify. They are distinct from the primary readers by the normal form. The brackets are 0/1 indicators. Use known lower bounds in place of C on the right. This is stronger than using only the minimum over the two restriction values of a variable. In particular when f is Strong in the sense of `CircuitLemmas/Robust.lean`, BOTH absorbing values of any first-layer gate give at least three deletions in the normalized minimum, and both neutral values give at least two. It does NOT say that every arbitrary circuit has both three-gate savings, nor that the proof can force a particular primary to be in the first layer.

To obtain an unconditional whole-function bound, take the max of these constraints and existing conditional first-gate inequalities for a proposed first gate, then the min over all i<j and signs a,b. Combine with any unconditional bound by max. Recursion on strictly fewer variables is well founded. Use full-support trimming before applying n>=3. For n<=1 cost zero; for essential two-input functions cost 1 except XOR/XNOR cost 3. A truth table cofactor need not have full support; apply its own trimmed lower bound. No structural condition on the original circuit is assumed other than the AIG model, because a normalized minimum exists.

## 2. Joint reader profile (coupled restrictions)

For the same first-layer gate g, use three binary indicators:

* A: at least one later gate reads i but not j;
* B: at least one later gate reads j but not i;
* D: at least one other gate reads both i and j.

The three classes are disjoint and each is disjoint from R_g. These are lower counts, not exact multiplicities. If x_i survives x_j=b, require A or D; if x_j survives x_i=a, require B or D. Thus there are at most eight possible profiles. No need to reconstruct a common circuit to check necessary conditions.

For a,b fixed, let l_i(c), l_j(c) be lower bounds for the individual cofactors, l_ij be the maximum lower bound over all four simultaneous constant restrictions of i,j, and e(p) be a lower bound after identification x_j=x_i xor p. Then the following inequalities hold in any normalized minimum with the profile:

    C(f) >= l_i(a)     + 2 + A + D
    C(f) >= l_i(1-a)   + 1 + A + D
    C(f) >= l_j(b)     + 2 + B + D
    C(f) >= l_j(1-b)   + 1 + B + D
    C(f) >= l_ij       + 2 + A + B + D
    C(f) >= e(a xor b) + 1 + D
    C(f) >= e(1 xor a xor b) + 2 + D.

Proof: single constant restrictions remove g and all direct primary readers of the pinned input, plus R_g if g is absorbing. With both primaries pinned, all three reader classes, g and at least one consumer of g disappear irrespective of the signs. For identification with parity a xor b, g aliases a literal; every D gate receives the same primary with possibly different edge signs and collapses. For the opposite parity, g is constant, so R_g also collapses. All counted sets are disjoint as required. These are valid deletions even if additional cascades occur. Deletion need not preserve the old topology; only the restricted function matters. No claim that the identified variable is essential in the restriction, or that unrelated gates can be charged twice.

Take the maximum of all seven inequalities and the prior per-gate bound, then minimize over the eight feasible profiles. Finally minimize over first-gate choices, which exist in a minimum circuit. This couples the restrictions: a low double-constant deletion count requires the same two inputs to share a reader, and that implies additional deletion in both identification restrictions. Simply independently minimizing each constraint would lose this relation. The code below compares the existing recurrence (mode 0), adding Section 1 only (mode 1), and adding Section 2 (mode 2). It reimplements the repository recurrence from the inspected source, not a native benchmark or a differential against the installed repository Python module.

At a fixed candidate budget K, these are also sound conditional topology cuts **if the search explicitly restricts to the normalized minimum/at-most decision model**: for example, if e(a xor b)+2 > K, then D=0 whenever g is present; if l_ij+4 > K, the profile A=B=1,D=0 is forbidden. Do not apply these as universal constraints on an arbitrary fixed unnormalized topology, a forced prefix, or exact-size padded circuits. For practical use, start with the two inexpensive inequalities of Section 1. Reuse existing recursive cofactor values. The eight-profile test and identification constraints show no extra gains when exact three-input leaves are used in the tested screen.

## 3. Actual results and negative findings

Standalone Python run: 32 local truth-table identities; independent nonredundant truth-function-set enumeration up to 3 gates on 2 inputs, 6 on 3 inputs and 4 on 4 inputs. Total 4,282,074 candidate output hits (repetitions included), 8+128+1795 distinct complement classes across the three dimensions. All lower bounds checked against the resulting known upper budgets. The exhaustive 3-input enumeration reaches all 128 complement classes, so its first-discovery costs are exact (a minimum circuit never needs a constant/duplicate output gate, and retaining available complemented truth functions suffices for future gates). Random circuit checks: 1,500 (173 full-support), zero violations.

Recursive leaves using the existing bound (no exact 3-input table):

| full support targets | cases | Section 1 gain | additional Section 2 gain |
|---|---:|---:|---:|
| 3 inputs exhaustive | 218 | 0 | 0 |
| 4 inputs exhaustive | 64594 | 384 | 192 |
| 5 inputs seeded | 300 | 3 | 1 |
| 6 inputs seeded | 80 | 0 | 0 |

Maximum gain in these screens: one gate. Example 0x06b0 on 4 inputs goes 6,6,7. LSB row convention.

Fairer comparison: all three modes use exact enumerated 3-input minima as leaves. Clear the recursive memo before changing leaves.

| targets | cases | Section 1 gain | additional Section 2 gain |
|---|---:|---:|---:|
| 4 inputs exhaustive | 64594 | 384 | 0 |
| 5 inputs seeded | 300 | 6 | 0 |

The 384 gains are EXACTLY the NPN orbit of `0x07e1` (checked by permutation, input negations and output complement), so this is only one 4-input NPN class. `0x07e1` goes from lower bound 6 to 7; do not call it a newly established minimum. An optional independent seven-gate SMT witness search via libz3 reached its 12-second solver timeout, returning unknown, not UNSAT. No exact size certificate from that search. Example 5-input `0xc688438d`: 8 -> 9 with exact three-input leaves. No additional profile gain in the sampled cases with exact leaves.

For the previous isolated-model functions, tested all 742 independent nonempty sets on four inputs and 200/80 seeded even-parity subsets on five/six inputs. The new bound exceeded the recursive isolation bound in 456/174/80 cases but **never exceeded the existing first-gate recurrence**. Do not present those as new improvements over production. All checks passed; no solver/native runtime gain has been demonstrated.

The recurrence remains local gate elimination: each recursive step uses at most a constant number of deletions while reducing the number of ordinary inputs, so it does not prove a superlinear lower bound. In particular the new per-step increments are at most 5 (with the binary indicators, including double restrictions), and the inherited support/excess contribution is at most the number of eliminated coordinates (apart from the harmless constant-function base convention). Induction gives a crude bound of 5n for this numerical recurrence even with exact three-input leaves. The search of reader profiles is not a way of summing all cofactor complexities. Future work should seek a genuinely reusable multi-restriction resource, not keep increasing the local deletion constants.

## 4. Executable reference (stdlib Python)

Extract the first Python fence to `joint_reader_check.py` and run `python -B joint_reader_check.py`. It includes the exhaustive enumeration, the baseline, the two new modes, all checks and orbit certificate. The optional SMT witness search is not required and is not used as evidence for a lower bound.

```python
from itertools import combinations, product, permutations
from collections import Counter
from functools import lru_cache
from random import Random
from time import perf_counter

@lru_cache(None)
def co(n,f,i,b):
    mask=(1<<i)-1
    return sum(((f>>((x&mask)|(b<<i)|((x&~mask)<<1)))&1)<<x for x in range(1<<(n-1)))
@lru_cache(None)
def support(n,f):
    return tuple(i for i in range(n) if co(n,f,i,0)!=co(n,f,i,1))
def canon(n,f):return min(f,f^((1<<(1<<n))-1))
@lru_cache(None)
def trim(n,f):
    for i in reversed(range(n)):
        if co(n,f,i,0)==co(n,f,i,1):
            f=co(n,f,i,0); n-=1
    return n,canon(n,f)
@lru_cache(None)
def ident(n,f,i,j,p):
    assert i<j
    mask=(1<<j)-1
    return sum(((f>>((x&mask)|((x&~mask)<<1)|(((x>>i&1)^p)<<j)))&1)<<x for x in range(1<<(n-1)))

def lower(n,f,mode):return solve(*trim(n,f),mode)
EXACT3 = None
@lru_cache(None)
def solve(n,f,mode):
    if n<2:return 0
    if n==2:return 3 if f==6 else 1
    if n==3 and EXACT3 is not None:return EXACT3[f]
    c=[[co(n,f,i,b) for b in (0,1)] for i in range(n)]
    t=[[lower(n-1,g,mode) for g in pair] for pair in c]
    full=(1<<(1<<(n-1)))-1
    nc=[all(g not in (0,full) for g in pair) for pair in c]
    L=max(n-1,max(t[i][b]+n-max(1,len(support(n-1,c[i][b]))) for i in range(n) for b in (0,1)))
    for i in range(n):
        if nc[i]:L=max(L,min(t[i])+2)
        if c[i][0]^c[i][1]==full:L=max(L,min(t[i])+3)
    best=10**9
    for i,j in combinations(range(n),2):
        js=[j-1 in support(n-1,g) for g in c[i]]
        ins=[i in support(n-1,g) for g in c[j]]
        eq=[lower(n-1,ident(n,f,i,j,p),mode) for p in (0,1)]
        if mode==2:
            both=max(lower(n-2,co(n-1,c[i][a],j-1,b),mode) for a,b in product((0,1),repeat=2))
        for a,b in product((0,1),repeat=2):
            # Existing repository first_gate_bound.py (mode 2 there).
            v=max(L,t[i][a]+2,t[j][b]+2,eq[a^b]+1,eq[1^a^b]+2)
            if js[a]:
                v=max(v,max(t[j])+2)
                if nc[j]:v=max(v,min(t[j])+3)
            if ins[b]:
                v=max(v,max(t[i])+2)
                if nc[i]:v=max(v,min(t[i])+3)
            if mode>=1:
                # No first-layer reapplication in a suitable minimum circuit.
                v=max(v,t[i][a]+2+ins[b],t[j][b]+2+js[a])
            if mode==2:
                # One common local reader pattern must meet all restrictions.
                local=10**9
                for A,B,AB in product((0,1),repeat=3):
                    if ins[b] and not (A or AB):continue
                    if js[a] and not (B or AB):continue
                    u=max(v,t[i][a]+2+A+AB,t[i][1-a]+1+A+AB,
                          t[j][b]+2+B+AB,t[j][1-b]+1+B+AB,
                          both+2+A+B+AB,eq[a^b]+1+AB,eq[1^a^b]+2+AB)
                    local=min(local,u)
                v=local
            best=min(best,v)
    return best

# Independent exhaustive construction; quotient by complemented truth functions.
def enumerate_aig(n,maxg):
    full=(1<<(1<<n))-1
    prim=[canon(n,sum(1<<x for x in range(1<<n) if x>>i&1)) for i in range(n)]
    states={tuple(sorted(prim))}; costs={0:0,**{x:0 for x in prim}}; hits=0
    for k in range(1,maxg+1):
        new=set()
        for st in states:
            present=set(st)
            for a,b in combinations(st,2):
                for aa,bb in product((a,a^full),(b,b^full)):
                    c=canon(n,aa&bb)
                    if c==0 or c in present:continue
                    hits+=1
                    costs.setdefault(c,k)
                    if k<maxg:new.add(tuple(sorted((*st,c))))
        states=new
    return costs,hits

def independent(n,f):
    return f and all(not (f>>(x^(1<<i))&1) for x in range(1<<n) if f>>x&1 for i in range(n))
@lru_cache(None)
def q(n,f):
    if n<=1:return 0
    cs=[co(n,f,i,b) for i in range(n) for b in (0,1)]
    qs=[q(n-1,g) for g in cs if g]
    return max(qs+([1+min(qs)] if all(cs) else []))

def main():
    start=perf_counter(); exact={}
    # Algebraic normal form: each signed consumer of a first-layer gate
    # and one original primary is a literal, constant, or signed minterm.
    prim=(0b1010,0b1100); full=15
    allowed={0,full,*prim,*(p^full for p in prim)}
    allowed.update((prim[0]^(full if a else 0))&(prim[1]^(full if b else 0)) for a,b in product((0,1),repeat=2))
    count=0
    for a,b,i,c,d in product((0,1),repeat=5):
        g=(prim[0]^(full if a else 0))&(prim[1]^(full if b else 0))
        h=(g^(full if c else 0))&(prim[i]^(full if d else 0))
        assert h in allowed; count+=1
    print('local rewrite truth tables',count,flush=True)
    for n,g in ((2,3),(3,6),(4,4)):
        costs,hits=enumerate_aig(n,g); exact[n]=costs
        for f,c in costs.items():assert lower(n,f,2)<=c,(n,hex(f),c,lower(n,f,2))
        print('enumeration',n,g,'distinct complement classes',len(costs),'candidate output hits',hits,flush=True)
    for n in (3,4,5,6):
        rng=Random(738+n); counts=Counter(); witnesses=[]; gain_max=0
        fs=range(1<<(1<<n)) if n<=4 else [rng.getrandbits(1<<n) for _ in range(300 if n==5 else 80)]
        for f in fs:
            if len(support(n,f))!=n:continue
            a,b,c=[lower(n,f,m) for m in range(3)]
            assert a<=b<=c,(n,f,a,b,c)
            counts['full_support']+=1; counts['no_reapp_gain']+=b>a; counts['pattern_gain']+=c>b;counts['total_gain']+=c>a
            if c>a and (len(witnesses)<5 or c-a>gain_max):witnesses.append((hex(f),a,b,c));gain_max=max(gain_max,c-a)
        print('full-support screen',n,dict(counts),'witnesses',witnesses,'max gain',gain_max,flush=True)
    for n in (4,5,6):
        rng=Random(421+n); cnt=Counter(); ex=[]
        fs=range(1,1<<(1<<n)) if n==4 else [sum(1<<x for x in range(1<<n) if x.bit_count()%2==0 and rng.random()<.55) for _ in range(200 if n==5 else 80)]
        for f in fs:
            if not independent(n,f):continue
            a,b,c=[lower(n,f,m) for m in range(3)];d=n-1+2*q(n,f)
            cnt['sets']+=1;cnt['pattern_over_existing_first_gate']+=c>a;cnt['pattern_over_isolation']+=c>d;cnt['pattern_over_both']+=c>max(a,d)
            if c>max(a,d) and len(ex)<6:ex.append((hex(f),a,b,c,d))
        print('isolated',n,dict(cnt),ex,flush=True)
    rng=Random(921);cnt=Counter()
    for n in range(2,7):
        full=(1<<(1<<n))-1
        for _ in range(300):
            ws=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
            G=rng.randrange(1,3*n+1)
            for _ in range(G):
                a,b=rng.choices(ws,k=2);ws.append((a^(full if rng.randrange(2) else 0))&(b^(full if rng.randrange(2) else 0)))
            f=ws[-1];assert lower(n,f,2)<=G,(n,G,f,lower(n,f,2));cnt['circuits']+=1;cnt['full_support']+=len(support(n,f))==n
    print('random circuits',dict(cnt),flush=True)
    global EXACT3
    EXACT3=exact[3]; assert len(EXACT3)==128
    solve.cache_clear()
    for n in (4,5):
        rng=Random(884+n); cnt=Counter(); ex=[]; gained=set()
        fs=range(1<<(1<<n)) if n==4 else [rng.getrandbits(1<<n) for _ in range(300)]
        for f in fs:
            if len(support(n,f))!=n:continue
            a,b,c=[lower(n,f,m) for m in range(3)]
            assert a<=b<=c
            if n==4 and canon(n,f) in exact[n]:assert c<=exact[n][canon(n,f)]
            cnt['cases']+=1;cnt['no_reapp_gain']+=b>a;cnt['pattern_gain']+=c>b;cnt['total_gain']+=c>a
            if c>a:
                gained.add(f)
                if len(ex)<6:ex.append((hex(f),a,b,c))
        print('exact three-input leaves',n,dict(cnt),ex,flush=True)
        if n==4:
            orbit=set(); f=0x07e1
            for p in permutations(range(n)):
                for mask in range(16):
                    v=sum(((f>>sum((((x^mask)>>i)&1)<<p[i] for i in range(n)))&1)<<x for x in range(16))
                    orbit.update((v,v^65535))
            assert gained==orbit
            print('exact-leaf four-input gains are one NPN orbit',len(orbit),hex(min(orbit)),flush=True)
    print('elapsed seconds',perf_counter()-start,flush=True)
if __name__=='__main__':main()
```

## 5. Replay output

```text
local rewrite truth tables 32
enumeration 2 3 distinct complement classes 8 candidate output hits 54
enumeration 3 6 distinct complement classes 128 candidate output hits 3766248
enumeration 4 4 distinct complement classes 1795 candidate output hits 515772
full-support screen 3 {'full_support': 218, 'no_reapp_gain': 0, 'pattern_gain': 0, 'total_gain': 0} witnesses [] max gain 0
full-support screen 4 {'full_support': 64594, 'no_reapp_gain': 384, 'pattern_gain': 192, 'total_gain': 576} witnesses [('0x6b0', 6, 6, 7), ('0x6d0', 6, 6, 7), ('0x790', 6, 6, 7), ('0x7e2', 5, 6, 6), ('0x7e4', 5, 6, 6)] max gain 1
full-support screen 5 {'full_support': 300, 'no_reapp_gain': 3, 'pattern_gain': 1, 'total_gain': 4} witnesses [('0xda9c8bb1', 8, 9, 9), ('0x870856ff', 8, 8, 9), ('0x4729e3fc', 8, 9, 9), ('0x9cf0341c', 8, 9, 9)] max gain 1
full-support screen 6 {'full_support': 80, 'no_reapp_gain': 0, 'pattern_gain': 0, 'total_gain': 0} witnesses [] max gain 0
isolated 4 {'sets': 742, 'pattern_over_existing_first_gate': 0, 'pattern_over_isolation': 456, 'pattern_over_both': 0} []
isolated 5 {'sets': 200, 'pattern_over_existing_first_gate': 0, 'pattern_over_isolation': 174, 'pattern_over_both': 0} []
isolated 6 {'sets': 80, 'pattern_over_existing_first_gate': 0, 'pattern_over_isolation': 80, 'pattern_over_both': 0} []
random circuits {'circuits': 1500, 'full_support': 173}
exact three-input leaves 4 {'cases': 64594, 'no_reapp_gain': 384, 'pattern_gain': 0, 'total_gain': 384} [('0x7e1', 6, 7, 7), ('0x7e8', 6, 7, 7), ('0xbd2', 6, 7, 7), ('0xbd4', 6, 7, 7), ('0xdb2', 6, 7, 7), ('0xdb4', 6, 7, 7)]
exact-leaf four-input gains are one NPN orbit 384 0x7e1
exact three-input leaves 5 {'cases': 300, 'no_reapp_gain': 6, 'pattern_gain': 0, 'total_gain': 6} [('0xc688438d', 8, 9, 9), ('0xc7f71aa0', 8, 9, 9), ('0x794df1b0', 8, 9, 9), ('0x93c11280', 8, 9, 9), ('0xc4eb4ca2', 8, 9, 9), ('0x1d3ec55', 8, 9, 9)]
elapsed seconds 24.592152965999958
```


---

# Prior research archive (historical; no request to repeat integrated work)

# Research handoff — isolated-model restriction potential for unrestricted AIGs

## 0. Status and priority

This round gives an unconditional (free-complement AIG) **linear** lower-bound certificate for projected functions, rather than another fixed-template representation theorem. It uses the existing `three_step` and `excess_restriction` lemmas from the agent's Lean development. The new combination is a paper proof, not yet Lean checked. No novelty claim or production solver change. It does not establish L-clb-036 and cannot by itself exceed 3n-3 on n input bits. The strongest SAT lower bound reported formally checked remains 2n-o(n) on multiples of six. The fixed programmable fork construction from the last handoff remains the representation mechanism; do not redo supplied-template hardness or the completed robust-identifier formalization.

Both repository notes rechecked at master `ec3ed3ee020722e366fc05b63ca528ad3f0b5d48`: `sat-search/NOTES_ORIENTATION_QUOTIENT.md` blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2` and `RESEARCH_NOTES.md` blob `88db5dd0ca6fcac530b6926fd39750da044e1769`. Both unchanged. Also inspected `sat-search/lean/CircuitLemmas/Robust.lean` blob `282d83197b43da0592cfc89aba5a6d1f8e88d5ad` and its `three_step` statement/proof. Repository access was read-only. Previous handoff follows in the archive; no request to implement every old proposal.

## 1. An isolated-model lower bound

Let S be a nonempty subset of the n-dimensional Boolean cube, n>=1, with no two members at Hamming distance one. Define f_S as its indicator. In SAT terminology S is the set of **projected ordinary-input models**, not the set of assignments to existential witness variables. Define the minimum isolation number

    t(S) = min{|I| : some assignment on I has exactly one extension in S}.

The empty set of pins is allowed, giving t=0 for a singleton. This is the minimum over models, not the maximum teaching dimension, nor the minimum over all inconsistent assignments. It can be computed by finding a smallest mask on which some row of S has a unique projection.

**Theorem.** Every free-complement fan-in-two AND circuit for f_S satisfies

    C(f_S) >= n - 1 + 2 t(S).

No assumptions on fan-out, sharing, depth, or linearity. The same holds for the complement of f_S. The result concerns a fixed ordinary-input function even if its defining existential projection has a much larger witness space.

Proof. Every coordinate is essential: flip that coordinate in any member of S; the flipped row is not in S. Every nonempty cofactor S_{i=b}, after deleting i, is again independent, and all its remaining coordinates are essential. For n>=2 it is nonconstant, so fixing i in f_S costs at least one gate by `excess_restriction` (with a singleton set of fixed variables). Furthermore t(S_{i=b}) >= t(S)-1: append the pin i=b to a minimum isolator of the residual row. If only one value of i is present in S, then t(S_{i=b})=t(S) since pinning a constant-on-S coordinate cannot help to isolate a model.

Induct on n. At n=1 S is a singleton, t=0 and the indicator is a literal. If n>=2 and some coordinate is constant on S, fix its unique feasible value. The one-gate restriction bound and induction give C>=1+(n-2)+2t(S). Otherwise each coordinate assumes both values in S. Every single-coordinate cofactor is nonempty and independent, hence every remaining coordinate is essential. This is exactly `Strong` on all n ordinary inputs. Apply `three_step` to obtain a restriction of some coordinate to some value with at least three deleted gates. The residual is nonempty regardless of which coordinate/value the lemma chooses, and t drops by at most one. Thus C>=3+(n-2)+2(t(S)-1)=n-1+2t(S). This covers all cases. QED.

The support bound for n essential inputs is n-1. The new term charges two extra gates for each necessary non-forced isolation step. Nonempty restrictions are essential to the argument: a branch which destroys every model can collapse the whole circuit, so we do not charge three gates when there is a forced coordinate. There is no assumption that pins corresponding to the chosen restriction are known to the original circuit.

## 2. Stronger recursive restriction potential

Define q(S) by recursion on dimension. For n=1 put q=0. For n>=2 let Q be the list of q(S_{i=b}) over every nonempty single-coordinate cofactor. Set

    q(S) = max(Q)                                  if some cofactor is empty;
    q(S) = max(max(Q), 1 + min(Q))                 otherwise.

Then

    C(f_S) >= n-1+2q(S).

Proof by induction. Every nonempty child can be selected using the one-gate restriction bound, giving C>=n-1+2q(child), hence the max(Q) branch. If all children are nonempty the three-gate lemma gives at least one child, not a child of our choosing, so C>=n-1+2(1+min(Q)). Both constraints hold at once. At n=1 the bound is zero. This proves the recursion. No enumeration of circuit topologies is needed for the theoretical bound.

Let r(S) be the maximum t of any nonempty coordinate restriction with at least one free coordinate (including S itself). The same excess-restriction lemma gives C>=n-1+2r(S): fixing n-m essential coordinates costs at least n-m when the m-input residual is nonconstant. Alternatively q>=r follows inductively from q>=t and q>=max(Q). The proof of q>=t uses the same two cases as Section 1. In particular

    t(S) <= r(S) <= q(S) <= n-1.

Also q(S) <= floor(log2 |S|). Induct on n: the max-child term cannot exceed the parent cardinality bound, and when all cofactors are nonempty at least one child has at most |S|/2 rows, so 1+min(Q) cannot exceed that bound either. Thus this remains a linear technique; even full parity has q=n-1. It cannot establish a superlinear bound regardless of how hard finding the optimal isolation certificate is.

The proof suggests a small dynamic-programming lower-bound checker over coordinate subcubes. With memoization on truth tables and dimension it computes q exactly (at most 3^n coordinate restrictions of the original table, fewer after cofactor equality merging). This is an optional research certificate; no end-to-end synthesis improvement has been established.

### Examples of strict improvement

Use least-significant truth-table bit for input all zero and bit i of row index for variable i. For n=4, `tt=0x0196` is independent, t=1 and r=q=2, giving 7 gates instead of 5. For n=5, `tt=0x60969409` is independent and t=r=2, but every one of its ten nonempty one-bit cofactors has q=2. Thus q=3 and the recursive lower bound is 10 instead of 8. These are **lower bounds**, not exact minima. A future exact-synthesis comparison could test usefulness on the relevant corpus; do not treat the examples as certified minima.

For a general full-support f on n ordinary inputs, if a coordinate restriction to m>=1 free bits has a nonempty independent accepting or rejecting set S, then C(f)>=n-1+2q(S). The proof fixes the n-m original essential inputs, uses the excess bound, and optionally complements the residual. If only some original inputs are essential, first restrict to the essential support. For monotone f a nonempty independent accepting (or rejecting) set is necessarily a singleton, so this is not a nontrivial lower bound for the full monotone availability function on its entire cube. The previous programmable region can be nonmonotone; this is where the certificate applies.

## 3. Affine-code membership: rank-based bound and tight families

Let H be a binary matrix with n columns, none zero, rank r, and suppose Hx=b is consistent. Its solution set S is an affine subspace of dimension d=n-r. Every solution flipped in any single coordinate leaves S (the corresponding column of H is nonzero). A set of pins can isolate a member exactly if the coordinate projection is injective on the direction space of S. Fewer than d pins cannot suffice by rank-nullity, and d pins suffice by choosing a basis of the coordinate functionals on that direction space. Consequently t(S)=d. Every feasible restriction is affine of dimension at most d, and |S|=2^d, so q(S)=r(S)=t(S)=d. Hence

    C([Hx=b]) >= 3n - 2 rank(H) - 1.

This is an unrestricted AIG gate lower bound, not a bound on XOR-only circuits. It holds with arbitrary shared preprocessing and gate reconvergence. Zero columns can be discarded, and an inconsistent RHS is excluded (constant false).

It is sharp for every n>=1 and 1<=r<=n: partition the n bits into r nonempty blocks and impose one parity equation per block. Each block of size s uses 3(s-1) AND gates to compute parity with free complements. The conjunction of r results uses r-1 ANDs, giving exactly 3(n-r)+r-1 = 3n-2r-1 gates. For r=1 this is the usual parity bound; for r=n it is the minterm bound. For general H, a systematic independent equation basis gives an explicit upper bound 3 times the number of nonpivot coefficient ones plus r-1, but equality with the lower bound need not hold and is not claimed.

This family fits the fixed programmable fork model: use auxiliary XOR gates encoded by their four width-three truth-table clauses to enforce each row parity, and a fixed unit to force each resulting bit. If H has w nonzero entries, the fixed CNF plus pins has O(w+n) literal occurrences. The previous linear-overhead compiler produces O(w+n) vertices, fully genuine on the projected region. For sparse H (w=O(n)), this gives a linear-size template and an unconditional lower bound 3n-2r-1 on its n ordinary-input function. It is not a 3N lower bound in the vertex count N, and the reverse SAT encoding increases length further. Thus this is a calibration family and a proof-of-concept for direct semantic lower bounds on the new projected model, not an improvement to the 2n-o(n) SAT bound.

## 4. Verification performed in this session

The dependency-free reference below was executed. The final run printed:

    n 1 sets by isolation {0: 2}
    n 2 sets by isolation {0: 4, 1: 2} state counts [1, 4, 6, None] known functions 8 target hits 54 tight complement classes 5
    n 3 sets by isolation {0: 8, 1: 24, 2: 2} state counts [1, 12, 114, 994, 8291, None] known functions 119 target hits 97440 tight complement classes 20
    n 4 sets by isolation {0: 16, 1: 536, 2: 188, 3: 2} state counts [1, 24, 468, 8756, None] known functions 1795 target hits 12576 tight complement classes 16
    witness 0x60969409 cofactor potentials [[2, 2], [2, 2], [2, 2], [2, 2], [2, 2]]
    {'exhaustive_restriction_improvements': 64, 'exhaustive_recursive_improvements': 0, 'independent_sets': 784, 'nonempty_cofactors': 5850, 'circuit_target_hits': 110070, 'affine_codes': 540, 'tight_parity_partitions': 1023}
    random parity subsets {'sets': 598, 'restriction_improved': 55, 'recursive_improved': 45}

All assertions passed. The program enumerates every nonempty independent set up to 4 bits, tests cofactor properties and the nested bounds, and enumerates all nonredundant AIG states up to gate budgets 3,5,4 for n=2,3,4 respectively. A state retains the set of available truth tables modulo complement; a duplicate/constant gate can be bypassed, and equal available sets have identical possible continuations. This enumeration checks all output hits at the indicated budgets against the strongest recursive bound. Hits count repeated candidate gate outputs, not distinct circuits or distinct functions. The final frontier need not be stored (`None`). `known functions` counts complement classes, including constants and input literals; it does not mean all functions were synthesized at n=3 or n=4. `tight complement classes` counts exact agreement with a found minimum within the budget. The sampled n=5,6 sets are random subsets of even parity, not uniform independent sets; their improvement counts do not estimate a general population rate. The affine test checks nonzero columns, rank, cardinality and the isolation number on 540 seeded consistent systems of n=2..10. The parity partition test checks all 1023 contiguous block partitions for n=1..10, evaluates explicit three-AND XOR and merge constructions as truth tables, and checks their gate counts against the lower bound. The infinite theorem is the induction in Sections 1-3, not the finite tests. No Lean build or native solver benchmark was performed for this result.

## 5. Runnable reference (`isolation_bound_check.py`)

```python
from itertools import combinations, product
from collections import Counter
from random import Random
from functools import lru_cache

def rows(tt,n): return [x for x in range(1<<n) if tt>>x&1]
def independent(tt,n):
    return all(not (tt>>(x^(1<<i))&1) for x in rows(tt,n) for i in range(n))
def restrict(tt,n,i,b):
    return sum(((tt>>((x&((1<<i)-1)) | (b<<i) | ((x>>i)<<(i+1))))&1)<<x for x in range(1<<(n-1)))
def essential(tt,n,i): return restrict(tt,n,i,0)!=restrict(tt,n,i,1)
def isolate(tt,n):
    rr=rows(tt,n); assert rr
    for k in range(n+1):
        for bits in combinations(range(n),k):
            mask=sum(1<<i for i in bits)
            if 1 in Counter(x&mask for x in rr).values(): return k
    raise AssertionError

def canon(tt,n): return min(tt,tt^((1<<(1<<n))-1))
def bound(tt,n): return n-1+2*isolate(tt,n)

# Every nonredundant AIG up to maxg, retaining its set of available functions.
def circuit_screen(n,maxg,targets):
    full=(1<<(1<<n))-1
    prim=[canon(sum(1<<x for x in range(1<<n) if x>>i&1),n) for i in range(n)]
    states={tuple(sorted(prim))}; costs={0:0,**{x:0 for x in prim}}; counts=[1]; checked=0
    for k in range(1,maxg+1):
        new=set()
        for st in states:
            present=set(st)
            for a,b in combinations(st,2):
                for aa,bb in product((a,a^full),(b,b^full)):
                    c=canon(aa&bb,n)
                    if c==0 or c in present: continue
                    if c not in costs: costs[c]=k
                    if c in targets:
                        checked+=1
                        assert k>=targets[c], (n,k,c,targets[c])
                    if k<maxg: new.add(tuple(sorted((*st,c))))
        counts.append(len(new) if k<maxg else None)
        states=new
    return costs,counts,checked

def rank(vs):
    basis={}
    for v in vs:
        while v:
            k=v.bit_length()-1
            if k in basis:v^=basis[k]
            else:basis[k]=v;break
    return len(basis)

def affine_tt(cols,rhs):
    n=len(cols); out=0
    for x in range(1<<n):
        s=0
        for i,a in enumerate(cols):
            if x>>i&1:s^=a
        if s==rhs:out|=1<<x
    return out

@lru_cache(None)
def tmax(tt,n):
    q=isolate(tt,n)
    if n<=1:return q
    return max([q]+[tmax(u,n-1) for i in range(n) for b in (0,1) if (u:=restrict(tt,n,i,b))])
@lru_cache(None)
def potential(tt,n):
    if n<=1:return 0
    cs=[restrict(tt,n,i,b) for i in range(n) for b in (0,1)]
    qs=[potential(u,n-1) for u in cs if u]
    return max(qs+([1+min(qs)] if all(cs) else []))

def parity_partition_aig(n,cols):
    full=(1<<(1<<n))-1
    gate_count=0
    def AND(a,b):
        nonlocal gate_count
        gate_count+=1
        return a&b
    def XOR(a,b):
        return full^AND(full^AND(a,full^b),full^AND(full^a,b))
    acc=[]
    for i,c in enumerate(cols):
        a=sum(1<<x for x in range(1<<n) if x>>i&1)
        j=c.bit_length()-1
        if j==len(acc):acc.append(a)
        else:acc[j]=XOR(acc[j],a)
    f=full^acc[0]
    for a in acc[1:]:f=AND(f,full^a)
    return f,gate_count

def main():
    total=Counter()
    for n in range(1,5):
        targets={}; cnt=Counter(); eq=0
        for tt in range(1,1<<(1<<n)):
            if not independent(tt,n):continue
            t=isolate(tt,n); r=tmax(tt,n); q=potential(tt,n)
            assert t<=r<=q<=n-1
            total['exhaustive_restriction_improvements']+=r>t
            total['exhaustive_recursive_improvements']+=q>r
            L=n-1+2*q
            cnt[t]+=1; total['independent_sets']+=1
            c=canon(tt,n);targets[c]=max(targets.get(c,0),L)
            for i in range(n):
                assert essential(tt,n,i)
                cs=[restrict(tt,n,i,b) for b in (0,1)]
                for b,u in enumerate(cs):
                    if not u:continue
                    assert independent(u,n-1)
                    assert isolate(u,n-1)>=t-1
                    if not cs[1-b]:assert isolate(u,n-1)==t
                    for j in range(n-1):assert essential(u,n-1,j)
                    total['nonempty_cofactors']+=1
        if n>=2:
            maxg={2:3,3:5,4:4}[n]
            costs,states,checks=circuit_screen(n,maxg,targets)
            eq=sum(costs.get(c)==L for c,L in targets.items())
            total['circuit_target_hits']+=checks
            print('n',n,'sets by isolation',dict(sorted(cnt.items())),'state counts',states,'known functions',len(costs),'target hits',checks,'tight complement classes',eq,flush=True)
        else: print('n',n,'sets by isolation',dict(cnt),flush=True)
    rng=Random(62026)
    for n in range(2,11):
        for _ in range(60):
            r=rng.randrange(1,n+1)
            cols=[rng.randrange(1,1<<r) for i in range(n)]
            x=rng.randrange(1<<n);rhs=0
            for i,a in enumerate(cols):
                if x>>i&1:rhs^=a
            tt=affine_tt(cols,rhs); d=n-rank(cols)
            assert independent(tt,n)
            assert tt.bit_count()==1<<d
            assert isolate(tt,n)==d
            total['affine_codes']+=1
    for n in range(1,11):
        for cuts in range(1<<(n-1)):
            cols=[]; j=0
            for i in range(n):
                cols.append(1<<j)
                if cuts>>i&1:j+=1
            r=j+1
            tt=affine_tt(cols,0)
            assert 3*(n-r)+r-1==bound(tt,n)
            got,g=parity_partition_aig(n,cols)
            assert got==tt and g==bound(tt,n)
            total['tight_parity_partitions']+=1
    rng=Random(444); sample=Counter()
    for n in (5,6):
        for j in range(300):
            p=rng.uniform(.2,1)
            tt=sum(1<<x for x in range(1<<n) if x.bit_count()%2==0 and rng.random()<p)
            if not tt:continue
            t=isolate(tt,n);r=tmax(tt,n);q=potential(tt,n);assert t<=r<=q<=n-1
            sample['sets']+=1;sample['restriction_improved']+=r>t;sample['recursive_improved']+=q>r
    tt=0x60969409; n=5
    assert (isolate(tt,n),tmax(tt,n),potential(tt,n))==(2,2,3)
    print('witness',hex(tt),'cofactor potentials',[[potential(restrict(tt,n,i,b),n-1) for b in (0,1)] for i in range(n)])
    print(dict(total),flush=True)
    print('random parity subsets',dict(sample),flush=True)
if __name__=='__main__':main()
```

## 6. Next work

If formalizing, prioritize the short cofactor-independence and isolation-number lemmas, then combine the existing `three_step` and `excess_restriction` results by induction. The strongest recursive potential is optional; do not redo the robust SAT formalization. If benchmarking, compare the actual new lower endpoints against already verified exact minima, and record both the cost of computing the potential and changes to certified intervals. The small enumerations above establish no production speedup.

For L-clb-036 the limitation is fundamental to this accounting: q<=n-1. Repeatedly refining a one-coordinate elimination strategy will not by itself produce a superlinear lower bound. The outstanding target is a semantic restriction argument with a genuinely superlinear potential, or a new quantitative bridge that makes a stronger restricted-model lower bound apply to unrestricted circuits. The isolated-model geometry offers a rigorous linear baseline for such a theory; it is not evidence that the remaining superlinear step is close.

---

# Earlier research archive (historical; current priorities above)

# Research handoff — fixed programmable, fully genuine fork templates

## 0. Status and task

New result first. The agent's supplied-template hardness reduction in `sat-search/results/fork_mode_core/README.md` is already in the repository and need not be implemented again. The new theorem below lifts its structural properties to a **single fixed template per source CNF**, simultaneously for every input of a prescribed literal projection. This closes the fixed-template *representation* gap, not the circuit lower-bound gap. No novelty claim. No new Lean result, exact synthesis budget, or production solver improvement.

Both requested notes rechecked at master `ec3ed3ee020722e366fc05b63ca528ad3f0b5d48`: `sat-search/NOTES_ORIENTATION_QUOTIENT.md` blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`; `RESEARCH_NOTES.md` blob `88db5dd0ca6fcac530b6926fd39750da044e1769`. Both unchanged. Also inspected `sat-search/results/fork_mode_core/README.md`, blob `65b938cc2d92852d9e00c1feeb6ef54e9dbf2868`. The strongest checked SAT bound remains 2n-o(n) along multiples of six, as reported by the repository. Do not repeat the completed robust-identifier formalization. All repository access was read-only. The older sections are retained as historical research, not a request to reimplement their filters or reprove checked results.

## 1. Statement and precise scope

Let F be a fixed CNF of width at most three, on existential variables y, including variables v_1,...,v_p. Consider the ordinary-input function

    f(x) = SAT(F AND conjunction_{j=1}^p [v_j = x_j]).

The v_j may repeat, and source variables not occurring in F or the pins may be discarded. Let L be the number of literal occurrences of F. If F has an empty clause, the function is identically false and may be replaced by any fixed contradictory pair of units; below use a nonempty-clause source (an empty *family* of clauses is fine).

**Theorem.** There is one fixed independent-transversal template T, with O(L+p) vertices, whose conflict graph has only disjoint edges P2 and three-vertex paths P3, and whose groups have size at most three, and a fixed literal projection a(x) into its availability coordinates, such that:

* T(a(x)) = f(x) for every x. Every availability coordinate is a constant 1, x_j, or NOT x_j. No gates are needed for the projection in the free-complement AIG model.
* All P3 vertices are available at every projected input. Only matching-edge endpoint availability is programmable. Both endpoints of each matching edge always have equal availability on the projection.
* On every projected input, the matching background consists of trees, each requiring exactly one additional fork resource. Each fork supplies three distinct deficient components, so it remains genuine after both matching contractions and dominated-mode elimination.
* The resulting mode CNF has exactly one positive and two negative occurrences per mode variable, in three distinct clauses. All clauses have width two or three, with distinct variables, and any two clauses intersect in at most one variable. Thus no units or pure literals appear.
* For each fixed x, the mode models correspond bijectively to satisfying assignments of the occurring source variables, with the pins imposed. This bijection is about mode assignments, not the number of independent transversals of the uncontracted graph.

The promise is the **image of a(x)**, not the whole independent availability cube. Outside this image, e.g. if a slot has neither of its two possible routing edges available, the mode CNF may have units or simplified forks. The theorem is sufficient for transferring arbitrary deterministic circuit lower bounds: a circuit computing T on the entire cube also computes its restriction on this image; a circuit computing T only on the promise likewise computes f. It does not prove hardness on the full cube or any lower bound beyond the representation reduction.

## 2. Balanced programmable forcing gadget

For a source literal l, introduce fresh z,w and replace the unit (l) by

    (l OR z), (l OR NOT z), (NOT l OR z), (NOT l OR w).

The first two clauses force l true, then the last two force z=w=true. There is a unique extension. The important difference from the agent's three-clause gadget is that l has two positive-role and two negative-role occurrences (relative to its literal phase). The roles can be kept fixed even when the sign to force is an input.

For pin j, start with l=v_j. If x_j=1, use the four clauses above. If x_j=0, swap the v_j literal slots between clauses 1 and 3, and between clauses 2 and 4 (numbered from one). This produces exactly the same gadget for NOT v_j. All literal occurrence roles and their signs remain fixed; only their clause destinations change. Each movable slot has two possible destinations, and each destination contains one of a designated pair of slots. The auxiliary literal positions never move. Fixed source units can also use the gadget, without switches. Normalize an empty clause to a fresh contradictory pair of units if needed. Write L' for the normalized literal count; for sources without empty clauses L' <= 8L+8p.

## 3. Fixed copy variables, fixed signs, and fixed links

Use the agent's three-replica copy construction, but create copy variables for **occurrence roles**, not for the input-dependent literal positions. Each role has three copies indexed by replica 0,1,2. For each original variable, order its copies first by role and then by replica, and impose a directed implication cycle equating all their decoded values. Every cycle has length at least three; adjacent copies have different replica indices, including wraparound. Each role copy participates in exactly one replicated source/gadget clause (possibly at either of two anchors within the same replica) and two fixed link clauses. Complement copies whose original role was positive, so that every replicated-clause occurrence becomes negative in the mode variable, and the two link occurrences are one positive and one negative. This gives fixed polarity on all mode slots, independent of x.

For every projected input the cycles enforce equality of decoded copies; the replicated clauses enforce the original F and the pinned units. The balanced gadget auxiliaries are uniquely forced, and the cycles make the copy extension unique. Inactive original variables are omitted, not counted as additional models. The converse is immediate by decoding one copy of each occurring original variable. Each clause's variables are distinct even when a source clause repeats a variable, because its literal occurrences have distinct copies. Different replicated clauses share no copy. Two link clauses share at most one copy because the cycles have length >=3. A link clause has endpoints in different replica indices, so intersects a replicated clause in at most one copy even after swaps. All clauses are width two or three; each variable appears once positively and twice negatively, with these occurrences in distinct clauses.

## 4. Realize programmable destinations by matching edges

Make a group (anchor) for every replicated clause and every link clause. For each mode literal occurrence create a separate slot group containing its fork vertex. Assemble the three fork vertices belonging to one mode variable into a P3 component, center = positive, leaves = negative. Every fork vertex is available, permanently.

For each possible destination of a slot, create a separate P2 conflict component (one endpoint in the slot group, one in its clause anchor). If the destination is fixed, both endpoints are always available; if it is switched, both endpoints have availability x_j or NOT x_j, as appropriate. Every vertex belongs to just one conflict component. A fixed slot group has two vertices, and a movable slot group has three. A fixed clause anchor has width two or three and that many vertices. A switched clause anchor has two possible endpoints for its movable position and one endpoint for its fixed auxiliary position, hence has three vertices. Link anchors have two vertices. No group exceeds three.

On a projected input, every slot has exactly one available routing edge and every anchor has exactly its required two or three active incident edges. Unavailable edges have both endpoints unavailable, never an unmatched private resource. The active matching resource graph on groups is therefore a disjoint union of stars, with one anchor and s slot groups, s in {2,3}. There are s shared resources for s+1 groups and no private resource. It is impossible to cover the star without at least one fork resource. Conversely, if a fork vertex is usable at any slot group, root the star at that slot and assign each shared resource to the group farther from the root. Every other group is covered, and the root uses its fork vertex. This is also a direct proof of the first contraction on these templates (no generic connectivity algorithm needed).

A fork has three distinct clause anchors by Section 3. Both leaves are compatible with each other, whereas the center conflicts with both. Thus a mode assignment that satisfies every mode clause can select an available fork resource at one slot of each star, and assign the ordinary resources as above. Conversely an independent transversal covers each star using at least one fork vertex. Its selected fork vertices extend to a mode choice: choose center if selected, otherwise leaves (arbitrary choice for unused forks). The chosen modes satisfy the contracted clauses. This proves exact graph feasibility and shows the first contraction leaves all forks genuine. No fork is dominated or degenerates to an ordinary edge/private option, so the second contraction changes nothing; units and pure-literal rules also do nothing.

### Exact size accounting

Let C' be the normalized clause count, K=3L' the number of mode variables. There are 3K literal slots, 3C'+K anchors, and 3K+12p possible routing edges, since each pin has four movable occurrence roles in three replicas and each such slot gains one extra possible destination. Each slot contains one fork vertex, and every possible routing edge adds two endpoint vertices. Hence

    N = 3K + 2(3K+12p) = 9K+24p = 27L'+24p,
    groups = 3C'+4K.

Each pin controls 12 movable slots, each with two routes and two endpoints per route: exactly 24 x_j and 24 NOT x_j availability vertices. In the pins-only case (no F), N=240p, K=24p, groups=108p. The constants are not optimized. In particular this is not a proposal to accelerate small-instance SAT solving.

## 5. Exact reverse encoding and exponent transfer

For any constructed T on N vertices, introduce a selector variable s_v for each vertex, require at least one selector in each group, and include (NOT s_u OR NOT s_v) for each conflict edge. It is unnecessary to require at most one selected in each group: deleting additional choices preserves independence and availability. For availability x_j or NOT x_j, introduce a source-pin variable t_j, include (NOT s_v OR t_j) or (NOT s_v OR NOT t_j), and pin t_j to x_j with one programmable unit-clause sign. Constant available vertices need no such clauses. This construction has O(N) literal occurrences (degree <=2, group size <=3, and p <= N), width at most three, and no repeated programmable signs. Renumber variables to positive identifiers <= N+p. The external exact SAT encoding uses O(log(N+2)) bits per literal, so the total length is O(N log(N+2)). Every x_j controls exactly one sign coordinate; all other encoded bits are fixed. This is a genuine coordinate restriction of SAT, not merely a projection with duplicated inputs. The proof uses the same encoding grammar as the prior handoff (1, sign), then canonical least-significant-first identifier digits as (1, digit), then (0,1), and clause delimiter (0,0). Only nonzero identifiers are needed.

Define T(S) as maximum deterministic AIG size of SAT at lengths <=S, and J(S) as maximum deterministic AIG size of the **projected ordinary-input functions** of these fixed programmable templates with <=S vertices (not the size of a circuit that must handle all independent availability assignments). Let D(S) be the prior worst-case deterministic AIG size of functions having nondeterministic circuits of total size <=S, including used inputs and witnesses. The new compilation and standard gate-consistency CNF give D(S) <= J(O(S)), and the reverse encoding gives J(S) <= T(O(S log(S+2))). The earlier verifier bridge, conditional only on its previously supplied construction/proof, gives T(S) <= D(O(S log^2(S+2))). Together these inequalities preserve the worst-case polynomial exponent, i.e. the limsup of log(1+size)/log S, including infinite exponent. They do not preserve exact Big-O at exponent 1.01. A fixed positive exponent gap above 1.01 for J would suffice for L-clb-036. In particular a lower bound Omega(N^(1.01+epsilon)) on a family of projected functions would transfer at lengths O(N log N). Conversely no small graph or easy background alone supplies such a lower bound. The full independent availability function is monotone, but its literal projection need not be; all lower bounds here must apply to unrestricted AIGs, not only monotone circuits.

This is a representation theorem, not a proof that any individual family has a superlinear lower bound. It explicitly addresses the earlier agent caveat that supplied-template NP-hardness only certified one all-available point per template. Here one graph and partition cover all ordinary inputs, with genuine cores throughout the specified promise. Further supplied-template NP-hardness refinements or faster exponential branching do not establish L-clb-036.

## 6. Executed verification

The embedded program below uses ordinary Python DPLL for small source formulas, and independent Z3 SAT checks for the contracted CNFs and the original graph constraints. It also compares source-model truth by exhaustive enumeration for a subset of cases, checks unique mode extensions by a blocking clause, and independently decodes the exact SAT bit strings. All checks on the final run passed:

    {'templates': 185, 'max_vertices': 1557, 'projection_checks': 539,
     'slot_checks': 129087, 'unique_extensions': 318,
     'source_assignment_checks': 2076, 'encoded_checks': 66}
    pins 1 forks 24 vertices 240 groups 108
    pins 2 forks 48 vertices 480 groups 216
    pins 4 forks 96 vertices 960 groups 432
    pins 8 forks 192 vertices 1920 groups 864
    pins 16 forks 384 vertices 3840 groups 1728

Projection checks include all 16 subsets of the four two-variable binary clauses with both variables pinned, nine edge-case templates (including empty CNF, empty clause, fixed units, repeated literals and repeated pins), and 160 seeded random templates. All input assignments of each sampled template are enumerated. The slot count is the total mode literal slots examined across these input cases, not a count of independent SAT calls. The unique-extension checks count successful source-assignment extensions (unused original variables can duplicate a test). The encoded checks verify length invariance, one changed sign position per changed input bit, decoding round trip, and satisfiability. The direct graph SAT constraints are generated without contraction; Z3 is shared as a backend for the larger formulas, so these are separate encodings, not two independently implemented large SAT solvers. No proof certificates were emitted, and no exact AIG size or Lean verification was performed.

Initial replay with elementary DPLL on the large auxiliary graph formulas exceeded the 200 s tool cap. The revised run used the installed `libz3.so.4` through Python ctypes (no Python z3 package required). The code's source formula oracle remains the original DPLL implementation. On other systems change the library name/path to the local Z3 shared library. The reference compiler is proof-oriented and not a production solver.

## 7. Runnable reference (`fixed_fork_check.py`)

```python
from itertools import product
from collections import defaultdict, Counter
from random import Random

# Literal truth with a total assignment indexed by positive variable ID.
def truth(l, a): return a[abs(l)] == (l > 0)
def eval_cnf(f,a): return all(any(truth(l,a) for l in c) for c in f)

def sat(f, assumptions=()):
    # Independent elementary DPLL, no knowledge of compiler or resources.
    f = [frozenset(c) for c in f] + [frozenset([l]) for l in assumptions]
    f = [c for c in f if not any(-l in c for l in c)]
    def go(f,a):
        while True:
            if not f: return a
            c=min(f,key=len)
            if not c: return None
            if len(c)>1: break
            l=next(iter(c)); a[abs(l)]=l>0
            f=[c-{-l} for c in f if l not in c]
        l=min(c,key=lambda l:(abs(l),l))
        for u in (l,-l):
            b=dict(a); b[abs(u)]=u>0
            r=go([c-{-u} for c in f if u not in c],b)
            if r is not None:return r
        return None
    return go(f,{})

import ctypes as C
import re
z=C.CDLL('libz3.so.4'); P=C.c_void_p; I=C.c_int; S=C.c_char_p
for name,rest,args in [('Z3_mk_config',P,[]),('Z3_mk_context_rc',P,[P]),('Z3_del_config',None,[P]),('Z3_mk_solver',P,[P]),('Z3_solver_inc_ref',None,[P,P]),('Z3_solver_dec_ref',None,[P,P]),('Z3_solver_from_string',None,[P,P,S]),('Z3_solver_check',I,[P,P]),('Z3_solver_get_model',P,[P,P]),('Z3_model_to_string',S,[P,P])]:
 f=getattr(z,name);f.restype=rest;f.argtypes=args
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context_rc(cfg);z.Z3_del_config(cfg)

def sat_z3(f,assumptions=()):
    f=list(f)+[(l,) for l in assumptions]
    variables=sorted({abs(l) for c in f for l in c})
    def lit(l):return f'v{l}' if l>0 else f'(not v{-l})'
    commands=[f'(declare-const v{v} Bool)' for v in variables]
    commands += ['(assert '+('false' if not c else lit(c[0]) if len(c)==1 else '(or '+' '.join(map(lit,c))+')')+')' for c in f]
    s=z.Z3_mk_solver(ctx);z.Z3_solver_inc_ref(ctx,s)
    try:
        z.Z3_solver_from_string(ctx,s,'\n'.join(commands).encode())
        result=z.Z3_solver_check(ctx,s)
        assert result in (-1,1), 'solver unknown'
        if result==-1:return None
        model=z.Z3_model_to_string(ctx,z.Z3_solver_get_model(ctx,s)).decode()
        return {int(v):b=='true' for v,b in re.findall(r'v(\d+) -> (true|false)',model)}
    finally:z.Z3_solver_dec_ref(ctx,s)

# Source: fixed width <=3 CNF and input j pins variable pins[j-1].
# Constant fixed units normalized by same balanced gadget; empty clause -> contradiction.
def compile_template(n,f,pins):
    clauses=[]; swaps=[]; fresh=n
    def forcing(l,j=None):
        nonlocal fresh
        z,w=fresh+1,fresh+2;fresh+=2
        t=len(clauses)
        clauses.extend([(l,z),(l,-z),(-l,z),(-l,w)])
        if j is not None: swaps.extend([(t,t+2,j),(t+1,t+3,j)])
    for c in f:
        assert len(c)<=3
        if not c:
            fresh+=1; v=fresh;forcing(v);forcing(-v)
        elif len(c)==1:forcing(c[0])
        else: clauses.append(tuple(c))
    for j,v in enumerate(pins,1):forcing(v,j)
    # Occurrence-role -> replica copies. Each role has stable original sign.
    roles=[]; switch={}
    for a,b,j in swaps:switch[a]=(b,j);switch[b]=(a,j)
    C=len(clauses); anchors=3*C
    by_var=defaultdict(list); info={}; slots=[]; K=0
    for a,c in enumerate(clauses):
        for h,l in enumerate(c):
            for r in range(3):
                K+=1; v=K; by_var[abs(l)].append(v);info[v]=l
                dest=[(3*a+r,None)]
                if h==0 and a in switch:
                    b,j=switch[a];dest=[(3*a+r,j),(3*b+r,-j)]
                slots.append((-v,dest));roles.append((a,h,r,v))
    # Link clauses; decoded original copy = -mode for positive role, mode otherwise.
    def dec(v):return -v if info[v]>0 else v
    for vv in by_var.values():
        assert len(vv)>=3
        for u,v in zip(vv,vv[1:]+vv[:1]):
            slots.extend([(-dec(u),[(anchors,None)]),(dec(v),[(anchors,None)])]);anchors+=1
    groups=[[] for _ in range(anchors+len(slots))]; av=[None]; edges=[]; matching=[]; fork=defaultdict(dict); sv=[]
    def vertex(g,c):
        v=len(av);av.append(c);groups[g].append(v);return v
    for i,(l,dest) in enumerate(slots):
        g=anchors+i;v=vertex(g,None);sv.append(v)
        fork[abs(l)].setdefault(l>0,[]).append(v)
        for a,c in dest:
            u=vertex(g,c);w=vertex(a,c);edges.append((u,w));matching.append((g,a,u,w))
    for d in fork.values():
        assert len(d[True])==1 and len(d[False])==2
        edges.extend((d[True][0],v) for v in d[False])
    assert all(1<=len(g)<=3 for g in groups)
    assert len({v for g in groups for v in g})==len(av)-1
    return dict(clauses=clauses,swaps=swaps,roles=roles,info=info,by_var=by_var,slots=slots,anchors=anchors,K=K,groups=groups,av=av,edges=edges,matching=matching,sv=sv,source_n=n,pins=pins)

def contract(t,x):
    a=[False]+[l is None or truth(l,x) for l in t['av'][1:]]
    ng=len(t['groups']);parent=list(range(ng)); degree=[0]*ng
    def root(u):
        while parent[u]!=u:u=parent[u]
        return u
    for g,h,u,v in t['matching']:
        assert a[u]==a[v]
        if a[u]:
            assert root(g)!=root(h)
            parent[root(g)]=root(h);degree[g]+=1;degree[h]+=1
    anchors=t['anchors'];out=[[] for _ in range(anchors)]
    for g in range(anchors):assert root(g)==g and degree[g] in (2,3)
    for i,(l,_) in enumerate(t['slots']):
        g=anchors+i;assert degree[g]==1 and a[t['sv'][i]]
        out[root(g)].append(l)
    assert all(len(c) in (2,3) and len(set(map(abs,c)))==len(c) for c in out)
    # Fully genuine, distinct clause labels per fork, exact 1+/2- occurrences.
    cnt=Counter(l for c in out for l in c)
    assert all(cnt[v]==1 and cnt[-v]==2 for v in range(1,t['K']+1))
    pairs=set()
    for c in out:
        for i,u in enumerate(c):
            for v in c[i+1:]:
                p=tuple(sorted((abs(u),abs(v))));assert p not in pairs;pairs.add(p)
    return out,a

def direct_graph(t,a):
    # Independent group/conflict encoding; no contraction.
    f=[tuple(v for v in g if a[v]) for g in t['groups']]
    f += [(-u,-v) for u,v in t['edges'] if a[u] and a[v]]
    return sat_z3(f) is not None

def verify(n,f,pins,stats,full=False):
    t=compile_template(n,f,pins);stats['templates']+=1
    stats['max_vertices']=max(stats['max_vertices'],len(t['av'])-1)
    for bits in product((False,True),repeat=len(pins)):
        x=dict(enumerate(bits,1));units=[(v if x[j] else -v,) for j,v in enumerate(pins,1)]
        source=f+units; expected=sat(source) is not None
        mode,a=contract(t,x);got=sat_z3(mode) is not None
        assert got==expected
        assert direct_graph(t,a)==expected
        stats['projection_checks']+=1;stats['slot_checks']+=len(t['slots'])
        # Each pin bit controls exactly 24 positive and 24 negative availability vertices.
        counts=Counter(l for l in t['av'] if l is not None)
        assert all(counts[j]==counts[-j]==24 for j in x)
        if full:
            for vals in product((False,True),repeat=n):
                src=dict(enumerate(vals,1));want=eval_cnf(source,src)
                assumptions=[]
                for v in range(1,n+1):
                    if v not in t['by_var']:continue # absent variables are irrelevant
                    u=t['by_var'][v][0]; decoded=-u if t['info'][u]>0 else u
                    assumptions.append(decoded if src[v] else -decoded)
                m=sat_z3(mode,assumptions);assert (m is not None)==want
                if m is not None:
                    # Complete model if DPLL returned a partial one; unique extension test.
                    m={v:m.get(v,False) for v in range(1,t['K']+1)}
                    assert eval_cnf(mode,m)
                    block=tuple(-v if b else v for v,b in m.items())
                    assert sat_z3(mode+[block],assumptions) is None
                    stats['unique_extensions']+=1
                stats['source_assignment_checks']+=1
    return t

# Exact SAT string encoding, using one programmable unit sign per external bit.
def enc(f):
    out=[]
    for c in f:
        for v,p in c:
            out.extend((1,int(p)))
            while v:out.extend((1,v&1));v>>=1
            out.extend((0,1))
        out.extend((0,0))
    return out

def decode(s):
    f=[];c=[];i=0
    while i<len(s):
        a,b=s[i:i+2];i+=2
        if (a,b)==(0,0):f.append(tuple(c));c=[];continue
        assert a==1;sign=bool(b);v=0;w=0;last=None
        while s[i]==1:
            last=s[i+1];v|=last<<w;w+=1;i+=2
        assert s[i:i+2]==[0,1] and (last is None or last==1);i+=2
        c.append(v if sign else -v)
    assert not c
    return f

def sat_projection(t,x):
    # Variables 1..V select vertices. V+j is pinned to input j.
    V=len(t['av'])-1; f=[tuple(g) for g in t['groups']]
    f += [(-u,-v) for u,v in t['edges']]
    f += [(-v, (V+abs(l)) if l>0 else -(V+abs(l))) for v,l in enumerate(t['av']) if l is not None]
    f += [(V+j if x[j] else -(V+j),) for j in sorted(x)]
    word=enc([[(abs(l),l>0) for l in c] for c in f]);d=decode(word)
    assert d==f
    return word,d

def main():
    rng=Random(61421);stats=Counter();examples=[]
    # Every 2-variable binary clause subset, both variables pinned.
    candidates=[(a,b) for a,b in product((1,-1),(2,-2))]
    for mask in range(16):
        f=[c for i,c in enumerate(candidates) if mask>>i&1]
        verify(2,f,[1,2],stats,full=True)
    for f,pins in [([],[]),([()],[]),([(1,)], [1]),([(-1,)], [1]),([(1,-1)], [1]),([(1,1)], [1]),([], [1,1]),([], [1,2]), ([(1,2,3)], [1,2,3])]:
        verify(3,f,pins,stats,full=True)
    for i in range(160):
        n=rng.randrange(1,6);f=[]
        for _ in range(rng.randrange(0,7)):
            f.append(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4))))
        pins=rng.sample(range(1,n+1),rng.randrange(min(3,n)+1));t=verify(n,f,pins,stats,full=i<45)
        if i<24:
            base=None
            for bits in product((False,True),repeat=len(pins)):
                x=dict(enumerate(bits,1));word,d=sat_projection(t,x)
                if base is None:base=word
                else:
                    # Exactly one bit per changed source bit, because each pin has one unit.
                    assert sum(a!=b for a,b in zip(base,word))==sum(bits)
                assert len(base)==len(word)
                assert (sat_z3(d) is not None)==(sat(f+[(v if x[j] else -v,) for j,v in enumerate(pins,1)]) is not None)
                stats['encoded_checks']+=1
    print(dict(stats))
    for n in [1,2,4,8,16]:
        t=compile_template(n,[],list(range(1,n+1))); print('pins',n,'forks',t['K'],'vertices',len(t['av'])-1,'groups',len(t['groups']))
if __name__=='__main__':main()
```

## 8. Next useful research question

Now the persistent-genuine fixed-template representation is available, further refinements of the representation alone are unlikely to deliver L-clb-036. A useful next step is to investigate unrestricted circuit lower-bound mechanisms for the ordinary-input functions of these fixed templates, or to identify a quantitative theorem whose hypothesis can be established using the graph structure. Do not infer circuit complexity from the number of genuine forks, high incidence treewidth, source NP-hardness, or DPLL runtime. If exploring the incidence graph, test candidate lower-bound measures on the known quasi-linear negative controls in the archive first. The 2n-o(n) checked SAT lower bound remains the substantive lower-bound result; no stronger one is claimed here.

---

# Earlier research archive

The following prior handoffs are retained for continuity. Their historical status and next-step sections are superseded by the current status and priorities above. They are not an instruction to redo previously integrated work.

# Research handoff — Fibonacci branching circuits for genuine fork kernels

New section first. The only new implementation is the compressed-core reference circuit and its semantic cross-checks. This is a deterministic circuit **upper bound**, not a lower bound, and not an improvement to native exact synthesis. Prior material follows as historical research; do not redo completed Lean work or implement every old filter.

## 0. Repository status and independent agent progress

Both requested notes fetched at master `ec3ed3ee020722e366fc05b63ca528ad3f0b5d48` after the experiments. Orientation blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2` (unchanged); research notes blob `88db5dd0ca6fcac530b6926fd39750da044e1769` (updated). The new agent report `sat-search/results/fork_mode_core/README.md` was inspected, along with the SAT bounds notes. It proves a linear-size parsimonious reduction to fully genuine fork mode cores: all variables have exactly one positive and two negative occurrences in distinct clauses, every clause has width two or three, every pair of clauses intersects in at most one variable, and matching contractions, pure-literal elimination and unit propagation leave the entire core intact. The agent's reduction is NP-hardness with the template supplied as input; the construction realizes one all-available input per template, so it does not prove fixed-template circuit hardness. It also independently proves the long-clause Hall observation used below, and the deficiency inequality (a Hall-deficient set of deficit delta contains at least 3 delta binary clauses for width-two/three instances). These observations are already in the repository. Our new contribution is the uniform fixed-topology circuit construction below, its refined exponent, and the degree-weighted sufficient test. No novelty claim; no independent Lean replay or repository changes. The checked SAT lower bound remains 2n-o(n) on multiples of six.

## 1. Hall terminal rule and exact branching

Use the preceding fork-kernel reduction. For every fixed availability input, the matching background yields a mode CNF on at most k variables, each with at most one positive and two negative occurrences. A variable may be unused; every literal occurrence is in one of the three fork slots. Use at most 3k rows (one per distinct deficient component with an available fork slot), plus a flag for an uncovered deficient component. Discard tautological clauses and deduplicate literals. Empty clauses reject. Importantly, do **not** create a separate active clause for each slot of one component; that would duplicate occurrences and invalidate the Hall premise. The circuit below uses the first active slot for each label as representative, then represents that clause by a 2k-bit presence row.

If every remaining clause has at least three distinct variables, the formula is satisfiable. Indeed, each set S of clauses sends at least 3|S| edges to its neighboring variables in the clause-variable incidence graph. Each variable receives at most three edges, so the number of neighboring variables is at least |S|. Hall's theorem gives a distinct variable for every clause. Set the matched variable to satisfy its clause, and assign unmatched variables arbitrarily. This proof remains true after any restriction, since restriction only removes occurrences. The empty family of clauses is satisfiable as well. This is the agent's already recorded Hall observation.

If there is no empty clause but some short clause remains, choose a unit or binary clause. For a unit (a), restrict a=true. For a binary clause (a OR b), use the exact identity

    SAT(F) = SAT(F | a=true) OR SAT(F | a=false,b=true).

The literals in a binary clause are on distinct variables (tautologies removed, duplicates merged). The left branch eliminates one variable, the right branch eliminates two. Other clauses are restricted in the usual way, deleting satisfied clauses and removing falsified literals. No new occurrences are created. This proves that the worst-case size of the unrolled branching tree with n remaining variables is bounded by the recurrence T(0)=1, T(1)<=2, T(n)<=1+T(n-1)+T(n-2). Thus T(n)=O(phi^n), phi=(1+sqrt(5))/2=1.6180339887..., instead of 2^n full assignment leaves.

## 2. Fixed-topology deterministic AIG theorem

The branch rule alone is a RAM/time algorithm. To get a circuit bound we explicitly unroll a fixed tree, and retain original k columns even in descendants with a lower remaining-variable budget. A state is 3k rows, each consisting of an active flag and 2k presence bits ordered +1,-1,+2,-2,...,+k,-k. At each node, whose budget is b (fixed at circuit generation):

1. Compute whether any active row is empty. For each active row compute whether its number of literals is 1 or 2, via saturating unary counts ge1,ge2,ge3 (constant AND/OR work per bit). Select the first such row by prefix priority, or no row if none qualifies.
2. Gather the selected row (one-hot AND/OR over all rows for each column), and isolate its first and second present literals by prefix counts. Both chosen indices are represented by one-hot masks of length 2k. No data-dependent wiring or array indexing is assumed.
3. Left child sets the first literal true. Right child (only valid when a second literal exists) sets the first false and second true. For every row, test whether any of its literals is set true; mask off the row if so. Clear both signs of every assigned variable in every row. All operations use the same fixed 3k by 2k dimensions, and cost O(k^2) AIG gates per node. Inactive rows may keep arbitrary presence bits, since all their tests are guarded by their active flags.
4. Generate the left child with budget b-1 and (when b>=2) the right child with budget b-2. Return false if an active empty row exists, true if no short row exists, otherwise OR the valid child results. A unit-clause right branch is masked off. If b=0, accept precisely when no active rows remain. The invariant on every valid child is that the number of still unset variables is at most its budget. Invalid branches are masked; no semantic assertion about them is necessary.

The construction has O(k^2 phi^k) gates. Initial metadata conversion computes equality of component labels with O(log(N+2)) gates per pair, sets a single representative for each active label, deduplicates negative occurrences via OR, and disables tautologies. Its size is O(k^2 log(N+2)); reject when the supplied uncovered-component flag is true. There are at most 3k active slot labels and all nonempty clauses are represented. The uncovered flag handles zero-incident clauses and k=0. The previous matching background and compaction circuits contribute O(N log^5(N+2)); this result relies on their mathematical size analysis and does not re-emit those background AIGs. The quadratic logarithmic term is absorbed: for k<=log2(N+2), it is at most O(log^3(N+2)), and otherwise it is O(k^3)=O(k^2 phi^k).

**Theorem:** for the template with at most k forks, and for templates with a uniform bound p on the genuine forks after the first classification (use the prior compaction and second matching contraction), respectively,

    C(f) = O(N log^5(N+2) + min(k*2^k, k^2*phi^k)),
    C(f) = O(N log^5(N+2) + min(p*2^p, p^2*phi^p)).

The minimum follows by choosing one of the two circuit constructions at compile time, with the previous enumeration theorem as the alternative. The zero-parameter case uses only the matching background and uncovered flag. The bounds also apply on promised regions if the bound p is not global, but then no full-function bound follows. As before, actual parameters from individual assignments or averages cannot be substituted for a uniform p. All constants are absolute; this is a size theorem in the free-complement fan-in-two AND model, not a claim about synthesized minima or measured end-to-end savings.

Since log2(phi) = 0.6942419136..., an upper bound

    p <= (1.01 log2 N - 2 log2 log2 N)/log2(phi) + O(1)

suffices for O(N^1.01) deterministic circuits (and the previous SAT restriction length is O(N log N)). This raises the leading coefficient of the sufficient logarithmic-fork cutoff from 1.01 to approximately 1.455. The lower-order logarithm and constant matter for finite N. Exceeding either threshold does not prove hardness. This removes another parameter regime as a possible witness for L-clb-036; it is not an improved SAT lower bound.

## 3. Degree-weighted Hall termination

There is a sharper sufficient criterion. For each currently occurring variable v, let d(v) in {1,2,3} be the number of active normalized clauses containing it. If every clause C satisfies

    sum_{v in C} 1/d(v) >= 1,

then SAT holds. For any subset S of clauses, summing the left-hand sides gives at least |S| and at most |N(S)|, since a variable contributes at most d(v) copies of 1/d(v). Apply Hall as above. This includes all clauses of size >=3, plus (for example) binary clauses on two degree-two variables and units on degree-one variables. More generally it holds for arbitrary occurrence counts when the displayed inequality holds. It is sufficient, not necessary: failure need not mean Hall fails, and Hall failure need not mean UNSAT. In our occurrence-three model every failing nonempty clause has width <=2, so we can use the same recurrence by branching only on failing clauses. Counts can be implemented with O(k^2) gates using unary degree counters capped at three and scaled integer weights 6,3,2 (comparison to six). This preserves the worst-case bound but may reduce software search. We tested this rule in software only; the emitted AIG uses the simpler unweighted Hall rule. This is a termination test, not a new lower-bound invariant.

## 4. Actual reproducible verification and negative performance result

The standalone program below exhausts all record tuples for k=0,1,2 and 0..3 deficient labels, including inactive slots and uncovered labels. Then 4,000 randomized and 2,000 fully active random record cases, up to k=10, compare exhaustive mode-assignment SAT with both branching solvers. It emits a structurally hashed AIG for the unweighted recursion and evaluates all record cases of k<=6 in batches. The reference starts from extracted metadata, not the full original availability graph. The previous kernel theorem and agent replay cover the extraction. Results from the current runtime:

    semantic {'exhaustive': 4994, 'random': 4000, 'dense': 2000}
    branch {'nodes': 18770, 'hall': 4381, 'empty': 6613, 'unit': 6224, 'binary': 1552}
    weighted {'nodes': 14693, 'hall': 4381, 'empty': 6613, 'unit': 3370, 'binary': 329}
    AIG evaluations 8411 parameter pairs 24
    gates (k, branching, enumeration), w=4:
    1 115 75
    2 857 366
    3 3227 927
    4 9272 1884
    5 23442 3525
    6 54458 6498
    7 119717 12243
    8 252567 23928

All assertions passed. The degree-weighted rule cut recursive node visits from 18,770 to 14,693 (21.7%) in these synthetic cases; software solver short-circuiting is allowed, not assumed in the circuit. The branch circuits have many more gates than enumeration for every tested k, despite the smaller asymptotic exponent. Gate counts include all emitted gates, even if dead; no output-cone minimization, native performance claim or exact minimum. Both columns use the same metadata representation and structural hashing. Do not replace the existing small-core enumerator on these results; choose the better available construction. No finite crossover was established. The reference AIG tests cover only k<=6, gate generation through k=8. The upper bound is a paper proof awaiting independent review, not a Lean result.

## 5. Next research target

The agent's fully genuine reduction establishes that local reductions cannot remove every hard supplied-template instance. But no fixed-template lower bound follows. The present improved upper bound only narrows the small-fork regime; further FPT improvements cannot establish L-clb-036. A more useful next step is to strengthen the agent's reduction to a **single fixed template per size with programmable availability inputs**, preserving full genuineness on all input assignments or in a well-defined promise region, with a linear-size overhead and projections for the free input bits. Then investigate invariants of its incidence geometry that constrain arbitrary deterministic circuits, rather than branch-and-bound complexity. Do not claim that high incidence treewidth, NP-hardness, or many branching nodes imply superlinear unrestricted circuit size. The checked 2n-o(n) SAT bound and the open L-clb-036 status are unchanged.

## 6. Standalone reference (`hall_branch_check.py`)

```python
from itertools import product
from random import Random
from collections import Counter, defaultdict
from math import log2

class AIG:
    def __init__(self,n): self.n=n; self.g=[]; self.memo={}
    def And(self,a,b):
        if a==0 or b==0 or a==b^1:return 0
        if a==1:return b
        if b==1 or a==b:return a
        a,b=sorted((a,b)); key=(a,b)
        if key not in self.memo:
            self.g.append(key); self.memo[key]=2*(self.n+len(self.g))
        return self.memo[key]
    def Or(self,a,b):return self.And(a^1,b^1)^1
    def XOR(self,a,b):return self.Or(self.And(a,b^1),self.And(a^1,b))
    def all(self,ls):
        r=1
        for l in ls:r=self.And(r,l)
        return r
    def any(self,ls):return self.all(l^1 for l in ls)^1
    def eval_batch(self,inputs,out):
        mask=(1<<len(inputs))-1
        val=[0]+[sum(((row>>i)&1)<<j for j,row in enumerate(inputs)) for i in range(self.n)]
        def get(l):return val[l//2]^(mask if l&1 else 0)
        for a,b in self.g:val.append(get(a)&get(b))
        return get(out)

def normalize(cs):
    return tuple(sorted(set(tuple(sorted(set(c))) for c in cs if not any(-l in c for l in c))))

def restrict(cs,l):
    return tuple(tuple(q for q in c if q!=-l) for c in cs if l not in c)

def brute(cs,k):
    return any(all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) for x in range(1<<k))

def solve(cs,stats,weighted=False):
    stats['nodes']+=1
    if () in cs:stats['empty']+=1;return False
    if weighted:
        degree=Counter(abs(l) for c in cs for l in c)
        assert max(degree.values(),default=0)<=3
        short=[c for c in cs if sum(6//degree[abs(l)] for l in c)<6]
    else:short=[c for c in cs if len(c)<3]
    if not short:stats['hall']+=1;return True
    c=min(short,key=len); x=c[0]
    assert 1<=len(c)<=2
    if len(c)==1:
        stats['unit']+=1;return solve(restrict(cs,x),stats,weighted)
    stats['binary']+=1
    return solve(restrict(cs,x),stats,weighted) or solve(restrict(restrict(cs,-x),c[1]),stats,weighted)

# Fixed branching circuit, original k columns retained at every node.
# Rows (flag, literals), literals ordered +1,-1,+2,-2,...
def branch(a,rows,budget,k):
    if budget==0:return a.any(on for on,row in rows)^1
    empty=[]; first=[]; found=0
    for on,row in rows:
        # Saturating unary count: ge1, ge2, ge3.
        g1=g2=g3=0
        for l in row:
            g3=a.Or(g3,a.And(g2,l));g2=a.Or(g2,a.And(g1,l));g1=a.Or(g1,l)
        empty.append(a.And(on,g1^1))
        short=a.all((on,g1,g3^1))
        first.append(a.And(short,found^1));found=a.Or(found,short)
    selected=[a.any(a.And(flag,row[j]) for flag,(on,row) in zip(first,rows)) for j in range(2*k)]
    one=[];two=[];seen1=seen2=0
    for l in selected:
        one.append(a.And(l,seen1^1));two.append(a.all((l,seen1,seen2^1)))
        seen2=a.Or(seen2,a.And(seen1,l));seen1=a.Or(seen1,l)
    def child(true,rem,step):
        remove=[a.Or(rem[2*i],rem[2*i+1]) for i in range(k)]
        rr=[]
        for on,row in rows:
            satisfied=a.any(a.And(l,v) for l,v in zip(row,true))
            rr.append((a.And(on,satisfied^1),[a.And(l,remove[j//2]^1) for j,l in enumerate(row)]))
        return branch(a,rr,budget-step,k)
    left=child(one,one,1)
    out=a.Or(found^1,left)
    if budget>=2:
        right_true=[a.Or(one[j^1],two[j]) for j in range(2*k)]
        right_rem=[a.Or(x,y) for x,y in zip(one,two)]
        right=child(right_true,right_rem,2)
        out=a.Or(out,a.And(seen2,right))
    return a.And(a.any(empty)^1,out)

def core(k,w,algorithm='branch'):
    a=AIG(1+3*k*(w+1)); reject=2
    active=[]; labels=[]
    for j in range(3*k):
        off=1+j*(w+1);active.append(2*(off+1));labels.append([2*(off+2+i) for i in range(w)])
    rows=[]
    for j in range(3*k):
        related=[a.And(active[t],a.all(a.XOR(u,v)^1 for u,v in zip(labels[j],labels[t]))) for t in range(3*k)]
        lits=[]
        for i in range(k):lits.extend((related[3*i],a.Or(related[3*i+1],related[3*i+2])))
        # One row per deficient label; deduplicate both literal occurrences and rows.
        on=a.And(active[j],a.any(related[:j])^1)
        on=a.And(on,a.any(a.And(lits[2*i],lits[2*i+1]) for i in range(k))^1)
        rows.append((on,lits))
    if algorithm=='branch':out=branch(a,rows,k,k)
    else:
        joint=[1]*(1<<k)
        for on,row in rows:
            vals=[on^1]
            for i in range(k):vals=[a.Or(v,l) for v in vals for l in (row[2*i+1],row[2*i])]
            joint=[a.And(u,v) for u,v in zip(joint,vals)]
        out=a.any(joint)
    return a,a.And(reject^1,out)

def metadata(D,records,w):
    flat=[v for f in records for v in f]; r=int(not D<=set(flat))
    for j,v in enumerate(flat):
        if v is not None:r|=(1|(v<<1))<<(1+j*(w+1))
    return r

def clauses(D,records):
    cs={d:[] for d in D}
    for i,(c,l,r) in enumerate(records,1):
        for v,s in ((c,i),(l,-i),(r,-i)):
            if v is not None:cs[v].append(s)
    return list(cs.values())

def main():
    rng=Random(261126);stats=Counter();weighted=Counter();counts=Counter();batches=defaultdict(list)
    def check(k,D,R,kind):
        cs=normalize(clauses(D,R));occ=Counter(abs(l) for c in cs for l in c)
        assert max(occ.values(),default=0)<=3
        exp=brute(cs,k)
        assert solve(cs,stats)==exp
        assert solve(cs,weighted,True)==exp
        counts[kind]+=1
        if k<=6:
            w=max(1,max(D,default=0).bit_length());batches[k,w].append((metadata(D,R,w),exp))
    # Exhaust every 2-fork record, with up to three labels; include uncovered labels.
    for k in range(3):
        for m in range(4):
            D=set(range(m))
            for flat in product([None]+list(D),repeat=3*k):
                check(k,D,[flat[3*i:3*i+3] for i in range(k)],'exhaustive')
    for _ in range(4000):
        k=rng.randrange(1,11);m=rng.randrange(1,3*k+2);D=set(range(m))
        R=[tuple(rng.choice([None]+list(D)) for _ in range(3)) for i in range(k)]
        check(k,D,R,'random')
    # Dense fully active records, to exercise branching and Hall termination.
    for _ in range(2000):
        k=rng.randrange(3,11);m=rng.randrange(1,2*k+1);D=set(range(m))
        R=[tuple(rng.randrange(m) for _ in range(3)) for i in range(k)]
        check(k,D,R,'dense')
    print('semantic',dict(counts),'branch',dict(stats),'weighted',dict(weighted),flush=True)
    total=0
    for (k,w),rs in sorted(batches.items()):
        a,out=core(k,w)
        for start in range(0,len(rs),128):
            b=rs[start:start+128];v=a.eval_batch([x for x,y in b],out)
            assert v==sum(int(y)<<j for j,(x,y) in enumerate(b));total+=len(b)
    print('AIG evaluations',total,'parameter pairs',len(batches),flush=True)
    for k in range(1,9):
        a,o=core(k,4);g=len(a.g);del a
        a,o=core(k,4,'enum');h=len(a.g);del a
        print('gates',k,g,h,flush=True)
if __name__=='__main__':main()

```

---

# Earlier handoffs (historical; current status is in section 0 above)

# Research handoff — exact fork kernel and additive deterministic upper bounds

Read this new section first. It extends the previous conflict-component threshold with an exact parameterized reduction and actual AIG tests for the compressed core. This is an upper bound, not a new SAT lower bound. No native solver changes recommended; no novelty claim.

## 0. Repository status

Both requested notes fetched at master `e05533d914b25af59b9814c771b17feb9b1f1766` after the experiments. Orientation blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`, research notes blob `96ee7ae211c13513b1ddb4ab7a07af4850761328`. Both unchanged. The repository reports the end-to-end robust `2n-o(n)` bound Lean-checked on multiples of six; the all-even tails and 17/12 proof remain open in Lean. No Lean replay or repository changes here. Do not redo the checked robust proof. Prior handoffs are retained below for reference, not requests to implement each item.

## 1. Exact kernel with at most three literal occurrences per mode variable

Setting: fixed conflict graph of isolated vertices, disjoint edges, and P3 components (center with two leaves); partition of all N vertices into nonempty groups. Availability a is the ordinary input. Output one iff there is an independent set selecting exactly one available vertex per group. Groups need not have bounded size for this upper bound. Let k be the number of P3 components, called forks here. Label the fork vertices `(c_i,l_i,r_i)`, center first. Each fork admits two modes: center (only c_i permitted) or leaves (both l_i and r_i permitted). Any independent set respects one such mode; it is harmless to permit available vertices without requiring them to be selected.

First remove every fork vertex from the available-option set, retaining all groups even if empty. Apply the previous matching-background reduction to the remaining isolated vertices and pairs: an available isolated vertex, or an available endpoint whose partner is unavailable, supplies a private resource to its group; a pair of available endpoints in one group also supplies one private resource. Two available endpoints in distinct groups form a shared resource edge in the group multigraph. Distinct edges are distinct resources, and may be parallel. An edge can be allocated to either endpoint group but not both. All resource allocations are equivalent to independent choices in the matching background. In a connected component with v groups and e shared edges, every group can be served if there is at least one private resource or e>=v. If neither holds, e=v-1 (connected), so the component is a tree that needs exactly one extra private resource. A spanning tree rooted at any group with a private resource serves all other groups by allocating parent edges to children. With e>=v, root at a cycle instead. These are the proofs of sufficiency; necessity follows from counting distinct resources. This includes singleton groups with no resources and parallel-edge cycles.

Let D be the set of deficient component labels (no private resource, e<v). For every fork, write C_i for the set containing the deficient component of its center if that vertex is available and the component is deficient, otherwise empty. L_i is the set of deficient component labels of its available leaves (deduplicated). Thus |C_i|<=1, |L_i|<=2. All nondeficient components can be ignored when considering fork choices: they can be served using the matching background only. Set a Boolean mode variable z_i=1 for the center mode and 0 for the leaves mode. For each d in D form the clause

    (OR over i with d in C_i of z_i) OR (OR over i with d in L_i of NOT z_i).

An empty clause means immediate rejection. **The original feasibility function equals the satisfiability of this mode CNF.**

Proof: in any feasible transversal, the selected fork vertices respect a mode assignment. Every deficient component needs at least one fork vertex to supplement its e=v-1 background resources. Hence every clause holds. Conversely, if the mode assignment satisfies all clauses, grant each deficient component one available vertex in a permitted mode. Grants can be made independently between components: the same fork can grant its two leaves to distinct components simultaneously, and each vertex belongs to only one group and component. No granted pair conflicts. Use a granted vertex as the private resource for its component's root group, and the tree allocation for its remaining groups. Serve nondeficient components with their background resources. The union selects exactly one vertex per group, with no conflicts. A fork may grant more than one vertex in the same component but only one grant is needed there.

The mode CNF has at most k variables, at most one positive and two negative occurrences per variable, and at most 3k total literal occurrences (duplicates only reduce the count). If every clause is nonempty it has at most 3k clauses. If |D|>2k, reject by the stronger capacity bound: each fork covers at most two deficient components. If |D|=2k, every satisfying mode assignment must choose both available leaves of every fork and these 2k leaf labels must all be distinct. More generally, for any input with |D|>=2k-b, a satisfying assignment chooses center mode on at most b forks, since an assignment with s center choices covers at most 2k-s components. These are exact semantic necessary conditions, not new global lower bounds. Enumerating only mode assignments with at most b centers suffices on that promised input region, but a fixed circuit for all inputs cannot use an input-dependent gate budget.

## 2. Additive circuit upper bound, including the dynamic kernel construction

The previous matching-background construction supplies component labels and deficiency flags using O(N log^5(N+2)) gates. Its proof uses sorting-network gathers, segmented counts and simultaneous contractions with pointer jumping (see immediately preceding handoff). It also applies to a fixed upper bound on the number of records, with input-dependent active flags, endpoints, and private-resource flags: record sorting, label lookup, and aggregation use dynamic keys, not fixed adjacency matrix indexing. All counts/labels have O(log(N+2)) bits. No data-dependent circuit topology is used. In addition aggregate the OR of available fork-endpoint flags in each component (one O(N log^3(N+2)) record aggregation). A deficient component with zero such endpoints sets a global reject bit. The same gathers provide the component label of each of the 3k fork slots, and an active flag iff its vertex is available and its component deficient. Uncovered deficient components are thereby detected even if k=0.

Build the following explicit circuit for the remaining metadata. For each ordered pair j,t of the 3k slots, compute M[j,t] = active[t] AND (label[j]==label[t]). This costs O(k^2 log(N+2)) gates. For each slot j and each i, let p[j,i]=M[j,3i] for the center, and n[j,i]=M[j,3i+1] OR M[j,3i+2] for the leaves (zero-based indexing). The slot's constraint is automatically true if it is inactive; otherwise the associated component clause must hold. Instead of evaluating a length-k OR separately for each of the 2^k mode assignments, produce all 2^k values of that OR by a binary prefix tree. Start with v=NOT active[j]. At depth i, every existing prefix value u yields the two values u OR n[j,i], u OR p[j,i]. This costs at most 2^(k+1)-2 gates for one slot. At each complete mode assignment AND all slot truth values; OR these joint values across assignments; AND with NOT reject. Duplicating constraints for slots in the same component is harmless. There are only 3k slots and every deficient component with a nonempty clause has at least one active slot. The resulting gate bound is O(k^2 log(N+2)+k*2^k), with k=0 handled by the global reject bit. This argument counts actual free-complement AND gates, not running time for a RAM algorithm.

The overall bound is **O(N log^5(N+2)+k*2^k)**. To absorb the quadratic term, if k<=log2(N+2), then k^2 log(N+2)<=log^3(N+2); otherwise log2(N+2)<k and k^2 log(N+2)<k^3=O(k*2^k). This is additive, not O(N log^5(N+2)*2^k). In particular k<=log2 N gives quasi-linear circuits. More generally k<=1.01 log2 N-log2 log2 N+O(1) is sufficient for O(N^1.01) gates. The statement is asymptotic and no constant-optimal synthesis is claimed. Since N-coordinate availability templates are SAT restrictions of length O(N log N), this subclass cannot furnish the desired superlinear SAT lower bound by that transfer. Exceeding the threshold is not evidence of hardness.

## 3. Stronger parameter: genuine forks after contraction

The raw k count can substantially overestimate the residual difficulty. After the first contraction, regard each deficient component as a single group needing one resource. The mode sets (C_i,L_i) exactly encode the remaining choices. Classify each pair:

* If C_i is a subset of L_i, always use the leaves mode and grant a private resource to every element of L_i. If L_i is a subset of C_i, use the center mode and grant a private resource to its elements. The chosen mode dominates the other and never creates new conflicts.
* In the remaining cases C_i is a nonempty singleton, L_i is nonempty and C_i is disjoint from L_i. If |L_i|=1, this is a single shared resource edge between two distinct deficient labels. If |L_i|=2, it is a **genuine fork**, with three distinct deficient labels.

These cases exhaust all possibilities, including unavailable center or leaves, duplicate leaves in the same component, and all endpoints inside nondeficient components. Now contract the multigraph of the newly created private resources and shared edges on D. Each of its remaining deficient components needs a resource from a genuine fork. This is precisely the same allocation proof as section 1, now on contracted groups with possibly dynamic labels. Remap each genuine fork endpoint to its new component if that component is deficient; otherwise discard the endpoint. The resulting mode CNF is equivalent to the original function. It can have fewer genuine forks than were originally present; the one extra contraction described here is sufficient for the theorem. Iteration may reduce it further, but no bound on iterative-round cost beyond the number of forks eliminated is claimed.

**Uniform-in-input size theorem.** Suppose there is an integer p such that for every availability input at most p genuine forks remain at the classification step above (before the second contraction). Then the same fixed template has deterministic AIG complexity O(N log^5(N+2)+p*2^p). This holds with p=0 as well. For a proof, implement the classification using the three active flags and O(log(N+2))-bit label equalities per record. Use sorting/compaction on O(N) records to gather all genuine forks into the first p slots, padding with inactive records; reject on overflow if a promise version is desired. Implement a second matching-background contraction on at most N dynamically labeled vertices and O(N) resource records (unused labels/edges masked). Gather the surviving deficient labels and uncovered flag for the compacted slots. This costs O(N log^5(N+2)) by the previous construction and its dynamic-record interpretation above. Apply section 2 with p slots. For p=0, only the matching-background feasibility test remains. These are fixed-size circuits, with p a bound fixed at construction, not the realized p(a) chosen at runtime. The same construction computes the function correctly on the promised input region p(a)<=p if that promise is not global. It is not legitimate to infer a global circuit bound from an average or sampled p(a). The reference program uses DFS and dictionaries for these background steps; it emits an AIG only for the compressed kernel, not the sorting/contraction stages. No claim of measured end-to-end gate reduction.

## 4. Actual verification

Standalone Python 3, standard library only. Executed on the current runtime:

    semantic checks {'exhaustive': 22760, 'random': 3500}
    statistics {'forks': 40464, 'genuine': 2220, 'no_genuine': 24283,
                'uncovered': 19719, 'budget_reject': 7085, 'simplified': 24911}
    core AIG evaluations 52480 distinct circuit parameter pairs 26
    sample constructed core sizes (w=10):
    [(1,136),(2,682),(3,1690),(4,3283),(5,5743),(6,9706),
     (7,16588),(8,29509),(9,55285),(10,108700)]

The semantic checks compare a direct independent-transversal backtracker with both the kernel CNF brute-force evaluator and an independent mode-coverage evaluator, before and after reclassification/contraction. Exhaustive cases cover every partition into groups of size <=3 and every availability mask for four fixed small conflict graphs: one P3, P3+edge, two P3s, P3+edge+isolated. The 3,500 random cases cover varying group sizes, fork and matching counts, and availability; N<=26. The core AIG is built explicitly with complemented literals, constant simplification and structural hashing, and evaluated in bit-parallel batches on extracted metadata (both before and after simplification, when mode count<=7). The measured gate counts above are for the metadata-to-answer circuit, not end-to-end AIGs; label width w=10. All assertions passed. The sample distribution (especially exhaustive tiny graphs and unsatisfiable inputs) is not evidence of global bounds on p. The asymptotic background gate count is proved using the previous sorting-network construction, not reimplemented gate-by-gate this round.

## 5. Next research target and limitations

A useful next target is the group structure of the compressed mode CNF after removing pure literals and dominated modes. It has very limited signed variable incidence (one positive, two negative), yet the uncompressed P3 model is exponent-universal. Seek transformations or hard families that preserve the genuine interaction after contraction. Any proposed superlinear lower bound must handle arbitrary unrestricted AIGs, not just branching algorithms or monotone circuits. A large genuine-fork count is only a necessary condition for this upper-bound filter to fail; it is not a lower bound. L-clb-036 remains open, and the checked SAT coefficient has not changed. No novelty claim; independent proof review and Lean formalization of this exploratory result are pending.

## 6. Executable reference (`fork_kernel_check.py`)

```python
from collections import Counter, defaultdict
from itertools import product
from random import Random

# Independent baseline: choose one available vertex per group.
def transversal(groups, edges, available):
    adj=defaultdict(set)
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    def go(opts):
        if not opts: return True
        i=min(range(len(opts)),key=lambda i:len(opts[i]))
        return any(go([o-adj[v] for j,o in enumerate(opts) if j!=i]) for v in opts[i])
    return go([set(g)&available for g in groups])

def background(vertices, edges, private):
    """Connected components and deficient labels in a resource multigraph."""
    vertices=set(vertices); adj={v:[] for v in vertices}
    for a,b in edges: adj[a].append(b); adj[b].append(a)
    label={}; sizes=Counter()
    for r in sorted(vertices):
        if r in label: continue
        label[r]=r; stack=[r]
        while stack:
            v=stack.pop(); sizes[r]+=1
            for w in adj[v]:
                if w not in label: label[w]=r; stack.append(w)
    counts=Counter(label[a] for a,b in edges)
    supplied={label[v] for v in private}
    deficient={r for r,n in sizes.items() if counts[r]<n and r not in supplied}
    assert all(counts[r]==sizes[r]-1 for r in deficient)
    return label,deficient

def first_stage(groups,matching,forks,available):
    owner={v:i for i,g in enumerate(groups) for v in g}
    used={v for e in matching for v in e}|{v for f in forks for v in f}
    private={owner[v] for v in available-used}; edges=[]
    for a,b in matching:
        u,v=owner[a],owner[b]
        if a in available and b in available and u!=v: edges.append((u,v))
        else:
            if a in available: private.add(u)
            if b in available: private.add(v)
    labels,D=background(range(len(groups)),edges,private)
    records=[tuple(labels[owner[v]] if v in available and labels[owner[v]] in D else None for v in f) for f in forks]
    return D,records

def kernel(D,records):
    clauses={c:[] for c in D}
    for i,(c,a,b) in enumerate(records,1):
        for v,l in ((c,i),(a,-i),(b,-i)):
            if v is not None: clauses[v].append(l)
    cs=list(clauses.values())
    counts=Counter(l for cl in cs for l in cl)
    assert sum(map(len,cs))<=3*len(records)
    assert all(counts[i]<=1 and counts[-i]<=2 for i in range(1,len(records)+1))
    return cs

def brute_cnf(cs,k):
    return any(all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) for x in range(1<<k))

def mode_eval(D,records):
    """Independent set-cover interpretation, not the CNF evaluator."""
    for x in range(1<<len(records)):
        covered=set()
        for i,(c,a,b) in enumerate(records): covered.update((c,) if x>>i&1 else (a,b))
        if D<=covered: return True
    return False

def simplify(D,records):
    """Reduce dominated modes and two-choice resources, then contract again."""
    private=set(); edges=[]; genuine=[]
    for c,a,b in records:
        C={c}-{None}; L={a,b}-{None}
        if C<=L: private.update(L)
        elif L<=C: private.update(C)
        elif len(L)==1: edges.append((c,next(iter(L))))
        else:
            assert c is not None and len(L)==2 and c not in L
            genuine.append((c,a,b))
    lab,D2=background(D,edges,private)
    reduced=[tuple(lab[v] if lab[v] in D2 else None for v in f) for f in genuine]
    return D2,reduced

# AIG: 0/1 constants, primary/gate i represented by 2*i, complement ^1.
class AIG:
    def __init__(self,n): self.n=n; self.g=[]; self.memo={}
    def And(self,a,b):
        if a==0 or b==0 or a==b^1:return 0
        if a==1:return b
        if b==1 or a==b:return a
        a,b=sorted((a,b));key=(a,b)
        if key not in self.memo:
            self.g.append(key);self.memo[key]=2*(self.n+len(self.g))
        return self.memo[key]
    def Or(self,a,b):return self.And(a^1,b^1)^1
    def XOR(self,a,b):return self.Or(self.And(a,b^1),self.And(a^1,b))
    def all(self,ls):
        r=1
        for l in ls:r=self.And(r,l)
        return r
    def any(self,ls):return self.all(l^1 for l in ls)^1
    def eval_batch(self,inputs,out):
        mask=(1<<len(inputs))-1
        val=[0]+[sum(((row>>i)&1)<<j for j,row in enumerate(inputs)) for i in range(self.n)]
        def get(l):return val[l//2]^(mask if l&1 else 0)
        for a,b in self.g:val.append(get(a)&get(b))
        return get(out)

def core_circuit(k,w):
    """Inputs: uncovered flag, then for each of 3k slots (active, w-bit label).
    Active means available in a deficient component. Uncovered means some deficient
    component has no active endpoint. This is the post-background circuit only.
    """
    a=AIG(1+3*k*(w+1)); reject=2
    active=[]; labels=[]
    for j in range(3*k):
        off=1+j*(w+1);active.append(2*(off+1));labels.append([2*(off+2+i) for i in range(w)])
    # Compute clauses for every slot, including duplicates and inactive slots.
    # All clause truth vectors use the same lexicographic mode assignment order.
    joint=[1]*(1<<k)
    for j in range(3*k):
        related=[a.And(active[t],a.all(a.XOR(u,v)^1 for u,v in zip(labels[j],labels[t]))) for t in range(3*k)]
        vals=[active[j]^1]
        for i in range(k):
            p=related[3*i];n=a.Or(related[3*i+1],related[3*i+2])
            vals=[a.Or(v,l) for v in vals for l in (n,p)]
        joint=[a.And(u,v) for u,v in zip(joint,vals)]
    return a,a.And(reject^1,a.any(joint))

def encode_metadata(D,records,w):
    flat=[v for f in records for v in f]; r=int(not D<=set(flat))
    for j,v in enumerate(flat):
        if v is not None:r|=(1|(v<<1))<<(1+j*(w+1))
    return r

def partitions(vs):
    if not vs:yield [];return
    v,*rest=vs
    for p in partitions(rest):
        yield [(v,)]+p
        for j,g in enumerate(p):
            if len(g)<3:yield p[:j]+[(v,)+g]+p[j+1:]

def main():
    rng=Random(261126); counts=Counter(); batches=defaultdict(list); stats=Counter()
    def check(gs,match,forks,A,kind):
        edges=match+[(c,v) for c,a,b in forks for v in (a,b)]
        expected=transversal(gs,edges,A)
        D,R=first_stage(gs,match,forks,A);cs=kernel(D,R)
        assert brute_cnf(cs,len(R))==expected
        assert mode_eval(D,R)==expected
        assert not expected or len(D)<=2*len(R)
        D2,R2=simplify(D,R)
        assert brute_cnf(kernel(D2,R2),len(R2))==expected
        assert mode_eval(D2,R2)==expected
        assert len(R2)<=len(R)
        counts[kind]+=1;stats['forks']+=len(R);stats['genuine']+=len(R2)
        stats['no_genuine']+=not R2;stats['uncovered']+=any(not c for c in cs)
        stats['budget_reject']+=len(D)>2*len(R)
        stats['simplified']+=len(R2)<len(R)
        # Actual gate-level core circuit batch, both before and after simplification.
        w=max(1,(len(gs)-1).bit_length())
        for DD,RR in ((D,R),(D2,R2)):
            if len(RR)<=7:batches[len(RR),w].append((encode_metadata(DD,RR,w),expected))
    for n,match,forks in [(3,[],[(0,1,2)]),(5,[(3,4)],[(0,1,2)]),(6,[],[(0,1,2),(3,4,5)]),(6,[(3,4)],[(0,1,2)])]:
        for gs in partitions(list(range(n))):
            for mask in range(1<<n):
                check(gs,match,forks,{i for i in range(n) if mask>>i&1},'exhaustive')
    for _ in range(3500):
        n=rng.randrange(1,27);p=list(range(n));rng.shuffle(p);gs=[]
        while p:
            s=rng.randrange(1,4);gs.append(tuple(p[:s]));p=p[s:]
        p=list(range(n));rng.shuffle(p);k=rng.randrange(n//3+1)
        forks=[tuple(p[3*i:3*i+3]) for i in range(k)];p=p[3*k:];j=rng.randrange(len(p)//2+1)
        matching=[tuple(p[2*i:2*i+2]) for i in range(j)]
        A={v for v in range(n) if rng.random()<rng.choice((.35,.65,.95))}
        check(gs,matching,forks,A,'random')
    print('semantic checks',dict(counts));print('statistics',dict(stats))
    total=0
    for (k,w),rows in sorted(batches.items()):
        a,out=core_circuit(k,w)
        for start in range(0,len(rows),256):
            b=rows[start:start+256];v=a.eval_batch([x for x,y in b],out)
            assert v==sum(int(y)<<j for j,(x,y) in enumerate(b));total+=len(b)
    print('core AIG evaluations',total,'distinct circuit parameter pairs',len(batches))
    print('sample constructed core sizes (w=10):',[(k,len(core_circuit(k,10)[0].g)) for k in range(1,11)])
if __name__=='__main__':main()

```

---

# Earlier research archive (not a request to implement each item)

# Research handoff — a conflict-component threshold for sparse SAT projections

Read this new section first. We sharpen the previous bounded-occurrence compiler from five to three occurrences and isolate a canonical monotone feasibility problem. Conflict components of size three already retain the full worst-case polynomial exponent of SAT, whereas conflict components of size at most two admit quasi-linear deterministic circuits. This is a paper reduction and upper bound, **not a superlinear lower bound** or a claim of literature novelty. No native solver changes recommended.

## 0. Repository status

Both requested notes were fetched after the experiments at `e05533d914b25af59b9814c771b17feb9b1f1766`: orientation blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`; research notes blob `96ee7ae211c13513b1ddb4ab7a07af4850761328`. Both unchanged. The robust identifier `2n-o(n)` theorem on multiples of six remains reported Lean-checked; the all-even support/tails and 17/12 chain remain open in Lean. No Lean replay or repo modifications in this round. Do not duplicate the checked robust proof.

## 1. Occurrence three instead of five

Given any fixed CNF with clauses of width at most three, split every variable into one fresh copy per occurrence. Instead of bidirectional equality clauses on a path, link the d copies by a **directed cycle** of implications `(-w_j OR w_{j+1})`, indices modulo d, when d>=2. Use no link when d=1. Every satisfying assignment to a directed cycle is constant: one true copy forces all true, and otherwise all are false. Each copy now occurs once in the original formula, once positively in the cycle, and once negatively in the cycle. Thus each copy has at most **three total occurrences**, and the new formula has at most 3L literal occurrences if the original has L. Programmable unit signs are retained as single occurrences of their designated copies. The projection to SAT remains a coordinate restriction of length O(L log(L+2)). This improves the five-occurrence version in the earlier verifier bridge. Empty clauses give a constant false function and may be handled separately.

## 2. A monotone canonical problem with tiny conflict components

Define an availability-to-transversal function `F_{G,P}(a)` on N bits, one per vertex of a fixed undirected simple conflict graph G. P is a partition of the vertices into nonempty groups of size at most three. Output one iff there exists an independent set containing exactly one available vertex from each group. This is monotone in the availability bits, but **all complexity bounds below count unrestricted Boolean AIGs**, not monotone circuits. Edges may connect vertices in the same group (these are irrelevant). Components of G must be isolated vertices or three-vertex paths P3 (a center with two leaves); no restriction on the way the partition groups cross graph components.

**Universality theorem.** For every width-at-most-three fixed CNF projection `f(x)=exists y B(x,y)` of L fixed literal occurrences and m ordinary input bits, there is such an F with N<=3(L+2m) vertices and `f(x)=F(a(x))`, where each availability coordinate is a constant one, x_i, or its complement. Constant functions can be obtained separately, including empty-clause cases. No extra AIG gates are needed to perform the projection.

**Proof.** Treat the fixed clauses as groups of literal occurrences. For each ordinary input variable i, add a two-literal choice group `(i, -i)` (a tautology before restricting availability). The positive choice is available iff x_i=1; the negative iff x_i=0. All other choices initially have availability one. Now split **all** literal occurrences, including both choices in each of these new groups, into fresh copies. Add directed implication cycles as in section 1 and make their two-literal clauses additional groups, all available. Let every literal occurrence in the resulting formula become a distinct graph vertex; connect two vertices iff their literals are opposite signs of the same copy. Every copy has either a single occurrence or three occurrences, two of one sign and one of the other. Its conflict component is therefore an isolated vertex or a P3. The groups are precisely the clauses, and every group has size 1, 2 or 3. The vertex count is at most 3(L+2m), since each pre-cycle occurrence creates at most two additional cycle occurrences.

If f(x)=1, extend a witness to equal copies and choose one true available literal per group; these choices never contradict. Conversely, a transversal cannot choose opposite signs of any copy, so assign all chosen literals true and extend arbitrarily to unchosen variables. This satisfies all cycle clauses and fixed clauses and enforces the input value via the uniquely available choice in each input group. Directed cycles then identify copies and give an original witness. This proves the exact equivalence. Using distinct copies for the two input alternatives is essential to keep the conflict components P3, not K2,2. Ordinary inputs absent from the fixed clauses are harmless.

**Positive projections for monotone f.** If f is monotone, the same construction need not use complemented availability inputs: set the positive choice to x_i and negative choice to constant one. Feasibility is then exactly `exists u<=x, f(u)=1`, which equals f(x). Thus every monotone function with a small nondeterministic AIG has a positive projection into this class with linear overhead. This assertion is about the function, not the gate basis of a deterministic implementation. A monotone lower bound for F is not automatically an unrestricted lower bound.

## 3. Reverse reduction and exponent equivalence

For any fixed G with maximum degree at most two, and groups of size <=3, use one existential selection bit z_v and one availability variable a_v per vertex. Write a positive clause OR(z_v for v in group) per group; a binary clause (-z_u OR -z_v) per conflict edge; a binary clause (-z_v OR a_v) per vertex; and a programmable unit prescribing a_v. A satisfying assignment selects at least one vertex per group; remove extra selected vertices to obtain an independent transversal. Conversely a transversal yields a satisfying assignment. The literal count is at most `N+2|E|+2N+N <=6N` (assuming nonempty groups); variables can be numbered 1..2N. The exact SAT encoding has length O(N log(N+2)), one free sign per vertex. For the P3 class, |E|<=2N/3, but the coarser bound suffices. If desired apply the directed-cycle compiler to make total variable occurrence <=3, with only a constant factor overhead. Independently the verification circuit has O(N) gates and O(N) total inputs/witnesses: guess z, check group clauses, conflicts, and availability implications. The reverse construction works without assumptions about deterministic circuit topology.

Let P(N) be the maximum of 1 and deterministic free-complement AIG sizes of these P3-transversal functions with at most N vertices. Let D(S) be the worst-case deterministic complexity of nondeterministic AIGs of total size (ordinary inputs+witness bits+gates) at most S, and T(N) the worst SAT-slice complexity up to length N, as in the earlier verifier bridge. The Tseitin compiler, section 2 and section 3 give absolute-constant rescalings `D(S)<=P(O(S))`, `P(N)<=D(O(N))`, `P(N)<=T(O(N log(N+2)))`. The previous exact-grammar verifier gives `T(N)<=D(O(N log^2(N+2)))`. Hence the three limsup polynomial exponents coincide. This uses the previous verifier theorem as a premise; this round does not replay that verifier. The exact boundary at exponent 1.01 is not equivalent up to logs. In particular a lower bound Omega(N^(1.01+epsilon)) on an infinite P3-transversal family would suffice for L-clb-036. No such bound is established. The functions can be chosen monotone, but unrestricted lower bounds remain the challenge. Even a conflict graph of treewidth one is not a small-width guarantee here, because the groups connect across components; this graph is NOT the clause-level conflict graph J in the previous section.

## 4. What if all conflict components have size at most two?

**Theorem.** For conflict graphs consisting of isolated vertices and disjoint edges (a matching), the same availability-to-transversal problem, with any nonempty groups, has deterministic AIG size O(N log^5(N+2)). No bounded treewidth of the group-level graph is needed. Consequently this subclass cannot witness L-clb-036 by the above coordinate restrictions. This is a sufficient upper bound, not an optimal exponent of the logarithm.

**Combinatorial reduction.** Treat each group as a vertex of a multigraph M. Each available isolated option or available option whose partner is unavailable supplies a private resource to its group. If both endpoints of a conflict edge are available and in the same group, that pair supplies a private resource as well (a group needs only one option). If both are available and in different groups, put an undirected edge between those groups; the edge can serve either endpoint, but not both. Discard unavailable options. Choosing one available independent option per group is exactly allocating distinct resources to every group vertex: shared edges may be allocated to one endpoint only. Parallel edges are distinct resources. For each connected component with v vertices and e shared edges, allocation exists iff it has a private resource or e>=v. Necessity: without private resources each vertex needs one distinct edge. Sufficiency: with a private resource, root a spanning tree there and allocate each parent edge to its child. Without private resources, e>=v implies a cycle (including a parallel-edge cycle of length two); orient the cycle cyclically to allocate one edge to each cycle vertex, then extend through a spanning forest rooted on the cycle, allocating parent edges to the remaining vertices. Isolated groups with no available resource fail the test. Thus evaluate component labels and compare edge/vertex counts and private flags.

**Circuit implementation (nonuniform fixed topology, no random access assumption).** There are k<=N group vertices and O(N) possible edge records with input-dependent active flags. Private-resource flags are ORs of local availability expressions, O(N) gates. Compute components by simultaneous contractions. Initially each vertex has its own label. At each round, each current component with a live outgoing edge chooses the edge of minimum fixed unique ID crossing to another component. Its successor is the other component label. Components without such edges point to themselves. Directed successor cycles of length >=3 are impossible: at each component on such a cycle its chosen edge ID is strictly less than the incoming edge ID, which gives a cyclic strict inequality. Break a 2-cycle by making the smaller label point to itself. Pointer jumping for ceil(log2(k+1)) rounds maps all labels to roots. Update every original vertex label to its root. Each nonisolated current component merges with at least one other; all such components merge into groups of size at least two. Components already isolated in the current active quotient never participate again. Therefore the number of nonisolated components halves or better each round. After ceil(log2(k+1)) rounds there are no remaining crossings. Every merge follows an active edge, and absence of crossings proves the labels are exactly the connected components.

Use ordinary fan-in-two bitonic sorting networks on O(N) records of O(log(N+2)) bits. Each comparator and conditional record exchange costs O(log(N+2)) AIG gates, and there are O(N log^2(N+2)) comparators, so one sort costs O(N log^3(N+2)). All required lookup/broadcast operations can be implemented with this bound: append one table record for each possible key (unused labels may contain defaults), sort by key with table before requests, then propagate the last table record in a doubling prefix scan and sort responses back by their original index. A segmented minimum or sum can be implemented similarly by sorting and a doubling scan with group-boundary tests, using O(N log^2(N+2)) additional gates; unique table records are filled by scatter via another sort. Counts use O(log(N+2)) bits. For each contraction round, gather endpoint labels, discard inactive or internal edges, sort directed incident records by component and edge ID, select minimum records and fill successor table. Detect 2-cycles using one table lookup. Each pointer-jump round uses one batched lookup on O(N) records, and update labels by one further lookup. These operations use O(N log^4(N+2)) gates per contraction round, with O(log(N+2)) rounds, giving O(N log^5(N+2)). At the end sort vertex records by component label and aggregate counts and private flags, also sort one record per active original shared edge by its final component label (do not drop edges that were contracted). Test e>=v or private for every nonempty component. This final step is O(N log^3(N+2)). Padding to fixed record counts and fixed numbers of rounds makes the circuit topology independent of the availability input. The proof is an explicit circuit-size accounting argument; the Python reference implements the contraction semantics with dictionaries, **not** the sorting-network gate implementation. No actual AIG count or speedup is claimed.

**Interpretation.** Conflict components of size two are easy in the precise quasi-linear sense above; size three suffices for exponent-universal representation. This is a structural expressiveness threshold, not a proved complexity-class separation: if SAT has small circuits, the P3 family may also have small circuits. Large conflict-component count, group-level expansion and monotonicity alone do not establish hard circuits. The next useful step is to investigate the P3 center-vs-two-leaf resource allocation, exploiting group incidence without assuming a restricted deterministic circuit model. In particular the matching case provides a negative control for any future purported lower-bound invariant.

## 5. Executed verification

Actual run of the standalone Python below (Python 3, stdlib only):

    compiler checks 1533 reverse SAT 411 encoding sign checks 411
    exhaustive matching checks 4864 max rounds 1
    random matching checks 3000 max rounds 2
    arbitrary multigraph connectivity checks 1000

Compiler: 240 random width<=3 CNFs, all ordinary assignments (1,533). Compare independent literal-transversal backtracking with DPLL on original clauses. For up to two assignments per template independently check reverse CNF satisfiability and encoding lengths/sign-coordinate differences (411 each). The graph compiler also asserts degree <=2, no edge with two degree-two endpoints, and occurrence <=3. Exhaust all partial matchings on six vertices (76) and all 64 availability masks for a fixed three-group partition into pairs. Random matching cases include same-group conflicts, parallel edges, isolated groups and variable group sizes. Test contraction on 1,000 arbitrary random multigraphs against DFS component sets. All assertions passed. These are semantic tests, not gate-level implementation or Lean checks. Positive monotone projection and asymptotic circuit costs are proved above, not separately benchmarked. The previous verifier bridge's tests have not been re-run this round. No claims of novelty or unrestricted superlinear bounds.

```python
from itertools import product
from collections import defaultdict, Counter
from random import Random

# Signed nonzero integers represent literals. Ordinary input i fixes variable i+1.
def sat(cs):
    cs=[frozenset(c) for c in cs if not any(-a in c for a in c)]
    def go(cs):
        if not cs:return True
        if any(not c for c in cs):return False
        c=min(cs,key=len);a=next(iter(c))
        for l in (a,-a) if len(c)>1 else (a,):
            if go([d-{-l} for d in cs if l not in d]):return True
        return False
    return go(cs)

def compile_paths(cs,m):
    copies=defaultdict(list); groups=[]; rails=[]; n=0
    def fresh(a):
        nonlocal n
        n+=1;copies[abs(a)].append(n);return n if a>0 else -n
    for c in cs:groups.append(tuple(fresh(a) for a in c))
    for i in range(1,m+1):
        rails.append(len(groups));groups.append((fresh(i),fresh(-i)))
    for vs in copies.values():
        if len(vs)>1:groups.extend((-a,b) for a,b in zip(vs,vs[1:]+vs[:1]))
    counts=Counter(abs(a) for c in groups for a in c);assert max(counts.values(),default=0)<=3
    signed=defaultdict(list); ids=[]; v=0
    for c in groups:
        g=[]
        for a in c:signed[a].append(v);g.append(v);v+=1
        ids.append(tuple(g))
    edges={tuple(sorted((a,b))) for i in range(1,n+1) for a in signed[i] for b in signed[-i]}
    degree=Counter(a for e in edges for a in e);assert max(degree.values(),default=0)<=2
    assert all(not(degree[a]==degree[b]==2) for a,b in edges)
    return ids,edges,rails,groups

def available(groups,rails,x):
    A={v for g in groups for v in g}
    for i,j in enumerate(rails):A.remove(groups[j][1 if x>>i&1 else 0])
    return A

def transversal(groups,edges,A):
    adj=defaultdict(set)
    for a,b in edges:adj[a].add(b);adj[b].add(a)
    opts=[set(g)&A for g in groups]
    def go(opts):
        if not opts:return True
        i=min(range(len(opts)),key=lambda i:len(opts[i]))
        return any(go([g-adj[v] for j,g in enumerate(opts) if j!=i]) for v in opts[i])
    return go(opts)

def reverse(groups,edges,A):
    # z_v = v+1; a_v = N+v+1. Each a_v has one programmable unit.
    N=sum(map(len,groups));cs=[tuple(v+1 for v in g) for g in groups]
    cs.extend((-a-1,-b-1) for a,b in edges)
    cs.extend((-v-1,N+v+1) for v in range(N))
    cs.extend(((N+v+1) if v in A else -(N+v+1),) for v in range(N))
    return cs

def encode(cs):
    def word(a):return ('11' if a>0 else '10')+''.join('1'+b for b in bin(abs(a))[2:][::-1])+'01'
    return ''.join(''.join(map(word,c))+'00' for c in cs)

def contraction(k,edges):
    # Simulates the component-label algorithm; dictionary operations are NOT gate counts.
    label=list(range(k));rounds=0
    while True:
        best={}
        for eid,(a,b) in enumerate(edges):
            u,v=label[a],label[b]
            if u==v:continue
            for p,q in ((u,v),(v,u)):
                if p not in best or eid<best[p][0]:best[p]=(eid,q)
        if not best:return label,rounds
        succ={p:best.get(p,(-1,p))[1] for p in set(label)}
        old=succ.copy()
        for p,q in old.items():
            if p!=q and old[q]==p and p<q:succ[p]=p
        for _ in range(max(1,k.bit_length())):succ={p:succ[q] for p,q in succ.items()}
        label=[succ[p] for p in label];rounds+=1
        assert rounds<=k.bit_length()

def matching_eval(groups,edges,A):
    owner={v:i for i,g in enumerate(groups) for v in g};pairs={v:w for a,b in edges for v,w in ((a,b),(b,a))}
    private=set();links=[]
    for v in A:
        w=pairs.get(v)
        if w not in A or owner[w]==owner[v]:private.add(owner[v])
        elif v<w:links.append((owner[v],owner[w]))
    lab,rounds=contraction(len(groups),links);V=Counter(lab);E=Counter(lab[a] for a,b in links);P={lab[a] for a in private}
    return all(E[c]>=n or c in P for c,n in V.items()),rounds

def matchings(vs):
    if not vs:yield ();return
    a,*rest=vs
    yield from matchings(rest)
    for b in rest:
        for e in matchings([v for v in rest if v!=b]):yield ((a,b),)+e

def main():
    rng=Random(261126); checks=0; reverses=0; maxdeg=0; signchecks=0
    for _ in range(240):
        n=rng.randrange(1,7);m=rng.randrange(n+1)
        cs=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4))) for j in range(rng.randrange(1,9))]
        gs,es,rails,clauses=compile_paths(cs,m)
        for x in range(1<<m):
            A=available(gs,rails,x);expect=sat(cs+[((i+1) if x>>i&1 else -(i+1),) for i in range(m)])
            assert transversal(gs,es,A)==expect;checks+=1
            if x<2:
                rs=reverse(gs,es,A);assert sat(rs)==expect;reverses+=1
                N=sum(map(len,gs));other=encode(reverse(gs,es,A^set(range(N))));s=encode(rs)
                assert len(s)==len(other) and sum(a!=b for a,b in zip(s,other))==N;signchecks+=1
    print('compiler checks',checks,'reverse SAT',reverses,'encoding sign checks',signchecks)
    count=0;roundmax=0
    gs=[(0,1),(2,3),(4,5)]
    for es in matchings(list(range(6))):
        for mask in range(64):
            A={i for i in range(6) if mask>>i&1};v,r=matching_eval(gs,es,A)
            assert v==transversal(gs,es,A);count+=1;roundmax=max(roundmax,r)
    print('exhaustive matching checks',count,'max rounds',roundmax)
    count=0
    for _ in range(3000):
        k=rng.randrange(1,17);gs=[];N=0
        for j in range(k):
            d=rng.randrange(1,4);gs.append(tuple(range(N,N+d)));N+=d
        order=list(range(N));rng.shuffle(order);es=list(zip(order[::2],order[1::2]))[:rng.randrange(N//2+1)];A={v for v in range(N) if rng.randrange(4)!=0}
        v,r=matching_eval(gs,es,A);assert v==transversal(gs,es,A);count+=1;roundmax=max(roundmax,r)
    print('random matching checks',count,'max rounds',roundmax)
    # Connectivity simulation against independent DFS, on arbitrary multigraphs.
    for _ in range(1000):
        k=rng.randrange(1,150);edges=[(rng.randrange(k),rng.randrange(k)) for i in range(rng.randrange(k*3+1))];lab,r=contraction(k,edges);adj=defaultdict(set)
        for a,b in edges:adj[a].add(b);adj[b].add(a)
        for i in range(k):
            seen={i};stack=[i]
            while stack:
                for j in adj[stack.pop()]-seen:seen.add(j);stack.append(j)
            assert seen=={j for j in range(k) if lab[j]==lab[i]}
    print('arbitrary multigraph connectivity checks 1000')
if __name__=='__main__':main()

```

---

# Earlier research archive (not a request to implement each item)

# Research handoff — shared 2-CNF propagation and the hard-clause conflict core

Read this section first. New result: a deterministic upper bound on fixed sparse CNF projections, independent of the treewidth of the fixed binary background. This is a negative control for candidate SAT restrictions, not a lower bound on SAT. No novelty claim; the ingredients are elementary implication-graph reasoning and finite-domain constraint compilation. The previous quantitative verifier bridge is retained below as historical context.

## 0. Repository status

Read-only inspection of `e05533d914b25af59b9814c771b17feb9b1f1766`: both requested notes were fetched after the experiment. Orientation notes blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`, research notes blob `96ee7ae211c13513b1ddb4ab7a07af4850761328`, unchanged from the previous round. The robust 2n-o(n) theorem on multiples of six remains reported Lean-checked; all-even support/tails and the 17/12 chain remain pending. No local Lean replay, no repo changes. Do not implement this in the native exact-synthesis engine unless there is an independent use case.

## 1. Exact reduction to a conflict core

Let P be a fixed CNF of width at most three, split into a fixed background B of clauses of width <=2 and k fixed ternary clauses H_i. Ordinary input bits independently prescribe signs of distinguished unit clauses. Let U(x) be those forced literals. L counts total literal occurrences including the programmable units. Ignore unused variables, so there are at most L variables; empty clauses can be treated as an immediate false output. Repeated literals, tautologies, and repeated programmable variables cause no difficulty.

**Theorem.** The projection f(x)=SAT(B and H and U(x)) has deterministic free-complement AIG size O(L + 3^k). More generally construct a graph J on the k hard clauses as below. For any vertex cover of size c, f has size O(L + (k+1)3^c). If J has treewidth t, size O(L + k 3^(t+1)) for k>=1. These are nonuniform bounds on the fixed template, not algorithms that solve arbitrary variable templates in this time.

**Proof of the shared background circuit.** If B is unsatisfiable, f is false. Otherwise form the fixed implication graph on signed literals, with edges not-a -> b and not-b -> a for (a or b), and not-a -> a for a unit. Let R(a) be the reflexive transitive closure from a. For any forced set W, its closure R(W) is the union of R(a) for a in W. B and W is satisfiable iff the closure contains no complementary pair. Necessity follows from the implications. For sufficiency assign all closure literals true, consistently. Every clause touching an assigned variable is either satisfied or, if one literal is false, its other literal is implied true (a unit false likewise contradicts closure). Thus remaining clauses are untouched clauses of B on unassigned variables, satisfiable by restricting any model of B. Combine the assignments. This proof avoids any assumption about the number of forced literals.

Contract strongly connected components of the fixed implication graph. For each component compute an activation bit as the OR of all forced input literals at that component and all predecessor activation bits, in topological order. Each prescribed sign gives two complementary possible activation literals. Fan-in-two OR costs at most the total number of edges plus unit occurrences, O(L). Check no variable has both signs active, using O(L) further gates. Write K(x) for this consistency bit and A_a(x) for activation of literal a. No transitive-closure matrix needs to be evaluated at runtime; the graph topology and SCCs are constants. The resulting background circuit is O(L), regardless of its treewidth. Static preprocessing can cost more than O(L) without changing circuit size.

**Proof of the conflict reduction.** For each H_i discard a candidate a if -a belongs to R(a). For remaining candidates define the availability bit v_a(x)=not A_(-a)(x). Candidates a,b are compatible iff -b is not in R(a). This is symmetric because implication edges are closed under contraposition (also for paths). Under K(x), a selection of one candidate per hard clause can extend the forced assignment iff each candidate is available and every pair compatible. To see this, the union of their closures and the background closure is inconsistent iff two generators p,q have p -> z and q -> not-z for some z; by contraposition this implies p -> not-q. Conversely such a path makes the union inconsistent. Self conflicts have already been removed; conflicts with the forced set are exactly the availability tests. Apply the closure extension lemma. In the reverse direction a model selects a true literal in each hard clause. Empty candidate sets yield false, and k=0 yields K(x).

Define J to have an edge between distinct hard clauses if at least one pair of their remaining candidates is incompatible. Each clause is a domain of at most 3 choices, with input-dependent unary availability and static pair constraints. This finite-domain CSP exactly captures the hard part. Repeated candidates may be merged but need not be.

**Unrestricted hard core.** Build a ternary branching tree on the k clauses. Prune static incompatible prefixes. At a node compute OR over its surviving children of (availability of the chosen literal AND child value). Leaves are true. There are at most (3^(k+1)-1)/2 nodes. Thus O(3^k) gates, not O(L*3^k). Conjoin K(x) at the root. The background activation wires are shared throughout.

**Vertex cover.** Enumerate the at most 3^c assignments to the cover, statically discard incompatible ones, and AND their availability bits. For each outside clause, OR the availability bits of its candidates compatible with the cover selection. No two outside clauses can conflict, so AND these per-clause results with the cover bits and OR over cover selections. Each branch costs O(k+1), yielding the stated bound. No assumption about optimal cover computation is needed.

**Treewidth.** Fix a tree decomposition of J with bags of size <=t+1. Contract adjacent bags when one is contained in the other (preserves decomposition); root the resulting tree. Each non-root bag introduces at least one vertex not in its parent, unique to that introduction by the connected-bag property; hence there are O(k) bags. For each bag assignment (<=3^(t+1)), enforce static internal conflicts, AND the availability bits for vertices introduced here, and AND the child messages evaluated at their corresponding separator assignments. For each child-to-parent message OR over child bag assignments agreeing with the separator. These ORs partition the child assignments and cost O(3^(t+1)) per edge. Total availability conjunctions O(k 3^(t+1)) since each vertex is introduced once; child conjunctions likewise because the tree has O(k) edges. This gives the theorem; no claim that the optimal decomposition can be found cheaply. Treewidth bound not experimentally implemented in this round.

## 2. Quantitative implications

For L literal occurrences the encoding length n is at least L and at most O(L log L) with compact identifiers. In particular any family with k <= 1.01 log_3 L + O(1) has deterministic size O(L^1.01), hence O(n^1.01) on the restriction. Even a large binary background cannot change that conclusion. With k<=L, the cover or treewidth bound excludes families with c <= 0.01 log_3 L + O(1) or t <= 0.01 log_3 L + O(1), respectively. These are sufficient upper-bound conditions, not necessary hardness conditions on all other families. If k is small, use the sharper O(L+3^k) bound rather than the cover formula. Fixed binary backgrounds can have arbitrarily large treewidth (e.g. equality constraints on a bounded-degree expander); the graph J is about incompatibility of hard choices after closure, not primal treewidth. This rules out a different class of candidate families than bounded primal treewidth alone. No claim of an unconditional improvement to the known SAT lower bound.

A next direction: construct explicit hard-choice conflict graphs with small literal-occurrence budget but high deterministic complexity of their availability-to-feasibility function. Beware: a large treewidth or cover is not a lower bound. A purely monotone lower bound on the availability function does not imply an unrestricted lower bound, and the availability bits may be correlated when produced by the background. The quantitative bridge in the previous section remains the target.

## 3. Actual replay

Python reference below uses explicit transitive closure for semantic checking, not the linear-gate SCC circuit; it checks both the full selection and greedy-cover reduction against independent exhaustive truth assignment enumeration. Run as a standalone script with Python 3. Output from the actual run:

    random instances=1120, input checks=12480, cover smaller than hard-clause count=966, unsatisfiable bases=257
    exhaustive two-variable partial-unit checks=9216

Total 21,696 input checks; no assertion failures. The exhaustive loop includes all subsets of the eight non-tautological distinct unit/binary clauses on two variables and four hard-clause configurations, with all nine partial unit assignments. The random tests include repeated literals, tautologies, and unsatisfiable backgrounds. The finite tests do not prove the asymptotic theorem or establish native runtime gains. The tree-decomposition extension and the SCC gate count are paper arguments, not implemented or Lean-checked.

```python
from itertools import product, combinations
import random

def litval(l,x): return bool((x>>(abs(l)-1))&1)==(l>0)
def sat(n,clauses,units):
    return any(all(litval(l,x) for l in units) and all(any(litval(l,x) for l in c) for c in clauses) for x in range(1<<n))

def compile_core(n,base,hard):
    L=list(range(1,n+1))+list(range(-n,0)); adj={l:{l} for l in L}
    for c in base:
        a,b=(c[0],c[-1]); adj[-a].add(b);adj[-b].add(a)
    for z in L:
        for a in L:
            if z in adj[a]: adj[a]|=adj[z]
    ok=not any(-a in adj[a] and a in adj[-a] for a in L)
    def compat(a,b): return -b not in adj[a]
    H=[tuple(a for a in c if compat(a,a)) for c in hard]
    edges={(i,j) for i in range(len(H)) for j in range(i+1,len(H)) if any(not compat(a,b) for a in H[i] for b in H[j])}
    # A greedy vertex cover; optimality not required for the bound.
    left=set(edges); cover=[]
    while left:
        v=max(range(len(H)),key=lambda v:sum(v in e for e in left));cover.append(v);left={e for e in left if v not in e}
    rest=[i for i in range(len(H)) if i not in cover]
    assert all(not(i in rest and j in rest) for i,j in edges)
    def evaluate(units):
        closure=set().union(*(adj[a] for a in units)) if units else set()
        if not ok or any(-a in closure for a in closure): return False,False
        allowed=[tuple(a for a in c if -a not in closure) for c in H]
        full=any(all(compat(a,b) for a,b in combinations(sel,2)) for sel in product(*allowed))
        reduced=False
        for sel in product(*(allowed[i] for i in cover)):
            if all(compat(a,b) for a,b in combinations(sel,2)) and all(any(all(compat(a,b) for b in sel) for a in allowed[i]) for i in rest):
                reduced=True;break
        return full,reduced
    return evaluate,len(cover),len(edges)

def run():
    rng=random.Random(20261126);checks=0; instances=0; cover_savings=0; unsat=0
    for n in range(1,8):
        for t in range(160):
            lits=[i*s for i in range(1,n+1) for s in (-1,1)]
            base=[tuple(rng.choice(lits) for _ in range(rng.choice((1,2,2)))) for _ in range(rng.randrange(0,2*n+1))]
            hard=[tuple(rng.choice(lits) for _ in range(3)) for _ in range(rng.randrange(0,7))]
            eval,c,e=compile_core(n,base,hard);instances+=1;cover_savings+=c<len(hard)
            unsat+=not sat(n,base,[])
            m=min(n,4)
            for bits in product((-1,1),repeat=m):
                units=[(i+1)*s for i,s in enumerate(bits)]
                expected=sat(n,base+hard,units)
                assert eval(units)==(expected,expected),(n,base,hard,units,eval(units),expected)
                checks+=1
    print(f'random instances={instances}, input checks={checks}, cover smaller than hard-clause count={cover_savings}, unsatisfiable bases={unsat}')
    # Exhaustively test all subsets of the 8 non-tautological unit/binary clauses on two vars.
    lits=(-2,-1,1,2); clauses=[(a,) for a in lits]+[(a,b) for a,b in combinations(lits,2) if a!=-b]
    k=0
    for mask in range(1<<len(clauses)):
        base=[c for i,c in enumerate(clauses) if mask>>i&1]
        for hard in [[],[(1,-2,2)],[(-1,2,2)],[(1,1,2),(-1,-2,-2)]]:
            ev,_,_=compile_core(2,base,hard)
            for bits in product((-1,0,1),repeat=2):
                units=[(i+1)*s for i,s in enumerate(bits) if s]
                expected=sat(2,base+hard,units)
                assert ev(units)==(expected,expected)
                k+=1
    print(f'exhaustive two-variable partial-unit checks={k}')
if __name__=='__main__': run()

```

---

# Previous research (retained for reference)

# Research handoff — quantitative verifier bridge and bounded-occurrence SAT restrictions

**Read only this new section first.** The research direction has changed from residual-family counts to existential projection of sparse constraints. New paper result: an explicit `O(n log^2 n)`-gate nondeterministic verifier for the exact pequalnp encoding, with `O(n log n)` witness bits, and a reverse coordinate-restriction compiler into 3-CNF of occurrence degree at most five. These imply equality of worst-case polynomial exponents (not an exact equivalence at the critical exponent 1.01). This is an elementary quantitative reformulation, not a new superlinear circuit lower bound or a claimed literature novelty. The proofs and code are below. The code is for auditing; do not port it into the native synthesis constructor.

## 0. Current repository and Lean status (2026-11-26)

Read-only inspection at [e05533d914b25af59b9814c771b17feb9b1f1766](https://github.com/Krapples/circuit-synthesis-research/commit/e05533d914b25af59b9814c771b17feb9b1f1766). Both requested notes read again after the experiments: `sat-search/NOTES_ORIENTATION_QUOTIENT.md` blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`; `RESEARCH_NOTES.md` blob `96ee7ae211c13513b1ddb4ab7a07af4850761328`. The latter records the completed robust-identifier proof in `SatBridge`. I inspected `SatBridge/RobustIdentifier.lean` lines 238–246: `sat_robust_identifier_eventually` proves that for each positive integer m, every sufficiently long length `n=6*(Q+1)` has `2*m*n <= m*D.size+n` for circuits deciding the external SAT function in the counted fan-in-two AND/OR/NOT model. Thus every fixed slope less than two eventually holds on that subsequence. The explicit loss is also reported checked; the analytic `O(n log log n/log n)` rate is a paper consequence, not a claim that an asymptotic Landau theorem was separately checked. I did not rerun Lean locally. No external submission or repository edits were made.

**Do not duplicate** the robust table counting, helper identity, coordinate layout, model transfer, XNOR, excess, robust block-product, or multiples-of-six theorems. The main remaining Lean gaps listed in the repository are full support and tails at other even lengths, and the 17/12 additive-weight chain. The existing checked result already suffices to exclude every fixed slope less than two in an asymptotic SAT size bound. If stronger finite-size bounds or all-even-length statements are desired, finish the even support certificate and additive-weight chain; the recurrence does not need Percy exact minima. Do not claim that this closes L-clb-036. No new proof submission without the project's required process.

## 1. A nondeterministic verifier for the exact SAT encoding

Let `n=2t>=2`, `w=ceil(log2(t+1))`, and `p` be the least power of two >= t. A nondeterministic AIG is an ordinary AIG `V(x,z)` with a specified ordinary-input block x and existential witness block z, computing `f(x)=exists z, V(x,z)=1`. Gates count ANDs with free complements and constants; the witness bits are not advice dependent on the input alone without verification. The new construction gives a verifier for the *whole* encoded SAT slice, including malformed words, rather than just the previous unit-clause restriction.

**Theorem.** `SAT_n` has a nondeterministic AIG of `O(n log^2(n+2))` gates and `O(n log(n+2))` witness bits. The construction is uniform in n. Odd lengths are constantly false; handle the empty word separately. This is NOT a deterministic upper bound on SAT.

### A. Local parser and guessed trie labels

Tokens are consecutive pairs. Between literals, `1s` starts a literal of sign s, `00` terminates the clause, and `01` is illegal. Within a literal, `1d` appends the next LSB-first identifier digit, `01` ends the literal, and `00` is illegal. A nonempty digit string must end in 1, so Nat.bits is canonical; zero has the empty digit string. The parser checks these conditions and that the final clause is closed. Reject empty clauses (unsatisfiable). This is an ordinary finite-state scan except for the label register described next.

Guess one w-bit child label and one truth bit per token (ignore them when inappropriate). The label register starts at zero at each literal start. On a digit d, emit active transition record `(parent label, d; child label)` and update register to child. On literal termination, emit active terminal record `(current label; truth bit)`. Track the sign and whether at least one literal in the current clause is satisfied by its guessed truth bit. Reject a clause terminator unless satisfied. Unroll t scan steps using O(w) ANDs per step, O(tw) total, with O(w) bits per record; each token has one slot in each of two record arrays with an active flag. No large numeric variable ID needs to be stored or compared directly.

Check the following two functional-dependency conditions:

* equal active transition keys `(parent,digit)` have equal child labels;
* equal active terminal labels have equal truth bits.

**Soundness:** any accepting certificate defines a partial deterministic transition map on label/digit pairs. By induction on identifier digits, occurrences of exactly the same identifier end at exactly the same label (start at 0 every time). Terminal consistency gives a well-defined variable assignment on all occurring identifiers; clauses pass the scan only if satisfied by it. Different identifiers may accidentally merge into one label, and cycles among labels are allowed. Neither can create a false satisfying assignment: they impose extra equalities, not fewer. The parser rejects noncanonical spellings and malformed words. **Completeness:** from a satisfying assignment choose one distinct label for each distinct digit prefix, including root zero. There are at most t+1 prefixes because there are at most t digit tokens. w bits suffice. Choose the assignment's actual variable value at each terminal. Both consistency conditions pass. Thus guessed trie labels avoid pairwise comparisons of variable-length identifiers while preserving exact semantics.

### B. Checking the records

One straightforward implementation uses bitonic sorting networks on p records, key `(active flag, parent,digit)` or `(active flag,label)`, active first. After sorting, check adjacent records with equal active keys for equal payloads. `O(p log^2 p)` comparators, `O(w)` gates each, gives `O(n log^3 n)` gates and `t(w+1)` witness bits. This version is implemented as `verifier(n)` below.

A smaller nondeterministic version guesses the switches of a rearrangeable Beneš permutation network instead of deterministically sorting. A p-port network has `p log2 p-p/2` binary swap switches for p>=2 and zero for p=1. Each switch costs at most 6 ANDs per record bit (two multiplexers). Add two such witness-controlled networks, one for each record array, padding with inactive records to p slots. Require active records to be in nondecreasing key order, preceding inactive ones (ignore order between inactive slots), and check adjacent equal active keys have equal payloads. Every switch setting permutes the records, so no witness can delete, duplicate or change a record. Conversely some setting sorts any given array. This proves soundness and completeness of the guessed sort. Costs: O(p log p * w) gates for routing, O(pw) for comparisons; O(tw + p log p) witness bits. The total is the claimed O(n log^2 n) gates and O(n log n) witness bits.

For completeness, rearrangeability follows recursively. For any desired permutation, draw one edge per input connecting its input pair to its required output pair. This is a bipartite degree-two multigraph (parallel edges allowed), hence its cycles have alternating two-colorings. First-layer switches send edges of the two colors into separate p/2-port subnetworks. Each color defines a bijection between pairs, routed recursively. The final switches send each edge to its specified output port. Base p=2 is one switch. This is the standard Beneš construction, not a new switching-network theorem; see [Beneš 1964](https://doi.org/10.1002/j.1538-7305.1964.tb04102.x). The recursive count is `T(p)=p+2T(p/2)` for p>=4, `T(2)=1`. The reference route algorithm explicitly colors the edges by alternating between the two pair matchings.

## 2. Reverse bridge: bounded-occurrence 3-CNF as a coordinate restriction

Let V be any nondeterministic AIG with m ordinary inputs, h witness inputs, g gates and S=m+h+g>=1. We count S, not just the gate count (this avoids free-input degeneracies). Make a CNF with one variable per primary or gate wire plus variable zero constrained false. For gate `z=a AND b` (a,b are possibly negated literals) use clauses `(NOT z OR a)`, `(NOT z OR b)`, `(z OR NOT a OR NOT b)`. Assert the possibly complemented output literal true by a unit clause. For each ordinary input i append a unit clause forcing its variable to x_i. This is the usual Tseitin definitional encoding. Constants are literals on the forced-false variable, with positive sign for false and negative sign for true. Induction in topological order proves that the CNF is satisfiable exactly if there exists a witness for V(x,z)=1. The CNF has `L=7g+m+2` literal occurrences, including the false-constant and output units (unused witnesses can be removed). Its encoding uses O(S log(S+2)) bits. Only the sign token's second bit in each of the m input unit clauses varies with x; all other bits and the length are fixed. Therefore the reduction is a coordinate restriction, **not** an input-computation circuit. No reduction gate cost is charged to the lower-bound transfer.

**Strengthening.** The CNF can be required to have at most three literals per clause and at most five occurrences per variable (count signs together), still with O(S) literal occurrences and the same sign-only restriction. For each variable with d occurrences, replace each occurrence by its own fresh variable. Join the d copies in a path by equality clauses `(NOT u OR v)` and `(u OR NOT v)` on each link. Each new variable appears once in an original clause and at most four times in equality clauses, so degree <=5. Equality paths enforce all copies equal; the original clauses are satisfied iff the transformed ones are. Make all equality clauses fixed and put the m input units at the end, retaining one independent free sign per input. There are exactly L fresh variables, at most L links, and at most 5L total literal occurrences. Assign fresh identifiers 1..L. A literal word has length at most `4+2 ceil(log2(L+1))`; each nonempty clause adds two bits; hence the resulting binary length is at most `5L*(6+2 ceil(log2(L+1)))`. This explicit bound also covers constant outputs and unused inputs. Our code tests both the original and bounded-occurrence compiler against direct existential evaluation. No bounded-treewidth assumption is made; bounded occurrence does not force low treewidth.

## 3. Quantitative equivalence of polynomial exponents

Define three monotone worst-case quantities (include 1 in the maxima so logarithms are defined):

* `T(N)=max(1,C(SAT_n): 1<=n<=N)` in the deterministic free-phase AIG model.
* `D(S)=max(1,C(f): f has a nondeterministic AIG V with total ordinary inputs + witness inputs + gates <= S)`.
* `H(L)=max(1,C(f_P): P is a fixed width-at-most-three CNF template with <=L total literal occurrences including distinguished input units, occurrence degree <=5, and f_P(x)=SAT(P with its distinguished units set by x))`. Here each free bit is one independent sign on a unit clause, no free input outside these units, and the designated variables are distinct. Empty clauses, if included, only yield constant functions; otherwise every variable can be numbered using <=L distinct indices.

By the two bridges, for absolute constants a,b,c>0 and sufficiently large integer parameters:

    D(S) <= H(a*S)
    H(L) <= T(b*L*log2(L+2))
    T(N) <= D(c*N*log2(N+2)^2).

There is also `H(L)<=D(O(L))`: guess a truth bit for every occurring variable, check the fixed clauses and the equality of each distinguished variable to its ordinary input. Fan-in-two OR/AND on at most L literals plus the unit checks uses O(L) gates and O(L) input/witness bits. The forward verifier's odd-length and constant cases are trivial. This gives the equal exponents

    limsup log(T(N))/log(N) = limsup log(D(S))/log(S)
                            = limsup log(H(L))/log(L).

Proof: the three inequalities in the cycle show that each exponent is at most the next, since scaling the argument by a constant and fixed powers of logarithms changes its logarithm by a factor 1+o(1). This also works when the common limsup is infinite. Nonuniform circuits suffice; the worst-case functions in D and H need not be a uniformly generated family. For the external counted AND/OR/NOT basis, the checked `transfer` gives AIG size no larger; conversely an AIG with n ordinary inputs and g gates can be compiled using O(n+g+1) counted gates (one shared complement per used wire and constant realizations from any input, n>=1). Thus exponents agree when using that basis for T. The statement is asymptotic and does not rely on quirks at input length zero.

### Exactly what would suffice for L-clb-036

The conjecture rules out an O(n^1.01) deterministic circuit size bound for SAT. From the forward reduction, if SAT had such circuits, **every** nondeterministic AIG of total size S would have a deterministic equivalent with `O((S log(S+2))^1.01)` gates, with a common constant. Consequently any of the following would suffice to rule out that SAT bound:

* `D(S)` or `H(S)` is not `O((S log(S+2))^1.01)`;
* an infinite family of fixed bounded-occurrence 3-CNF sign templates with L literal occurrences whose projection functions need `Omega(L^(1.01+epsilon))` deterministic gates for some fixed epsilon>0;
* in particular a family with O(m polylog m) occurrences and `Omega(m^(1.01+epsilon))` deterministic gate lower bounds, where m is the number of independently free sign bits.

Conversely, if the conjecture is true, then `D(S)` and `H(S)` cannot have an O(S^(1+epsilon)) upper bound for any fixed epsilon<0.01: such an upper bound would imply `T(N)=O((N log^2 N)^(1+epsilon))=o(N^1.01)`. This is a necessary consequence, not a sufficient proof of the conjecture. At the exact exponent 1.01 the logarithmic overheads matter: equality of limsup exponents alone does NOT settle L-clb-036. No separation of the required strength has been proved. A counting argument over sparse templates is not enough: the number of templates with L occurrences and renumbered variables is at most `2^O(L log L)`, so counting their descriptions against larger arbitrary circuits cannot force the desired polynomial separation. Do not infer a lower bound from bounded occurrence, expansion, or high treewidth alone.

This reformulation is closer to the real target than the fixed-interface encoder theorems. It does not assume any particular topology of the deterministic circuit being lower-bounded. One research direction is to find explicit sparse fixed constraint systems whose existential projection is provably harder to compute deterministically than their verifier (e.g. investigate high-treewidth bounded-occurrence templates as candidates, not as proved hard functions). Another is to study quantitative simulation of nondeterministic AIGs by deterministic circuits; a near-linear simulation would obstruct the conjecture rather than prove it. No algorithm-to-lower-bound theorem is being invoked without its hypotheses. General unrestricted superlinear lower bounds remain the obstacle.

## 4. Executed finite verification

Two standalone stdlib files below. Run `python bridge.py` then `python route_check.py` in the same directory. They create actual AIGs and evaluate bitpacked assignments; the abstract checker has an independent parser and DPLL. Results:

* All 5,460 nonempty even words of length <=12 (two chosen certificates each), plus 500 larger samples, total **11,920** comparator-network gate evaluations. 132 satisfiable instances with accepted constructed certificates, 5,828 rejected instances with attempted certificates, and 5,960 arbitrary certificates compared to the abstract consistency checker. This is not exhaustive witness enumeration at all these lengths.
* **1,438** reverse coordinate restrictions from 200 random nondeterministic AIGs, each checked on all ordinary inputs and direct existential witness enumeration; another **1,438** with occurrence splitting, checked clause width, variable occurrences, sign-only coordinate positions and fixed encoding length. Initial constant-literal polarity was reversed in the first test; corrected, all final tests pass.
* **44,347** permutation-routing tests: every permutation for p=1,2,4,8 and 1,000 each at p=16,32,64,128. All route settings checked as actual permutations.
* **24,934** guessed-sort gate evaluations with constructed and arbitrary switch settings, all agree for sorted certificates; arbitrary settings never accept unless the abstract checker accepts. 192 accepted constructed sorted certificates, one accepted arbitrary setting. In debugging the additional planted tests accidentally used contradictory unit clauses and a mismatched digit-key endianness; corrected both and reran.
* **37,920** exhaustive input-plus-witness assignments at tiny sizes (plain n=2,4,6 and routed n=2,4), with acceptance over all witnesses compared to actual SAT. **12** long-identifier cases, including identical identifiers with opposing signs and distinct identifiers with shared prefixes, through 65 digit bits. All pass.

Illustrative constructed verifier sizes (not exact minima; free AND counts, with simplification/hash-consing):

| n | deterministic comparator network | guessed permutation network | latter witness bits |
|---:|---:|---:|---:|
| 16 | 4,010 | 2,755 | 80 |
| 32 | 15,475 | 8,585 | 208 |
| 64 | 52,468 | 24,311 | 512 |
| 128 | 164,029 | 64,997 | 1,216 |

The finite tests support the implementation, not the proof of the asymptotic result. No deterministic SAT upper bound, new unrestricted circuit minimum, native throughput benchmark, Lean verification of this new theorem, or novelty claim. Both repo notes checked again; no repo edits.

## 5. Runnable code

### `bridge.py`

```python
from itertools import product
from random import Random

# AIG literal: 0/1 constants, 2*i input i (1-based), complement via ^1.
class AIG:
    def __init__(self,n): self.n=n; self.g=[]; self.cache={}
    def AND(self,a,b):
        if a==0 or b==0 or a==b^1:return 0
        if a==1 or a==b:return b
        if b==1:return a
        k=tuple(sorted((a,b)))
        if k not in self.cache:
            self.g.append(k);self.cache[k]=2*(self.n+len(self.g))
        return self.cache[k]
    def OR(self,a,b):return self.AND(a^1,b^1)^1
    def XOR(self,a,b):return self.OR(self.AND(a,b^1),self.AND(a^1,b))
    def EQ(self,a,b):return self.XOR(a,b)^1
    def mux(self,s,a,b):return self.OR(self.AND(s,a),self.AND(s^1,b))
    def fold(self,op,seq,init):
        for v in seq:init=op(init,v)
        return init
    def eqvec(self,a,b):return self.fold(self.AND,(self.EQ(x,y) for x,y in zip(a,b)),1)
    def lt(self,a,b):
        # little-endian unsigned less-than
        r=0
        for x,y in zip(a,b):r=self.OR(self.AND(x^1,y),self.AND(self.EQ(x,y),r))
        return r
    def eval_batch(self,out,rows):
        mask=(1<<len(rows))-1
        v=[0]+[sum(((row>>i)&1)<<j for j,row in enumerate(rows)) for i in range(self.n)]
        def get(l):return v[l//2]^(mask if l&1 else 0)
        for a,b in self.g:v.append(get(a)&get(b))
        return get(out)

def sort_records(c,rs,keylen):
    # Batcher bitonic sorting, records have keys in their first keylen slots,
    # little-endian; pad with an inactive record (top key bit is 1).
    k=len(rs[0]);p=1<<(len(rs)-1).bit_length();a=list(rs)+[(0,)*(keylen-1)+(1,)+(0,)*(k-keylen)]*(p-len(rs))
    step=2
    while step<=p:
        j=step//2
        while j:
            for i in range(p):
                h=i^j
                if h<=i:continue
                x,y=a[i],a[h]
                sw=c.lt(y[:keylen],x[:keylen]) if i&step==0 else c.lt(x[:keylen],y[:keylen])
                a[i]=tuple(c.mux(sw,v,u) for u,v in zip(x,y))
                a[h]=tuple(c.mux(sw,u,v) for u,v in zip(x,y))
            j//=2
        step*=2
    return a

def consistent(c,rs,keylen):
    rs=sort_records(c,rs,keylen);ok=1
    for a,b in zip(rs,rs[1:]):
        same=c.AND(a[keylen-1]^1,c.eqvec(a[:keylen],b[:keylen]))
        ok=c.AND(ok,c.OR(same^1,c.eqvec(a[keylen:],b[keylen:])))
    return ok

def switch_count(p):
    return p*(p.bit_length()-1)-p//2 if p>1 else 0

def benes(c,rs,controls):
    p=len(rs)
    def pair(a,b):
        sw=next(controls)
        return (tuple(c.mux(sw,v,u) for u,v in zip(a,b)),
                tuple(c.mux(sw,u,v) for u,v in zip(a,b)))
    if p==1:return list(rs)
    if p==2:return list(pair(*rs))
    pairs=[pair(rs[i],rs[i+1]) for i in range(0,p,2)]
    u=benes(c,[a for a,b in pairs],controls);v=benes(c,[b for a,b in pairs],controls)
    return [q for a,b in zip(u,v) for q in pair(a,b)]

def consistent_routed(c,rs,keylen,controls):
    k=len(rs[0]);p=1<<(len(rs)-1).bit_length()
    rs=benes(c,list(rs)+[(0,)*(keylen-1)+(1,)+(0,)*(k-keylen)]*(p-len(rs)),controls)
    ok=1
    for a,b in zip(rs,rs[1:]):
        ok=c.AND(ok,c.OR(b[keylen-1],c.lt(b[:keylen],a[:keylen])^1))
        same=c.AND(a[keylen-1]^1,c.eqvec(a[:keylen],b[:keylen]))
        ok=c.AND(ok,c.OR(same^1,c.eqvec(a[keylen:],b[keylen:])))
    return ok

def verifier(n,routed=False):
    assert n>=2 and n%2==0
    t=n//2;w=t.bit_length();p=1<<(t-1).bit_length()
    c=AIG(n+t*(w+1)+(2*switch_count(p) if routed else 0));z=[2*(i+1) for i in range(c.n)]
    inside=has=last=opened=csat=sign=0;node=(0,)*w;ok=1;ds=[];ls=[]
    for i in range(t):
        a,b=z[2*i:2*i+2];child=tuple(z[n+i*(w+1):n+i*(w+1)+w]);value=z[n+i*(w+1)+w]
        start=c.AND(inside^1,a);digit=c.AND(inside,a)
        end=c.AND(inside,c.AND(a^1,b));close=c.AND(inside^1,c.AND(a^1,b^1))
        ok=c.AND(ok,c.fold(c.OR,(start,digit,end,close),0))
        ok=c.AND(ok,c.OR(end^1,c.OR(has^1,last)))
        ok=c.AND(ok,c.OR(close^1,csat))
        ds.append(node+(b,digit^1)+child);ls.append(node+(end^1,value))
        csat=c.AND(close^1,c.OR(csat,c.AND(end,c.EQ(value,sign))))
        opened=c.AND(close^1,c.OR(opened,start))
        node=tuple(c.mux(start,0,c.mux(digit,v,u)) for u,v in zip(node,child))
        sign=c.mux(start,b,sign);has=c.AND(start^1,c.OR(has,digit));last=c.mux(digit,b,last)
        inside=c.OR(start,c.AND(inside,end^1))
    ok=c.AND(ok,c.AND(inside^1,opened^1))
    if routed:
        controls=iter(z[n+t*(w+1):])
        ok=c.AND(ok,consistent_routed(c,ds,w+2,controls));ok=c.AND(ok,consistent_routed(c,ls,w+1,controls))
        assert next(controls,None) is None
    else:
        ok=c.AND(ok,consistent(c,ds,w+2));ok=c.AND(ok,consistent(c,ls,w+1))
    return c,ok,w

def decode(s):
    # independent parser, returns clauses of (identifier, sign, digit positions, end token)
    if len(s)%2:return None
    tok=[s[i:i+2] for i in range(0,len(s),2)];i=0;clauses=[];cl=[]
    while i<len(tok):
        h=tok[i];i+=1
        if h=='00':clauses.append(cl);cl=[];continue
        if h not in ('10','11'):return None
        digs=[];pos=[]
        while i<len(tok) and tok[i][0]=='1':digs.append(int(tok[i][1]));pos.append(i);i+=1
        if i==len(tok) or tok[i]!='01' or (digs and not digs[-1]):return None
        cl.append((sum(b<<j for j,b in enumerate(digs)),h=='11',pos,i));i+=1
    return None if cl else clauses

def solve(cs):
    if cs is None:return None
    clauses=[[(v,s) for v,s,*_ in cl] for cl in cs]
    def rec(cs,env):
        if not cs:return env
        if any(not cl for cl in cs):return None
        v=cs[0][0][0]
        for b in (False,True):
            got=rec([[(u,s) for u,s in cl if u!=v] for cl in cs if (v,b) not in cl],env|{v:b})
            if got is not None:return got
        return None
    return rec(clauses,{})

def cert(s,w,env=None,force_each=False):
    cs=decode(s);t=len(s)//2;out=[0]*t;prefix={():0}
    if cs is None:return 0
    for cl in cs:
        for v,sign,pos,end in cl:
            p=()
            for i in pos:
                p=p+(int(s[2*i+1]),)
                if p not in prefix:prefix[p]=len(prefix)
                out[i]=prefix[p]
            out[end]=int(sign if force_each else (env or {}).get(v,False))<<w
    return sum(x<<(i*(w+1)) for i,x in enumerate(out))

def abstract_check(s,w,certbits):
    cs=decode(s)
    if cs is None:return False
    ds={};ls={}
    for cl in cs:
        satisfied=False
        for v,sign,pos,end in cl:
            node=0
            for i in pos:
                b=int(s[2*i+1]);child=(certbits>>(i*(w+1)))&((1<<w)-1)
                if (node,b) in ds and ds[node,b]!=child:return False
                ds[node,b]=child;node=child
            value=bool((certbits>>(end*(w+1)+w))&1)
            if node in ls and ls[node]!=value:return False
            ls[node]=value;satisfied|=(value==sign)
        if not satisfied:return False
    return True

def encode_clause(cl):
    def literal(v,s):
        digs=bin(v)[2:][::-1] if v else ''
        return ('11' if s else '10')+''.join('1'+b for b in digs)+'01'
    return ''.join(literal(v,s) for v,s in cl)+'00'

def split_occurrences(cs):
    # One variable per literal occurrence, equality path for each original.
    prev={};eq=[];replaced=[];count=0
    for cl in cs:
        new=[]
        for v,s in cl:
            count+=1;u=count
            if v in prev:
                p=prev[v];eq.extend([[(p,False),(u,True)],[(p,True),(u,False)]])
            prev[v]=u;new.append((u,s))
        replaced.append(new)
    return eq+replaced

def reduce_to_sat(c,out,m,x,bounded=False):
    # literal l=0 or 1 represents false/true via forced-false variable 0.
    def l(lit):return (lit//2,not bool(lit&1)) if lit>=2 else (0,not bool(lit))
    def neg(lit):return (lit[0],not lit[1])
    cs=[[(0,False)]]
    for i,(a,b) in enumerate(c.g,c.n+1):
        z=(i,True);a,b=l(a),l(b)
        cs.extend([[neg(z),a],[neg(z),b],[z,neg(a),neg(b)]])
    cs.append([l(out)])
    cs.extend([[(i+1,bool(x>>i&1))] for i in range(m)])
    if bounded:cs=split_occurrences(cs)
    return ''.join(map(encode_clause,cs))

def packed(s,certbits):return sum(int(b)<<i for i,b in enumerate(s)) | (certbits<<len(s))

def main():
    rng=Random(261126);rows_checked=positive=negative=badcert=0
    for n in range(2,14,2):
        c,out,w=verifier(n);rows=[];expected=[]
        for bits in product('01',repeat=n):
            s=''.join(bits);cs=decode(s);env=solve(cs);accept=env is not None
            a=cert(s,w,env,force_each=not accept)
            assert abstract_check(s,w,a)==accept
            rows.append(packed(s,a));expected.append(accept);positive+=accept;negative+=not accept
            b=rng.getrandbits((n//2)*(w+1));rows.append(packed(s,b));expected.append(abstract_check(s,w,b));badcert+=1
        assert c.eval_batch(out,rows)==sum(v<<j for j,v in enumerate(expected));rows_checked+=len(rows)
        print('exhaustive n, gates, rows',n,len(c.g),len(rows))
    for n in (16,24,32,48,64):
        c,out,w=verifier(n);rows=[];expected=[]
        for k in range(100):
            # generate legal CNFs of <=n bits, pad with legal unit clauses if possible.
            s=''.join(rng.choice('01') for _ in range(n))
            if k%2==0:
                s='';tries=0
                while len(s)<n and tries<50:
                    tries+=1;cl=[(rng.randrange(4),bool(rng.randrange(2))) for _ in range(rng.randrange(1,4))];a=encode_clause(cl)
                    if len(s)+len(a)<=n:s+=a
                if len(s)!=n:s=s+'0'*(n-len(s))
            cs=decode(s);env=solve(cs);accept=env is not None
            a=cert(s,w,env,force_each=not accept)
            assert abstract_check(s,w,a)==accept
            rows.append(packed(s,a));expected.append(accept);positive+=accept;negative+=not accept
            b=rng.getrandbits((n//2)*(w+1));rows.append(packed(s,b));expected.append(abstract_check(s,w,b));badcert+=1
        assert c.eval_batch(out,rows)==sum(v<<j for j,v in enumerate(expected));rows_checked+=len(rows)
        print('random n, gates, rows',n,len(c.g),len(rows))
    # Planted repeated identifiers with conflicting truth values, and arbitrary cert collisions.
    # Reverse bridge: exhaustive input/witness evaluation for random nondet AIGs.
    reductions=0;bounded_reductions=0
    for _ in range(200):
        m=rng.randrange(1,5);w=rng.randrange(0,4);c=AIG(m+w);ls=list(range(2*(m+w+1)))
        for j in range(rng.randrange(0,9)):
            z=c.AND(rng.choice(ls),rng.choice(ls));ls.extend([z,z^1])
        out=rng.choice(ls);tab=c.eval_batch(out,list(range(1<<(m+w))));template=None;bounded_template=None
        for x in range(1<<m):
            s=reduce_to_sat(c,out,m,x);exp=any(tab>>(x|(y<<m))&1 for y in range(1<<w))
            assert (solve(decode(s)) is not None)==exp
            if template is None:template=s
            else:assert len(s)==len(template)
            # Last m unit clauses vary only sign token bit; all other bits fixed.
            positions=[];off=len(s)-sum(len(encode_clause([(i+1,False)])) for i in range(m))
            for i in range(m):positions.append(off+1);off+=len(encode_clause([(i+1,False)]))
            assert all(s[i]==template[i] for i in range(len(s)) if i not in positions)
            assert all(int(s[i])==((x>>j)&1) for j,i in enumerate(positions))
            reductions+=1
            s=reduce_to_sat(c,out,m,x,True);cs=decode(s)
            assert (solve(cs) is not None)==exp
            from collections import Counter
            occ=Counter(v for cl in cs for v,*_ in cl)
            assert max(occ.values())<=5 and max(map(len,cs))<=3
            units=[[(v,sign) for v,sign,*_ in cl] for cl in cs[-m:]]
            positions=[];off=len(s)-sum(len(encode_clause(cl)) for cl in units)
            for cl in units:positions.append(off+1);off+=len(encode_clause(cl))
            if bounded_template is None:bounded_template=s
            assert len(s)==len(bounded_template)
            assert all(s[i]==bounded_template[i] for i in range(len(s)) if i not in positions)
            assert all(int(s[i])==((x>>j)&1) for j,i in enumerate(positions))
            bounded_reductions+=1
    print('PASS',dict(verifier_rows=rows_checked,sat_witnesses=positive,rejected_instances=negative,random_certs=badcert,reverse_restrictions=reductions,bounded_occurrence_restrictions=bounded_reductions))

if __name__=='__main__':main()

```

### `route_check.py`

```python
from bridge import *
from itertools import permutations

def route(perm):
    """perm[input]=output, controls in recursive switch traversal order."""
    p=len(perm)
    if p==1:return []
    if p==2:return [perm[0]]
    inv=[0]*p
    for i,j in enumerate(perm):inv[j]=i
    color=[-1]*p
    for i in range(p):
        if color[i]>=0:continue
        color[i]=0;todo=[i]
        while todo:
            j=todo.pop()
            for k in (j^1,inv[perm[j]^1]):
                if color[k]<0:color[k]=1-color[j];todo.append(k)
                else:assert color[k]==1-color[j]
    a=[0]*(p//2);b=[0]*(p//2)
    for i,j in enumerate(perm):(a,b)[color[i]][i//2]=j//2
    return color[::2]+route(a)+route(b)+[color[inv[j]] for j in range(0,p,2)]

def apply(rs,it):
    n=len(rs)
    if n==1:return list(rs)
    def swap(a,b):return (b,a) if next(it) else (a,b)
    if n==2:return list(swap(*rs))
    pairs=[swap(rs[i],rs[i+1]) for i in range(0,n,2)]
    u=apply([a for a,b in pairs],it);v=apply([b for a,b in pairs],it)
    return [q for a,b in zip(u,v) for q in swap(a,b)]

def sort_controls(keys):
    ids=sorted(range(len(keys)),key=keys.__getitem__);perm=[0]*len(ids)
    for i,j in enumerate(ids):perm[j]=i
    return route(perm)

def record_keys(s,w,a):
    cs=decode(s);t=len(s)//2;p=1<<(t-1).bit_length();ds=[(1,0,0)]*p;ls=[(1,0)]*p
    if cs is None:return ds,ls
    for cl in cs:
        for _,_,pos,end in cl:
            node=0
            for i in pos:
                bit=int(s[2*i+1]);ds[i]=(0,bit,node)
                node=(a>>(i*(w+1)))&((1<<w)-1)
            ls[end]=(0,node)
    return ds,ls

def routed_cert(s,w,a):
    ds,ls=record_keys(s,w,a);bits=sort_controls(ds)+sort_controls(ls)
    return a|(sum(b<<i for i,b in enumerate(bits))<<((len(s)//2)*(w+1)))

def main():
    rng=Random(261127);routes=0
    for p in (1,2,4,8,16,32,64,128):
        ps=permutations(range(p)) if p<=8 else (rng.sample(range(p),p) for _ in range(1000))
        for perm in ps:
            cs=route(perm);assert len(cs)==switch_count(p);it=iter(cs);out=apply(list(range(p)),it)
            assert all(out[j]==i for i,j in enumerate(perm)) and next(it,None) is None;routes+=1
    tested=0;accepted=0;arbitrary_accepted=0
    for n in (2,4,6,8,10,12,16,24,32,48,64,96,128):
        c,out,w=verifier(n,True);plain,_,_=verifier(n);rows=[];exp=[];source=[];arb=[]
        words=map(''.join,product('01',repeat=n)) if n<=12 else (''.join(rng.choice('01') for _ in range(n)) for _ in range(100))
        for s in words:
            env=solve(decode(s));a=cert(s,w,env,force_each=env is None)
            for k in (a,rng.getrandbits((n//2)*(w+1))):
                good=abstract_check(s,w,k);r=routed_cert(s,w,k);rows.append(packed(s,r));exp.append(good);source.append((s,k))
                arb.append(packed(s,k|(rng.getrandbits(c.n-n-(n//2)*(w+1))<<((n//2)*(w+1)))))
        # Additional satisfiable words with shared long identifiers and some unsat.
        for j in range(50):
            base=encode_clause([(rng.randrange(1,16),True)])
            if len(base)>n:continue
            s=base+encode_clause([(0,bool(j%2))])*((n-len(base))//6)
            if len(s)!=n:continue
            env=solve(decode(s));a=cert(s,w,env)
            assert env is not None
            rows.append(packed(s,routed_cert(s,w,a)));exp.append(True);source.append((s,a));arb.append(packed(s,a))
        actual=c.eval_batch(out,rows);assert actual==sum(v<<j for j,v in enumerate(exp))
        arbitrary=c.eval_batch(out,arb)
        assert all(not (arbitrary>>j&1) or exp[j] for j in range(len(rows)))
        tested+=2*len(rows);accepted+=sum(exp);arbitrary_accepted+=arbitrary.bit_count()
        print('n, comparator gates, routed gates, routed witness bits, cases',n,len(plain.g),len(c.g),c.n-n,2*len(rows))
    print('PASS',dict(routes=routes,gate_evaluations=tested,accepted_sorted=accepted,accepted_arbitrary=arbitrary_accepted))
    # Exhaustive witnesses, not just a planted certificate, at tiny sizes.
    exact_rows=0
    for routed,n in ((False,2),(False,4),(False,6),(True,2),(True,4)):
        c,out,w=verifier(n,routed);k=c.n-n;size=1<<k
        rows=[x|(z<<n) for x in range(1<<n) for z in range(size)]
        actual=c.eval_batch(out,rows);mask=(1<<size)-1
        for x in range(1<<n):
            s=''.join(str(x>>i&1) for i in range(n))
            assert bool((actual>>(x*size))&mask)==(solve(decode(s)) is not None)
        exact_rows+=len(rows)
    # Large identifiers can be much larger than the label budget. Equal IDs
    # must still agree, while distinct IDs sharing a prefix may differ.
    long_rows=0
    for r in (8,16,32,64):
        a=(1<<r)|rng.getrandbits(r);b=a|(1<<(r+1))
        for cl in ([[(a,True)],[(a,True)]],[[(a,True)],[(a,False)]],[[(a,True)],[(b,False)]]):
            s=''.join(map(encode_clause,cl));c,out,w=verifier(len(s),True)
            env=solve(decode(s));k=cert(s,w,env,force_each=env is None)
            z=routed_cert(s,w,k);assert bool(c.eval_batch(out,[packed(s,z)]))==(env is not None)
            long_rows+=1
    print('PASS extra',dict(exhaustive_input_witness_rows=exact_rows,long_identifier_cases=long_rows))

if __name__=='__main__':main()

```


---

# Prior pending exploratory work (historical appendix)

The following is retained for independent review only. Its dated priority/status statements are superseded by section 0 above. Do not redo now-completed robust SAT formalization. The reviewed C5 encoder cost, joint residual cuts, boundary-sensitive sharing, list-disjointness and interacting clause restrictions are documented in `sat-search/NOTES_SAT_ENCODING_BOUNDS.md`; optional native filters were not adopted because there was no demonstrated end-to-end benefit. Previously reviewed robust identifier proof code has been removed now that the end-to-end multiples-of-six theorem is checked. The earlier all-even-length support certificate and additive-weight calculations are already in the repository's notes/scripts; the remaining Lean work is described above.

# Research handoff — exact universal residual families in quasi-linear circuits

**New paper result (negative control).** Exact shattering of every logarithmic probe by coordinate restrictions, not merely near-maximal residual cardinality or entropy, is compatible with `O(m log^3 m)` unrestricted AIG gates. This does not give a SAT upper bound or solve L-clb-036. No novelty claim or Lean verification. Repository checked read-only at `e73ee0f037dda1b83e84e116463515b579d17b39`; `sat-search/NOTES_ORIENTATION_QUOTIENT.md` and `RESEARCH_NOTES.md` are unchanged (blobs `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`, `677f9cbdfaf642613ef84db92161d1a78c655254`). Agent priority remains the counting and helper-clause premises for the 2n-o(n) SAT theorem, reusing the existing checked `block_restriction_lower`, `transfer`, and L037. Do not implement the following negative control as a native search filter.

## 1. Exact residual-family saturation

For each sufficiently large integer b, there exists a full-support Boolean function f on m=2^b+O(b^2) inputs with an AIG of size O(m log^3 m) such that, for every b-element subset B of its primary inputs, the set of restrictions of f to B obtained by assigning every input outside B is **the entire set of Boolean functions on B**. Thus N(B)=2^(2^b) exactly, not just approximately. This is also true for all smaller probes (extend to a b-set, realize a function ignoring the added variables, then fix them). The elementary necessary condition for the property is m-b>=2^b, because there must be at least one outside assignment for each truth table; the construction uses only O(b^2) more inputs than this necessary minimum. This is a nonuniform existential theorem, not an efficient uniform family generator or a statement about arbitrary fixed outside contexts.

### Construction

Work over F2. Let Q=2^b, s=10(b+1)^2, k=8(b+1)^2, l=ceil(log2 k), c=l(2b+1), m=Q+s+c. Partition primary inputs into a base vector of length Q+s and c control bits grouped into l disjoint groups of 2b+1. Compute the following signals:

* A data vector D x of Q bits, where D=[I_Q | R | 0] and R is a random Q-by-s matrix with independent fair entries. The last c columns are zero.
* k address maps H_j x, each H_j a random b-by-m binary matrix with independent fair entries, mutually independent and independent of R.
* A selector j from l majority gates (one majority of each control group). If j>=k, output 0; otherwise output the D x bit indexed by H_j x. This is one shared data lookup; the selector chooses an address map, not a separate data table for each map.

For any probe B of size b, write P for base coordinates outside B, excluding all controls. We need three simultaneous conditions:

1. D restricted to columns P has row rank Q.
2. For every j, the stacked matrix [D;H_j] restricted to P has row rank Q+b.
3. For every B there exists a j such that H_j restricted to B has rank b.

### Existence proof

For fixed B, a nonzero row combination of D that vanishes on P must have its Q-bit coefficient vector supported on the deleted systematic coordinates. There are fewer than 2^b candidates. For each fixed nonzero combination, its s random parity coordinates are independent fair bits; at least s-b remain in P. Failure probability <=2^(2b-s). Conditional on a fixed D satisfying condition 1, the rows of H_j on P are independent uniform vectors. Their images modulo the Q-dimensional row space of D are independent uniform vectors in a space of dimension |P|-Q>=s-b. For each nonzero combination of the b rows the probability of a zero quotient is at most 2^-(s-b); union bound gives <=2^(2b-s). No conditioning on the rank of H_j on B is necessary: bound the failures of each condition separately. Finally, for fixed B each H_j restricted to B is uniform b-by-b, invertible with probability >=1/4 by the product formula. Failure of all k independent trials has probability <=(3/4)^k.

Since the number of B is <=m^b, the combined failure probability is at most

    m^b * ((k+1)*2^(2b-s) + (3/4)^k).

With m=2^b+O(b^2), log2 m<=b+1 eventually. The first term tends to zero since s=10(b+1)^2 and log2(k+1)=O(log b); the second tends to zero since 8 log2(4/3)>1. Thus for every sufficiently large b the combined failure probability is <1. Fix a single successful family of matrices. This proof makes no independence assumption across probes.

### Programming any target on any probe

Choose B and an arbitrary target truth table T on B. Use condition 3 to choose j. Fix every control bit outside B to the corresponding selector bit of j. Each majority group has at least b+1 fixed entries, so the selector remains j under every probe assignment w. Let c0 denote this fixed control assignment, zero on B. By condition 2 the free base bits outside B can independently set all Q data offsets and the b-bit address offset, after accounting for c0. Set the address offset to zero. Then the address for probe input w is H_j|_B w, a bijection onto the Q addresses. For address a=H_j|_B w set the data offset at a to T(w) XOR (D|_B w)_a. Since w->a is bijective, these prescriptions do not conflict. Solve the full-rank linear system on P for the fixed base assignment. For every w the resulting output is exactly T(w). This allows probes to contain control bits, systematic bits, or random parity bits. No assumption that probes avoid the encoder is made. Since every B can realize a function depending on any chosen member, every primary input is essential.

### AIG cost and limitation

Parity of h bits needs <=3 max(h-1,0) AND gates with free complements. Data encoding costs O(Qs), all address maps O(kbm), majority selectors O(l b^2) by the threshold DP (or cheaper), selecting one b-bit address O(kb), and the final Q-way data mux O(Q). Hence the total is O(m b^3)=O(m log^3 m)=o(m^1.01). No exponential truth-table oracle is hidden in the circuit. In particular the complete residual sets on all probes of size <=b are identical for any other Boolean function having this exact shattering property. Consequently, a proposed universal lower-bound criterion that uses only those sets and their cardinalities, rather than how individual outside assignments map to residual functions or how their realizations are correlated across probes, cannot infer an n^1.01 lower bound from exact saturation alone. The proof does not cover larger probes, arbitrary additional fixed contexts, exact residual mappings, or other semantic circuit measures. The earlier small-probe min-entropy result is complementary, not superseded: it covers larger probes and arbitrary fixed contexts. Neither result is an unrestricted SAT upper bound. The previously proved coordinate Tseitin embedding can transfer this negative control to a restricted SAT instance, with encoding overhead; no new SAT-parser checks this round.

## 2. Executed finite verification

The code below uses smaller parameters than the asymptotic existence proof, tests the weaker sufficient condition that each checked B has at least one usable j (rather than every j satisfying condition 2), and solves the programming equations over GF2. The first trial with smaller hash families (k=8 for b=2) did not find a family covering all probes within 100 attempts; the final parameters were increased. This is not a counterexample to the sufficient asymptotic parameters. The final run:

| b | m | probes | target tables programmed | family attempts | raw AIG gates |
|---:|---:|---:|---:|---:|---:|
|2|45|990 (all)|15,840 (all 16 per probe)|1|3,637|
|3|63|39,711 (all)|39,711 (one sampled per probe)|2|9,563|
|4|89|1,000 sampled|1,000|1|18,262|

41,701 final probe checks; 397,048 programmed assignment evaluations; 300 separately built AIG evaluations. All passed. For b=3 the rank check establishes the programming premises for all probes, even though only one target per probe was evaluated. For b=4 there is no claim of exhaustive probe coverage. The explicit AIG sizes are unoptimized and not evidence of a practical small-size crossover. The asymptotic theorem rests on the union bound and programming proof, not these samples. No repository changes, native benchmarks or new Lean checks.

## 3. Reference implementation (`universal_probe_check.py`)

Extract the following standalone Python 3 code and run it. The finite experiment regenerates random matrices when the checked probes are not covered; the theorem itself does not depend on this search procedure.

```python
from itertools import combinations
from random import Random
from math import ceil,log2

def parity(x):return x.bit_count()&1

def solve(rows, rhs, mask):
    basis={}
    for r,v in zip(rows,rhs):
        r &= mask
        while r:
            i=r.bit_length()-1
            if i not in basis:
                basis[i]=(r,v);break
            a,b=basis[i];r^=a;v^=b
        else:
            if v:return None
    x=0
    for i,(r,v) in sorted(basis.items()):
        if parity(r&x)!=v:x|=1<<i
    return x

def rank(rows):
    basis={}
    for r in rows:
        while r:
            i=r.bit_length()-1
            if i not in basis:basis[i]=r;break
            r^=basis[i]
    return len(basis)

def expand(w,B):return sum((w>>i&1)<<j for i,j in enumerate(B))
def val(rows,x):return sum(parity(r&x)<<i for i,r in enumerate(rows))

class Family:
    def __init__(self,b,s,k,rng):
        self.b=b;self.Q=1<<b;self.s=s;self.k=k;self.l=(k-1).bit_length();self.w=2*b+1
        self.p=self.Q+s;self.n=self.p+self.l*self.w;self.base=(1<<self.p)-1
        self.D=[(1<<i)|(rng.getrandbits(s)<<self.Q) for i in range(self.Q)]
        self.H=[[rng.getrandbits(self.n) for _ in range(b)] for _ in range(k)]
    def selector(self,x):
        return sum((((x>>(self.p+i*self.w))&((1<<self.w)-1)).bit_count()>self.b)<<i for i in range(self.l))
    def eval(self,x):
        j=self.selector(x)
        if j>=self.k:return 0
        return parity(self.D[val(self.H[j],x)]&x)
    def pick(self,B):
        bm=sum(1<<i for i in B);free=self.base&~bm
        for j,H in enumerate(self.H):
            if rank([r&bm for r in H])==self.b and rank([r&free for r in self.D+H])==self.Q+self.b:
                return j
        return None
    def program(self,B,tt,j):
        bm=sum(1<<i for i in B);H=self.H[j];c=0
        for i in range(self.l):
            if j>>i&1:c|=((1<<self.w)-1)<<(self.p+i*self.w)
        c&=~bm
        # Force address offset zero and data register values that compensate for probe-dependent parity.
        rhs=[0]*self.Q
        for w in range(self.Q):
            x=expand(w,B);a=val(H,x)
            rhs[a]=(tt>>w&1)^parity(self.D[a]&x)
        rr=rhs+[parity(r&c) for r in H]
        z=solve(self.D+H,rr,self.base&~bm)
        assert z is not None
        return z|c

class AIG:
    def __init__(self,n):self.n=n;self.g=[]
    def AND(self,a,b):self.g.append((a,b));return 2*(self.n+len(self.g))
    def OR(self,a,b):return self.AND(a^1,b^1)^1
    def XOR(self,a,b):return self.OR(self.AND(a,b^1),self.AND(a^1,b))
    def mux(self,c,a,b):return self.OR(self.AND(c,a),self.AND(c^1,b))
    def par(self,r):
        a=0
        while r:
            bit=r&-r;r^=bit;a=self.XOR(a,2*bit.bit_length()) if a else 2*bit.bit_length()
        return a
    def majority(self,ls):
        d=[1]+[0]*((len(ls)+1)//2)
        for x in ls:
            d=[1]+[self.OR(d[j],self.AND(x,d[j-1])) for j in range(1,len(d))]
        return d[-1]
    def lookup(self,ls,addr):
        for c in addr:ls=[self.mux(c,ls[i+1],ls[i]) for i in range(0,len(ls),2)]
        return ls[0]
    def eval(self,x,out):
        v=[0]+[(x>>i)&1 for i in range(self.n)]
        for a,b in self.g:v.append((v[a//2]^(a&1))&(v[b//2]^(b&1)))
        return v[out//2]^(out&1)

def build(F):
    A=AIG(F.n);D=[A.par(r) for r in F.D];H=[[A.par(r) for r in h] for h in F.H]
    c=[A.majority([2*(F.p+i*F.w+j+1) for j in range(F.w)]) for i in range(F.l)]
    addr=[A.lookup([H[j][i] if j<F.k else 0 for j in range(1<<F.l)],c) for i in range(F.b)]
    # Out-of-range selector returns 0, matching Family.eval.
    ok=A.lookup([int(j<F.k) for j in range(1<<F.l)],c)
    return A,A.AND(ok,A.lookup(D,addr))

def main():
    rng=Random(261126);total=0;assign=0;gchecks=0
    for b,s,k in [(2,16,24),(3,20,32),(4,28,32)]:
        F=Family(b,s,k,rng)
        Bs=list(combinations(range(F.n),b)) if b<=3 else [tuple(sorted(rng.sample(range(F.n),b))) for _ in range(1000)]
        # Regenerate if any selected probe has no usable address map.
        attempts=0
        while True:
            attempts+=1;js=[F.pick(B) for B in Bs]
            if all(j is not None for j in js):break
            F=Family(b,s,k,rng)
            assert attempts<100
        A,o=build(F);count=0
        for B,j in zip(Bs,js):
            # All target tables for b=2, sampled targets otherwise.
            tts=range(1<<F.Q) if b==2 else [rng.getrandbits(F.Q)]
            for tt in tts:
                z=F.program(B,tt,j);assert z&sum(1<<i for i in B)==0
                for w in range(F.Q):
                    x=z|expand(w,B);assert F.eval(x)==(tt>>w&1);assign+=1
                count+=1
        for _ in range(100):
            B,j=rng.choice(list(zip(Bs,js)));tt=rng.getrandbits(F.Q);z=F.program(B,tt,j);w=rng.randrange(F.Q);x=z|expand(w,B)
            assert A.eval(x,o)==F.eval(x)==(tt>>w&1);gchecks+=1
        total+=len(Bs);print('b,n,probes,target tables,attempts,gates',b,F.n,len(Bs),count,attempts,len(A.g),flush=True)
    print('PASS probes',total,'programmed assignment evaluations',assign,'AIG evaluations',gchecks)
if __name__=='__main__':main()

```

---

# Prior pending research (archive; not a request to implement every item)

# Research handoff — logarithmic-probe residual-diversity barrier

**Read this section first.** New paper negative-control theorem: nearly maximal residual min-entropy on *every* sufficiently large probe, down to `ceil(log2 m)+2` bits, is compatible with an AIG of size `O(m log^5 m)=o(m^1.01)`. This closes the natural small-probe extension of the preceding large-partition negative control at the level of near-maximal cardinality/min-entropy. It does NOT exclude every possible exact residual-profile method, prove a SAT upper bound, or solve L-clb-036. No novelty claim. No native integration recommended. Repository rechecked read-only at `e73ee0f037dda1b83e84e116463515b579d17b39`; both requested notes unchanged (orientation `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`, research `677f9cbdfaf642613ef84db92161d1a78c655254`).

**Agent priority:** the same remaining Lean premises for the robust identifier SAT lower bound, not the negative-control theorem. `sat_six_lower'`, `transfer`, `word_mem_sat`, `block_restriction_lower` already exist; prove PS_d existence by finite cardinality, unit-clause helper identity, and combine with L037 for multiples of six. General additive weights and exact four-input circuit minima are unnecessary for the robust route. See previous handoff below for details. The new result has no Lean check or independent proof review.

## 1. Theorem and explicit asymptotic parameters

Use m primary inputs, free constants and complemented edges, fan-in-two AND gates. For disjoint A,B and fixed outside assignment z let R(a) be the full truth table of the B-residual for source assignment a. The maximum possible number of distinct residuals is at most 2^|A| and also at most 2^(2^|B|).

**Theorem (paper).** For all sufficiently large m, put a=ceil(log2 m), b=a+2, t=b*a+ceil(log2(b+1))+2, Q=2^b and ell=16(t+b*a+a+2). There exists a full-support Boolean function f on m inputs with an AIG of size O(m log^5 m) such that, simultaneously for every disjoint A,B and every fixed outside z, if |B|>=b, each fiber of R has at most 2^t source assignments. In particular

    log2 N(A,B,z) >= max(0, |A|-t),
    H_infinity(R(U_A)) >= max(0, |A|-t).

Here U_A is uniform on source assignments. For large m, t=O(log^2 m), ell=O(log^2 m), ell<=m, b<=m. The statement is asymptotic; these sufficient constants are not a practical size crossover. The function family is existential/nonuniform, sufficient to refute a universal proposed lower-bound principle. The finite experiment below uses different smaller parameters and does NOT certify the existence proof for arbitrary m.

### A. Shared syndrome map

Choose a binary t-by-m matrix L whose columns indexed by any b-element set are independent. Existence: choose independent fair entries; any fixed nonzero d of weight <=b satisfies Pr[Ld=0]=2^-t. There are at most (b+1)m^b such d. With the stated t, their union failure probability is <=1/4. Fix one successful L. Thus any b-probe gives a b-dimensional affine subspace of the syndrome space F2^t as the probe varies. This does not require L to be globally injective, and t<m eventually.

### B. Sparse lookup functions with simultaneous rank

For each primary index i independently define h_i(s) on F2^t as

    h_i(s) = XOR_(j=1..ell) epsilon_ij * 1[H_ij s = c_ij],

where H_ij is an independent uniformly random b-by-t binary matrix, c_ij is an independent uniform b-bit offset, and epsilon_ij is an independent fair bit. These are ordinary Boolean circuits (affine tests and AND); no truth-table oracle is needed in the eventual circuit.

Fix a probe B of size b and an arbitrary shift c in syndrome space. Let U=L(F2^B); choose the natural parametrization of c+U by the probe bits, which is bijective. Each restricted indicator is a vector v in F2^Q. The restricted linear map H_ij L_B is a uniform b-by-b matrix, since L_B has rank b and the rows of H are independent uniform linear functionals. It is invertible with probability product_(k=1..b)(1-2^-k)>=1/4 (first factor 1/2, product of the remainder >=1-sum_(k>=2)2^-k>=1/2). Conditional on invertibility the indicator v is a uniformly random unit vector of F2^Q, because c_ij is uniform and independent. Noninvertible cases need not be analyzed further.

**Subspace avoidance lemma.** Fix any W<=F2^Q of dimension d<=m. Draw ell independent indicator vectors v_j as above. For j<=ell<=m, the span of W and the previous draws has dimension <=m+ell<=2m<=Q/2. It contains at most that many distinct coordinate unit vectors (unit vectors are linearly independent). Thus, conditional on all previous draws, the probability that v_j increases the rank of their images modulo W is at least (1/4)*(1/2)=1/8. Let R_j be the rank modulo W after j draws. Then

    E[2^-R_j | v_1,...,v_(j-1)] <= (15/16) * 2^-R_(j-1).

Inductively E[2^-R_ell]<=(15/16)^ell. Given all v_j, the independent fair epsilons make XOR_j epsilon_j v_j uniform in their span, so the probability that this sum belongs to W is exactly 2^-R_ell. Consequently

    Pr[h_i restricted to c+U lies in W] <= (15/16)^ell.

This is an exact probability bound, not a claim that the lookup vectors themselves are uniform or independent across probes.

For each fixed (B,c), sequentially expose the m-b restricted functions h_i with i outside B, starting the span with the all-ones vector. Before each exposure its dimension is <=m; the previous lemma applies conditional on the already exposed functions, since h_i are independent across i. Union bound over at most m such failures, binom(m,b)<=m^b probe sets and 2^t shifts. The total failure probability is bounded by

    2^t * m^(b+1) * (15/16)^ell
    <= 2^(t+(b+1)*a) * 2^(-ell/16) <= 1/4.

Here (15/16)^ell<=exp(-ell/16)<=2^(-ell/16). Hence some single choice of all lookup functions simultaneously makes the all-ones vector and every outside-B h_i linearly independent on every affine subcube c+U. No independence between different probe sets is used. Including the all-ones vector is important for the full-support correction below.

### C. Residual fiber injection, arbitrary outside contexts

Set f_0(x)=XOR_i x_i h_i(Lx). For fixed disjoint A,B with |B|=b and fixed z, suppose source assignments u,v have the same source syndrome L_A u=L_A v. For each probe assignment w the full input syndrome is then identical for u and v, namely c+L_B w with c=L_A u+L_Z z. The difference of output values cancels every term outside A and is exactly

    f_0(u,w,z) XOR f_0(v,w,z)
      = XOR_(i in A) (u_i XOR v_i) h_i(c+L_B w).

If u!=v, the right side is nonconstant by independence modulo the all-ones vector. Hence the full residuals differ, even after adding an arbitrary fixed linear function of the primary inputs. Choose that linear correction to include x_i exactly when x_i was inessential in f_0. Adding x_i toggles its identically-zero derivative to one and does not affect derivatives in any other variable. This makes f full-support while preserving the injection. If |B|>b, choose any b-subset of B, fix the other probe bits to zero, and apply the same argument to that subcube; equality of the full residuals would imply equality on the subcube. Thus within each source-syndrome class the residual is injective, and a residual can have at most one preimage per syndrome, hence at most 2^t preimages. Both asserted information bounds follow. The number of source syndrome values may be smaller than 2^t, in which case that smaller number bounds the fiber too.

### D. Circuit budget

Compute Lx once using t parities on m bits (<=3mt ANDs). Each active lookup term needs b parities on t bits, with free complement for the affine offset, and at most b-1 ANDs for their conjunction. XOR ell terms per h_i, multiply by x_i, XOR over i, add the linear correction. A conservative raw count is

    3mt + m*ell*(3bt+b+3) + 7m = O(m log^5 m).

AIG sharing of the syndrome is essential; do not replace its parities by separate copies per lookup. All weights/coefficients are fixed circuit parameters, not extra primary inputs. The construction gives o(m^1.01) gates as m tends to infinity; no estimate of when the asymptotic inequality becomes practically useful is asserted.

## 2. Consequence and precise limitations

The previous cubic negative control needed probes of size about m/log m for near-maximal information. This one works for b=ceil(log2 m)+2 and every larger probe, with only an O(log^2 m) deficit independent of the probe size. For large source blocks this is nearly maximal even for the smallest probes capable of representing that many distinct residuals: when |A|~m, the elementary ceiling 2^|B| on log2 N forces |B|>=log2 m-O(1). Thus requiring near-maximal residual diversity/min-entropy on ALL overlapping probes down to that scale cannot itself imply L-clb-036. This does not rule out measures using exact residual identities, finer semantic structure, demanding zero deficit, or probes below the stated threshold; the present theorem does not assert any of those properties. The O(log^5 m) circuit upper bound is nonuniform and may have huge constants. The construction uses low-dimensional shared parity preprocessing, not random independent full truth tables.

The exact SAT coordinate embedding from the preceding handoff applies unchanged: one free unit sign bit per primary, fixed gate Tseitin clauses, fixed output unit. After simplifying constants (or introducing fixed unit clauses for constant wires) the encoded length N is O((m+g) log(m+g)), N>=m. Its restricted function is this small f, so g=o(N^1.01). This is a mathematical application of the earlier encoding identity, not a newly executed SAT parser experiment. It says nothing about the upper bound for full SAT_N. The classical context is Nechiporuk subfunction counting for formulas (e.g. Boppana–Sipser, *The Complexity of Finite Functions*, https://www.cs.umd.edu/~gasarch/BLOGPAPERS/boppana_sipser.pdf); no priority/novelty claim about the present construction. Do not extrapolate formula lower bounds to circuits.

**Recommendation:** stop spending substantial time on ever larger collections of scalar residual-cardinality or min-entropy tests. They can still help exclude particular topologies, but the present family is an explicit barrier to a broad universal near-saturation argument, even when paired with the older sorting and cubic controls. A subsequent research step should test the actual residual sets/Boolean functions (e.g. their affine or nonlinear common representation complexity), or seek a quantitative circuit transformation to a restricted model with a proven lower bound. There is no known successful route here to the unrestricted n^1.01 target.

## 3. Executed verification

Standalone Python 3 stdlib script `small_probe_check.py` below was executed with seed 261126. Finite verification is not the proof of the asymptotic theorem. Small tests use b=ceil(log2 m)+2, ell=48 and an explicitly constructed parity-check matrix (kernel generated by all-ones vectors of disjoint groups of >=8 variables). These parameters differ from the sufficient existence proof. Results:

| m | b | t | All probe sets checked for syndrome injectivity | Selected probe sets checked for lookup rank | Raw AIG gates |
|---:|---:|---:|---:|---:|---:|
| 8 | 5 | 7 | 56 | 56 | 9,310 |
| 10 | 6 | 9 | 210 | 210 | 16,542 |
| 16 | 6 | 14 | 8,008 | 80 | 45,634 |

- 1,600 exact distribution inequalities: enumerate every affine map on 2- and 3-bit probe spaces, count its indicator tables, and verify the subspace avoidance inequalities and the exact XOR-convolution probability bound against random small subspaces. No failure.
- All 8,274 syndrome-injectivity checks passed. 3,184 lookup-rank checks including the constant column: all cosets for every probe at m=8,10; 16 cosets for each of 80 sampled probes at m=16. All passed.
- 403 exact residual tests over 26,879 source assignments, including random disjoint source/probe pairs, larger probes, and arbitrary fixed outside contexts. 512 excess source assignments share a syndrome with another source assignment in the same test. Every residual+syndrome pair was unique, as predicted; direct fiber counts satisfied the bound. No failure. Full-support correction was unnecessary for these three seeded examples.
- 192 explicit AIG evaluations against independently tabulated lookup computation, all passed. The large gate counts are literal constructive upper bounds, not synthesis optima or small-size evidence for a practical crossover. No new native benchmarks or Lean verification.

### Reference implementation: `small_probe_check.py`

Extract and run `python small_probe_check.py`.

```python
"""Logarithmic-probe negative control, standalone stdlib finite regression.
The asymptotic result is an existence proof, not a claim about these small samples.
"""
from itertools import combinations
from collections import Counter
from random import Random
from math import comb


def bits(x):
    while x:
        b=x&-x;yield b.bit_length()-1;x^=b

def span(cols):
    s=[0]
    for v in cols:s += [v^x for x in s]
    return s

def basis(rows):
    piv={}
    for v in rows:
        while v:
            j=v.bit_length()-1
            if j in piv:v^=piv[j]
            else:piv[j]=v;break
    return piv

def rank(rows):return len(basis(rows))

def image(cols):return span(cols)

def parity(x):return x.bit_count()&1


def affine_distribution(b):
    """Enumerate all affine maps F2^b -> F2^b. Counts indicator columns."""
    Q=1<<b;D=Counter();full=0
    for packed in range(1<<(b*b)):
        rows=[(packed>>(i*b))&(Q-1) for i in range(b)]
        vals=[sum(parity(x&r)<<i for i,r in enumerate(rows)) for x in range(Q)]
        full += rank(rows)==b
        for c in range(Q):D[sum(1<<x for x,v in enumerate(vals) if v==c)]+=1
    assert sum(D.values())==Q**(b+1)
    assert full*4>=Q**b
    assert all(D[1<<i]>=full for i in range(Q))
    return D


def distribution_checks(rng):
    checks=0
    for b in (2,3):
        Q=1<<b;D=affine_distribution(b);T=sum(D.values())
        for _ in range(500):
            d=rng.randrange(Q//2+1)
            W=set(span(list(basis([rng.getrandbits(Q) for _ in range(d)]).values())))
            assert len(W)<=1<<d
            assert sum(v in W for v in [1<<j for j in range(Q)])<=d
            assert 8*sum(w for v,w in D.items() if v not in W)>=T
            checks+=1
        # Independent fair epsilon: exact XOR convolution, not simulated.
        F=Counter(D);F[0]+=T;Z=Counter({0:1})
        for L in range(1,1+Q//2):
            Z=Counter({z:sum(w*F.get(z^v,0) for v,w in Z.items()) for z in range(1<<Q)})
            assert sum(Z.values())==(2*T)**L
            for _ in range(100):
                d=rng.randrange(Q//2-L+1)
                W=span(list(basis([rng.getrandbits(Q) for _ in range(d)]).values()))
                # P[X in W] <= (15/16)^L when d+L<=Q/2.
                assert sum(Z[v] for v in W)*16**L <= (2*T)**L*15**L
                checks+=1
    return checks


def block_columns(m):
    """Parity-check kernel spanned by all-ones on disjoint groups of >=8.
    Every <=7 columns independent; deliberately noninjective globally.
    """
    groups=[m] if m<16 else [8,m-8]
    cols=[];t=0
    for g in groups:
        cs=[1<<(t+i) for i in range(g-1)]
        cols.extend(cs+[sum(cs)]);t+=g-1
    return t,cols


def parity_columns(t):
    Q=1<<t;mask=(1<<Q)-1
    return [sum(1<<x for x in range(Q) if x>>i&1) for i in range(t)],mask


def h_tables(m,t,b,L,rng):
    ps,mask=parity_columns(t);cache={0:0};tabs=[];spec=[]
    def ptab(v):
        if v not in cache:
            k=v&-v;cache[v]=ptab(v^k)^ps[k.bit_length()-1]
        return cache[v]
    for i in range(m):
        tab=0;terms=[]
        for j in range(L):
            rows=[rng.getrandbits(t) for _ in range(b)];c=rng.getrandbits(b);eps=rng.getrandbits(1)
            terms.append((rows,c,eps))
            if eps:
                v=mask
                for k,r in enumerate(rows):v&=ptab(r) if c>>k&1 else mask^ptab(r)
                tab^=v
        tabs.append(tab);spec.append(terms)
    return tabs,spec


def coset_reps(t,cs):
    """Choose a complement of span(cs); its elements give all cosets."""
    piv=basis(cs);extra=[]
    for j in range(t):
        v=1<<j
        while v:
            k=v.bit_length()-1
            if k in piv:v^=piv[k]
            else:piv[k]=v;extra.append(1<<j);break
    return span(extra)


def restrict(tab,points):return sum(((tab>>s)&1)<<j for j,s in enumerate(points))


def rank_test(m,t,cols,tabs,B,shifts):
    cs=[cols[i] for i in B];assert rank(cs)==len(B)
    pts=span(cs);outside=[i for i in range(m) if i not in B]
    full=(1<<len(pts))-1
    for c in shifts:
        pp=[x^c for x in pts]
        rr=[full]+[restrict(tabs[i],pp) for i in outside]
        assert rank(rr)==len(rr),(m,B,c)
    return len(shifts)


class AIG:
    def __init__(self,n):self.n=n;self.g=[]
    def AND(self,a,b):
        if a==0 or b==0 or a==(b^1):return 0
        if a==1:return b
        if b==1 or a==b:return a
        self.g.append((a,b));return 2*(self.n+len(self.g))
    def XOR(self,a,b):return self.AND(self.AND(a,b^1)^1,self.AND(a^1,b)^1)^1
    def fold(self,seq,op,unit):
        for v in seq:unit=op(unit,v)
        return unit
    def eval(self,x,o):
        v=[0]+[x>>i&1 for i in range(self.n)]
        def r(a):return v[a//2]^(a&1)
        for a,b in self.g:v.append(r(a)&r(b))
        return r(o)

def make_aig(m,t,cols,spec,lin):
    a=AIG(m);p=[2*(i+1) for i in range(m)]
    sx=[a.fold((p[i] for i in range(m) if cols[i]>>j&1),a.XOR,0) for j in range(t)]
    terms=[]
    for i,H in enumerate(spec):
        hh=[]
        for rows,c,eps in H:
            if not eps:continue
            v=[a.fold((sx[j] for j in bits(r)),a.XOR,0)^(1^(c>>k&1)) for k,r in enumerate(rows)]
            hh.append(a.fold(v,a.AND,1))
        terms.append(a.AND(p[i],a.fold(hh,a.XOR,0)))
        if lin>>i&1:terms.append(p[i])
    return a,a.fold(terms,a.XOR,0)


def full_truth(m,t,cols,tabs):
    Q=1<<t
    tb=[v.to_bytes((Q+7)//8,'little') for v in tabs]
    masks=[sum(((v[s//8]>>(s%8))&1)<<i for i,v in enumerate(tb)) for s in range(Q)]
    syn=image(cols);truth=[parity(x&masks[s]) for x,s in enumerate(syn)]
    # Add a linear term only for inessential variables. Does not change the
    # column independence modulo the constant function.
    lin=0
    for i in range(m):
        d=1<<i
        if all(truth[x]==truth[x^d] for x in range(1<<m)):
            lin|=d;truth=[v^(x>>i&1) for x,v in enumerate(truth)]
    assert all(any(truth[x]!=truth[x^(1<<i)] for x in range(1<<m)) for i in range(m))
    return syn,truth,lin


def residual_test(m,syn,truth,A,B,z):
    aa=image([1<<i for i in A]);bb=image([1<<i for i in B]);fibers={};joint=set()
    for a in aa:
        v=sum(truth[a|b|z]<<j for j,b in enumerate(bb))
        assert (syn[a],v) not in joint
        joint.add((syn[a],v));fibers[v]=fibers.get(v,0)+1
    assert max(fibers.values())<=len(set(syn[a] for a in aa))
    return len(aa),len(fibers),len(aa)-len(set(syn[a] for a in aa))


def main():
    rng=Random(261126);D=distribution_checks(rng);print('PASS distribution inequalities',D,flush=True)
    ranks=checks=fiber_rows=collisions=evals=0
    for m in (8,10,16):
        b=(m-1).bit_length()+2;t,cols=block_columns(m);assert b<=7
        Bs=list(combinations(range(m),b));assert all(rank([cols[i] for i in B])==b for B in Bs)
        L=48;tabs,spec=h_tables(m,t,b,L,rng)
        # Small graphs: every probe and every syndrome coset. Larger graph:
        # all B satisfy syndrome injectivity; sample affine restrictions of h.
        selected=Bs if m<=10 else rng.sample(Bs,80)
        for B in selected:
            ss=coset_reps(t,[cols[i] for i in B]);assert len(ss)==1<<(t-b)
            if m>10:ss=rng.sample(ss,16)
            ranks+=rank_test(m,t,cols,tabs,B,ss)
        syn,truth,lin=full_truth(m,t,cols,tabs);a,o=make_aig(m,t,cols,spec,lin)
        for x in rng.sample(range(1<<m),min(64,1<<m)):
            assert a.eval(x,o)==truth[x];evals+=1
        # Real source assignments, not just rank certificates. Include larger
        # probe sets and random outside contexts; for m16 ensure collisions
        # in the syndrome really occur by leaving a whole parity group outside B.
        samples=selected if m<=10 else rng.sample(selected,16)+[(0,1,2,3,4,5)]
        for B in samples:
            A=[i for i in range(m) if i not in B];q,N,c=residual_test(m,syn,truth,A,B,0)
            checks+=1;fiber_rows+=q;collisions+=c
            assert N>=q//(1<<t)
        for _ in range(40):
            p=rng.sample(range(m),m);nb=rng.randrange(b,min(m,b+2)+1);na=rng.randrange(m-nb+1)
            B=p[:nb];A=p[nb:nb+na];z=sum(1<<i for i in p[nb+na:] if rng.getrandbits(1))
            q,N,c=residual_test(m,syn,truth,A,B,z);checks+=1;fiber_rows+=q;collisions+=c
        print('PASS m',m,'b',b,'t',t,'syndrome-injective probe sets',len(Bs),'selected rank probes',len(selected),'gates',len(a.g),'linear corrections',lin.bit_count(),flush=True)
    print('PASS rank certificates',ranks,'residual tests',checks,'source rows',fiber_rows,'same-syndrome excess rows',collisions,'AIG evaluations',evals,flush=True)

if __name__=='__main__':main()

```

---

# Research handoff — simultaneous residual-diversity barrier

**Read this section first.** New negative-control theorem: an AIG of size `o(m^1.01)` can have nearly maximal residual information simultaneously across *every* ordered disjoint source/probe pair with a sufficiently large probe. This is a paper counting proof with finite regression tests, not a new SAT lower bound or a claim of novelty. It identifies a concrete limitation of the previous multi-partition strategy. No native integration recommended. Repository rechecked read-only at `e73ee0f037dda1b83e84e116463515b579d17b39`; both requested notes unchanged. No new Lean proof or repository changes this round.

**Agent priority remains the actual SAT theorem.** `SatBridge/SixQ.lean` already proves `sat_six_lower'` (external counted gates >= 8Q-3 at length 6Q, Q>=2). `transfer`, `word_mem_sat`, and `block_restriction_lower` are also complete per the repository. Finish the PS_d existence and helper-unit identity, combine with L037 on multiples of six, then prove the finite arithmetic/asymptotic statements. The general additive-weight theorem is not needed for the robust route. For PS_d existence, a fixed d-cube, pair of free variables i,j, and fixed value of i gives a bad table when the two j-cofactors coincide. There are `2^(2^r - 2^(d-2))` such r-input tables: each of `2^(d-2)` disjoint pairs must agree. Union bound over the `binom(r,d) * 2^(r-d) * 4*binom(d,2)` choices of cube, pair, direction and fixed value. If this multiplier is smaller than `2^(2^(d-2))`, some table is PS_d. This is a finite-cardinality argument (no probability library or exact-synthesis oracle required). Use the reviewed `n + q*(2r-3d+3)` bound, not the historical `-1` version. The first tested *power of two* beating 17n/12 was 2^32, not a claim that no smaller even length works. Earlier optional interface results are archived below, not a request to implement all of them.

## 1. An all-partitions negative control for residual counting

All gates are free-phase AIG ANDs. Let m be the number of free source bits. For disjoint subsets A,B of [m] and fixed assignment z to the remaining variables, let N(A,B,z) be the number of distinct B-residual truth tables of f as the assignment to A varies. It is always at most 2^|A|. Even if both directions of every partition have close to this maximum, the function need not be hard for unrestricted circuits.

**Theorem (paper).** Let t be an integer with 2<=t<=m, `q0=binom(t,2)>m`, and `p=4m/[t(q0-m)]<=1/2`. There exists a full-support cubic Boolean polynomial f over F2, with at most `2p*binom(m,3)` cubic monomials and an AIG with at most `3m+10p*binom(m,3)-3` gates, such that for *all* disjoint A,B and all z, whenever |B|>=t,

    log2 N(A,B,z) >= max(0, |A|-t).

In fact every residual fiber has size at most 2^t. Thus for uniformly random A the residual has min-entropy at least |A|-t, not just high support cardinality. Both directions hold on every bipartition with both parts >=t; no chosen partition or choice of fixed context is needed.

**Construction.** Independently include every unordered triple in E with probability p. Set

    f(x) = XOR_i x_i XOR XOR_{ {i,j,k} in E } (x_i x_j x_k).

The linear terms make all inputs essential by uniqueness of Boolean ANF: the derivative in x_i has constant coefficient 1 and cannot be identically zero. A direct AIG computes each cubic monomial with two ANDs and XORs all m+|E| terms using three ANDs per XOR. Gate count is exactly `3m+5|E|-3` for this raw construction (not an optimality claim).

Fix disjoint A,B, put a=|A| and q=binom(|B|,2). Define the a-by-q matrix M over F2, row i in A, column {j,k} in B, entry 1 iff {i,j,k} is in E. All its entries are independent Bernoulli(p): the three indices identify a unique triple, because A and B are disjoint. After fixing A to u and the outside to z, the degree-two ANF coefficient vector of the B-residual is `u^T M + c_z`. Triples entirely inside B give fixed degree-three coefficients, and triples with at least two indices outside B give degree at most one in B. Therefore equal residual functions imply equal images under M. Rank R implies at least 2^R residuals and each fiber has size at most 2^(a-R).

**Rank lemma.** A random vector of q independent Bernoulli(p) bits belongs to any fixed subspace of dimension <=s with probability <=(1-p)^(q-s) for p<=1/2. Choose at most s pivot coordinates whose projection is injective on that subspace. Condition on their values. Membership fixes every other coordinate; by independence each has conditional success probability at most 1-p. This holds even if the candidate subspace is itself determined by other independent rows.

If a>=t and rank M<=a-t, some set R of exactly a-t rows spans all rows (pad an independent basis if necessary). Conditional on these rows, each of the remaining t independent rows must lie in their span. For any fixed A,B,R,

    Pr[all remaining rows lie in span(R)]
      <= (1-p)^(t(q-a+t))
      <= exp(-p*t*(q0-m)) = exp(-4m).

There are at most 4^m possible choices of disjoint A,B and R subset A: each index is in R, A\\R, B, or neither. Union bound gives probability of any rank failure <=4^m exp(-4m)<1/2. For a<t no rank requirement is needed. Separately, E has expected size p*binom(m,3), so Markov gives probability <=1/2 of exceeding twice that size. The sum of bad probabilities is strictly below 1. Hence one E satisfies both the uniform rank property and the gate budget. For |A|>=t, we have rank > a-t, and the slightly weaker stated inequality follows. This proof uses no independence across different partitions. In particular, one graph is chosen once and works for all of them.

### Quantitative consequences

- For any fixed epsilon>0 (epsilon<1/2), take t=ceil(epsilon*m). Then p=O_epsilon(1/m^2), and the gate count is O_epsilon(m). Every probe of size >=epsilon*m has residual log-count >=|A|-epsilon*m-O(1), simultaneously for every source set and context. The constant in the linear upper bound grows as epsilon decreases.
- Take t=ceil(m/log2 m). Then p=O(log^3 m/m^2), yielding O(m log^3 m) AIG size = o(m^1.01). Every probe at least m/log2 m in size nearly saturates the full residual information |A|, with deficit at most t. This is a family of circuits, not a uniform efficient deterministic construction. The existential counting proof is enough for a counterexample to a universal lower-bound principle.
- One can even take t=ceil(m^(1-delta)) for any fixed 0<delta<1/300. Then gate count O(m^(1+3delta))=o(m^1.01) and the deficit is polynomially sublinear, for all sufficiently large m. E.g. delta=1/400 gives exponent 1.0075. These are asymptotic bounds; the sufficient p can be too large at small m. Do not infer a practical crossover from this argument.

This rules out a proof principle of the form "near-saturation of residual diversity (or residual min-entropy) in both directions of all sufficiently large partitions forces an unrestricted n^1.01 lower bound." It does not rule out every measure involving exact residual sets, their semantic compatibility, tiny probes, or additional constraints. No claim that these polynomials match the complete SAT residual profile.

## 2. Exact coordinate embedding in pequalnp SAT

The negative control is not just an abstract Boolean function. It embeds into the same `encodeCNF` grammar. Use a fixed AIG for f as above with m primary wires, g AND nodes and free complemented edges. Give all wires distinct positive natural-number identifiers 1..m+g. Encode one unit clause per primary, with its polarity the corresponding free input bit. The identifier and all other tokens are fixed. For each AND `v = l AND r` put the fixed three clauses `(NOT v OR l)`, `(NOT v OR r)`, `(v OR NOT l OR NOT r)`, using the appropriate signed operand literals. Add a fixed unit clause asserting the output literal true. For every setting of the m free sign bits, the constraints have a unique gate-consistent extension of the primary assignment; it satisfies the last unit iff f=1. Thus the encoding is a genuine coordinate restriction (not a general reduction computing new input bits). All m free bits are essential.

There are m+3g+1 clauses, each of bounded width, and all variable identifiers use O(log(m+g)) digits. The token pairing yields total length N=O((m+g)log(m+g)) and N>=m. The restricted SAT function has the same small AIG with g=O(m log^3 m)=o(N^1.01), or the polynomial-deficit variant above. High residual diversity survives *inside* an interacting non-unit-clause SAT restriction. This is NOT an upper bound on full SAT_N; the full SAT predicate can be harder. The construction is a standard Tseitin encoding specialized to the exact token grammar. It supplies a second negative control, complementing the previously reviewed list-disjointness sorting construction. The list-disjointness example addresses many small identifier blocks, while this one addresses all sufficiently large probes and arbitrary contexts.

## 3. What the new theorem leaves open

A fixed degree-3 Boolean polynomial has an elementary ceiling on this information measure for small probes. After fixing all outside inputs, the degree-three coefficients on B never change. Only the constant, linear and quadratic coefficients can vary, so

    log2 N(A,B,z) <= min(|A|, 1+|B|+binom(|B|,2)).

For logarithmic-size B this is O(log^2 m), far below m. The new negative control does not address simultaneous near-maximal residual diversity on such small probes. List-disjointness already shows that high diversity on one particular small-block partition can coexist with quasi-linear circuits. To justify any stronger multi-partition method, test it on both families and prove it handles overlapping small probes, not merely count how many large bipartitions have high rank. The exact small-probe question is open here; no claim that high diversity on all small probes implies superlinear complexity.

A separate literature route worth investigating is Golovnev, Kulikov and Williams, *Circuit Depth Reductions* (https://doi.org/10.4230/LIPIcs.ITCS.2021.24), which gives an unrestricted-depth reduction to a disjunction of bounded-width CNFs with an exponential dependence on gate count. Their reduction suggests stronger **linear** bounds; the existing exponential dependence is insufficient for L-clb-036 at s=N^1.01, since a DNF of at most 2^N terms is always possible. The Valiant-style superlinear consequences require logarithmic depth or other restrictions; do not assume small unrestricted circuits are shallow. Also see Golovnev et al., *On the Limits of Gate Elimination* (https://doi.org/10.4230/LIPIcs.MFCS.2016.46). No new depth reduction is proved here. The next exploratory task should target a real semantic restriction on arbitrary small circuits, or a quantitative reduction to another model; avoid more isolated inner-product encoder refinements unless they directly transfer to whole circuits.

## 4. Executed verification

The standalone stdlib script below ran successfully. On six seeded cubic hypergraphs (m=3..8) it checked all ordered disjoint source/probe pairs (9,828 cases) with a seeded outside assignment per pair. It evaluates the entire residual table for every source setting, independently extracts its degree-two coefficients by Boolean second differences, and compares the exact image with the affine translate of the matrix image. All passed. For all 504 input assignments across those graphs, it simulated the actual AIG, encoded the CNF, verified exactly which sign-bit positions vary, and checked satisfiability using an independent parser and unit-propagation DPLL. Another 256 sampled AIG evaluations on larger graphs passed. All counts refer to these local runs, not exact optimal synthesis results.

Illustrative larger sample: 12m distinct random triples, with 128 independently sampled cuts at each probe size m/4, m/2, 3m/4 (1,536 sampled rank evaluations total). These are fixed-edge-count examples, not the Bernoulli existence construction and not exhaustive all-cut verification.

| m | Constructed AIG gates | Average rank deficit at probe m/4 | At m/2 | At 3m/4 |
|---:|---:|---:|---:|---:|
| 32 | 2,013 | 3.633 | 0 | 0 |
| 64 | 4,029 | 5.719 | 0 | 0 |
| 128 | 8,061 | 10.898 | 0.016 | 0 |
| 256 | 16,125 | 20.344 | 0.008 | 0 |

In all but three of the 512 sampled balanced cuts the quadratic coefficient matrix was full row rank; in the remaining three its deficit was one. In particular the actual residual count is exactly maximal on those full-rank cuts. The samples demonstrate the effect, not the proof of uniformity across all cuts at large m. They are not evidence of an optimal gate count. No independent Lean verification of the new counting theorem.

### Reference implementation: `multipartition_check.py`

Extract the following code to a standalone file and run `python multipartition_check.py`.

```python
"""Sparse cubic residual diversity: standalone stdlib regression checks."""
from itertools import combinations, product
from random import Random
from math import comb, ceil, log2


def bits(mask):
    while mask:
        b=mask&-mask; yield b.bit_length()-1;mask^=b

def submasks(mask):
    s=mask
    while True:
        yield s
        if not s:break
        s=(s-1)&mask

def rank(rows):
    base={}
    for x in rows:
        while x:
            k=x.bit_length()-1
            if k in base:x^=base[k]
            else:base[k]=x;break
    return len(base)

def cross(n,edges,A,B):
    """Source by unordered pair-of-probe matrix."""
    cols={p:j for j,p in enumerate(combinations(bits(B),2))}
    rows={i:0 for i in bits(A)}
    for e in edges:
        a=[i for i in e if A>>i&1];b=tuple(i for i in e if B>>i&1)
        if len(a)==1 and len(b)==2:rows[a[0]]^=1<<cols[b]
    return list(rows.values())

def value(edges,x):
    return (x.bit_count()+sum(all(x>>i&1 for i in e) for e in edges))&1

def coeff(row,B):
    # Boolean second differences at all-zero probe assignment.
    return sum((row[0]^row[1<<i]^row[1<<j]^row[(1<<i)|(1<<j)])<<k
               for k,(i,j) in enumerate(combinations(bits(B),2)))

def profiles(n,edges,A,B,z,truth):
    R=cross(n,edges,A,B); d=rank(R); pred=set(); observed=set(); tables=set()
    for a in submasks(A):
        q=0
        for i,r in zip(bits(A),R):
            if a>>i&1:q^=r
        pred.add(q)
        tab={b:truth[a|b|z] for b in submasks(B)}
        observed.add(coeff(tab,B));tables.add(tuple(tab.values()))
    # Fixed outside variables can contribute a constant shift to the coefficient vector.
    assert observed=={v^coeff({b:truth[b|z] for b in submasks(B)},B) for v in pred}
    assert len(pred)==1<<d and len(tables)>=1<<d
    return len(tables),d

def sample_edges(n,k,rng):
    if k>=comb(n,3)//3:
        return sorted(rng.sample(list(combinations(range(n),3)),k))
    E=set()
    while len(E)<k:E.add(tuple(sorted(rng.sample(range(n),3))))
    return sorted(E)

# AIG with free phase and constants. Nodes 1..n are primaries.
class AIG:
    def __init__(self,n):self.n=n;self.g=[]
    def AND(self,a,b):self.g.append((a,b));return 2*(self.n+len(self.g))
    def XOR(self,a,b):return self.AND(self.AND(a,b^1)^1,self.AND(a^1,b)^1)^1
    def evaluate(self,x,o):
        v=[0]+[x>>i&1 for i in range(self.n)]
        def get(a):return v[a//2]^(a&1)
        for a,b in self.g:v.append(get(a)&get(b))
        return get(o)

def make_aig(n,E):
    a=AIG(n);p=[2*(i+1) for i in range(n)]
    terms=p+[a.AND(a.AND(p[i],p[j]),p[k]) for i,j,k in E]
    out=terms[0]
    for w in terms[1:]:out=a.XOR(out,w)
    assert len(a.g)==3*n+5*len(E)-3
    return a,out

# Source sign bits are the only free coordinates; AIG gate clauses are fixed.
def lit(v,s):return '1'+str(int(s))+''.join('1'+b for b in bin(v)[2:][::-1] if v)+'01'
def clause(C):return ''.join(lit(v,s) for v,s in C)+'00'
def encode(a,out,x):
    C=[((i+1,x>>i&1),) for i in range(a.n)]
    for v,(p,q) in enumerate(a.g,a.n+1):
        # Signed operands. z iff (p and q).
        L=(p//2,1^(p&1));R=(q//2,1^(q&1))
        C.extend([((v,0),L),((v,0),R),((v,1),(L[0],1^L[1]),(R[0],1^R[1]))])
    C.append(((out//2,1^(out&1)),))
    return ''.join(clause(c) for c in C)

def parse(s):
    assert len(s)%2==0
    toks=[s[i:i+2] for i in range(0,len(s),2)];i=0;C=[];c=[]
    while i<len(toks):
        h=toks[i];i+=1
        if h=='00':C.append(c);c=[];continue
        assert h in ('10','11');d=[]
        while i<len(toks) and toks[i] in ('10','11'):
            d.append(int(toks[i][1]));i+=1
        assert i<len(toks) and toks[i]=='01' and (not d or d[-1]);i+=1
        c.append((sum(b<<j for j,b in enumerate(d)),int(h[1])))
    assert not c
    return C

def sat(C):
    # Independent generic DPLL with unit propagation (all sources fixed here).
    while C:
        if any(not c for c in C):return False
        c=min(C,key=len)
        if len(c)>1:
            v,b=c[0];return sat(C+[[(v,b)]]) or sat(C+[[(v,1^b)]])
        v,b=c[0];C=[[(u,s) for u,s in c if u!=v] for c in C if (v,b) not in c]
    return True

def main():
    rng=Random(261126);checks=enc=aig=0
    # All ordered disjoint source/probe pairs for six small graphs, and arbitrary contexts.
    for n in range(3,9):
        E=sample_edges(n,max(1,comb(n,3)//3),rng);truth=[value(E,x) for x in range(1<<n)]
        U=(1<<n)-1
        for A in submasks(U):
            for B in submasks(U^A):
                z=rng.getrandbits(n)&~(A|B);profiles(n,E,A,B,z,truth);checks+=1
        a,o=make_aig(n,E);base=encode(a,o,0)
        offsets=[];j=0
        for i in range(n):offsets.append(j+1);j+=len(clause(((i+1,0),)))
        for x in range(1<<n):
            assert a.evaluate(x,o)==truth[x];aig+=1
            w=encode(a,o,x);assert len(w)==len(base)
            assert {j for j,(b,c) in enumerate(zip(w,base)) if b!=c}=={offsets[i] for i in bits(x)}
            assert sat(parse(w))==bool(truth[x]);enc+=1
    print('PASS exact residual coefficient checks',checks,'AIG',aig,'SAT coordinate encodings',enc,flush=True)
    # Illustrative sampled cuts on larger sparse graphs, NOT a verification of all cuts.
    for n in (32,64,128,256):
        E=sample_edges(n,min(12*n,comb(n,3)),rng);a,o=make_aig(n,E)
        for _ in range(64):
            x=rng.getrandbits(n);assert a.evaluate(x,o)==value(E,x);aig+=1
        for b in (n//4,n//2,3*n//4):
            ds=[];N=128
            for _ in range(N):
                B=sum(1<<i for i in rng.sample(range(n),b));A=((1<<n)-1)^B
                ds.append(n-b-rank(cross(n,E,A,B)))
            print('sample n',n,'edges',len(E),'gates',len(a.g),'probe',b,'source',n-b,'cuts',N,'deficit min/mean/max',min(ds),round(sum(ds)/N,3),max(ds),flush=True)
    print('PASS total AIG',aig,flush=True)

if __name__=='__main__':main()

```

---

# Previous pending research (archive; no request to implement optional filters)

# Research handoff — sharp affine/nonlinear redundancy thresholds

**Agent priority:** finish the robust-identifier SAT theorem in Lean. The actual external SAT theorem `sat_six_lower'` (size >= 8Q-3 at n=6Q, Q>=2), model translation, six-bit identity, and robust block-product gate elimination are already checked per repository. Remaining tasks: PS_d existence by finite cardinality, helper-unit identity, length arithmetic and the robust theorem (first on multiples of six). This new section is an interface-specific mathematical result, not a new SAT bound. Repository rechecked read-only after experiments at `e73ee0f037dda1b83e84e116463515b579d17b39`; orientation note blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2` and research note blob `677f9cbdfaf642613ef84db92161d1a78c655254` unchanged. No repo changes or Lean proof this round. No priority/novelty claim. Do not implement optional native filters without a demonstrated benefit.

## 1. Affine codes with one redundant entry: an all-dimension theorem

Model: E=m+r entry ANDs `h_i=p_i(x) q_i(y)`, followed by any Boolean decoder, with separate pure-side preprocessing free. All actual AND operands p_i,q_i are nonconstant. No late pure-side injection. Let F(x,y) be an affine-bilinear polynomial (a bilinear form plus linear terms and constant), over F2. For IP_m the two port codes must be injective, since every row and column of IP is distinct. For the more general theorem assume both affine port maps have full input rank m.

**Theorem (paper reduction + exhaustive finite certificate):** at r=0 or r=1, if such a target F is constant on the fibers of h, then F has an affine-XOR reconstruction from h (constant plus XOR of a subset of entry bits). This is false at r=2, even for full-rank IP_2 and with all entry operands nonconstant.

For r=0 both codewords range over a full cube. Fix q to all ones, vary p, and use the fact F in p is affine and h=p. This determines the decoder on its entire domain. For r=1 write n=E=m+1. The affine images P,Q are hyperplanes `a dot p=alpha`, `b dot q=beta` with nonzero masks a,b. Each mask must have weight at least two, because a singleton relation would fix a port to a constant. F as a function on P×Q remains affine-bilinear under arbitrary independent changes of affine coordinates. The product map is h=p&q (coordinatewise AND).

### Finite obstruction lemma: seven ports suffice

Select pivots i∈supp(a), j∈supp(b). If their supports intersect, use the same pivot in the intersection (i=j); otherwise use distinct pivots. Eliminate p_i,q_j by the two affine equations. Every other coordinate is a free variable on the corresponding side. In those coordinates F has a unique coefficient vector consisting of all bilinear, linear and constant coefficients. The entry h_l for l outside {i,j} is exactly p_l q_l. Only pivot entries may contain off-diagonal or linear coefficients. An affine-XOR representation is an ordinary linear system on the coefficients of `F=c+sum_l lambda_l h_l`.

Eliminate each nonpivot lambda_l using the coefficient of p_l q_l; eliminate c using the constant coefficient. All remaining equations constrain only the pivot lambdas. If i=j there is one unknown, so inconsistency has a witness of at most two coefficient equations: a false constant equation or two opposite requirements. Each such equation mentions at most two free port indices. Let J contain the pivot and the mentioned indices, and add at most one other coordinate from each parity mask to ensure the two restricted masks still have weight >=2. Then |J|<=1+4+2=7.

If supports are disjoint, the two pivot polynomials are `h_i=(alpha+sum_{k in a-i} p_k) q_i` and `h_j=p_j (beta+sum_{k in b-j}q_k)`. Their nonzero coefficient supports are disjoint: their bilinear terms have first indices in a-i versus first index j, and their linear terms are on different sides. Hence each remaining coefficient equation involves at most one of the two unknown pivot coefficients. Inconsistency again has a witness of at most two equations, and if two equations conflict on a pivot each mentions at most one index outside the two pivots. A false constant equation mentions at most two free indices. Include both pivots, the at most two other indices, and at most two extra support witnesses; |J|<=6.

Now fix every free p and q coordinate outside J to zero. Both pivots are in J, so both smaller port codes are affine hyperplanes with the original offsets and masks restricted to J. Every h outside J is zero. The remaining coefficients of F and the pivot entries are precisely their original coefficients on J, not approximations. The conflicting equations survive, so the restricted F cannot have affine-XOR reconstruction. But Boolean decodability is inherited by restriction, since the original decoder can be evaluated with all deleted h coordinates zero. Thus **any counterexample would have a counterexample on at most seven ports, with all entry operands nonconstant**. The argument concerns all affine-bilinear targets; it does not require the restricted bilinear form to have full rank. Do not test only IP targets in the finite check.

### Exhaustive finite certificate

For n=2..7, simultaneous coordinate permutation classifies two parity masks by the sizes of a∩b, a\b, b\a (the unused size follows). Enumerate a representative of every class and all four offsets. Pick a pivot independently on each side for the following dimension calculation. Augment each vector of n-1 free coordinates by constant 1; call the resulting vectors u,v. All affine-bilinear functions are `T dot (u v^T)`, a space of dimension n^2. For every attained h, pick one reference tensor; form differences with the other tensors at that h. Their span K is exactly the space whose orthogonal complement gives the decodable affine-bilinear functions. Thus decodable dimension is n^2-dim K. Affine-XOR functions of h are a subspace of that space of dimension equal to the rank of `(h,1)` over attained h. If the dimensions are equal the spaces coincide. This is exact linear algebra over F2, not a heuristic sampling or solver assertion.

| E (ports) | Nonconstant cases | Dimension mismatches |
|---:|---:|---:|
| 2 | 4 | 0 |
| 3 | 20 | 0 |
| 4 | 56 | 0 |
| 5 | 116 | 0 |
| 6 | 204 | 0 |
| 7 | 324 | 0 |
| Total | 724 | 0 |

The checker also examines 336 degenerate cases with singleton masks. At each E exactly one symmetry/offset class has a dimension gap of one: a,b distinct singleton supports, both parity offsets 1. This supplies raw source and query signals disguised as entry products, and is excluded by the nonconstant assumption. The local-obstruction implementation separately compared to explicit full coefficient-span membership on 1,818 seeded cases of dimension up to 30: 903 representable and 915 not representable, all correct; extracted restrictions (max five observed ports, theoretical cap seven) were independently checked against the smaller coefficient span. The all-dimension theorem depends on the paper reduction and the finite certificate, not these random cases. Not Lean-checked.

## 2. Gate cost and sharp affine threshold

For IP_m, an affine-XOR reconstruction has bilinear coefficient matrix of rank m, so among the selected entry indices choose a set S of m linearly independent source forms. At r=1 the query code is an affine hyperplane with parity mask of weight >=2. Since only one coordinate is outside S, some parity-mask position lies in S. Take the word supported on S with all S coordinates one, and if necessary flip one in S to meet the affine constraint. It has at least m-1 active coordinates, all selected in the affine-XOR reconstruction. Fix query y to that word. The source forms at these active ports are independent affine bits. All E entry gates disappear, and on the active cube the decoder computes parity up to a fixed phase. The standard free-phase AIG parity minimum is 3(k-1) for k>=1 (see earlier handoff). Hence for m>=2

    G >= E + 3(m-2) = 4m-5.

This counts only mixed gates, with separate affine preprocessing free, arbitrary decoder reconvergence and no late injection. It is a lower bound, not a claimed exact minimum at r=1. Take max with the previous unconditional 2m+1 mixed bound for IP_m. At r=0 the same parity argument gives the exact 4m-3.

**Sharpness at r=2** (new): let source bits u,v and query bits s,t. Take four entry gates

    h0=u*(1+s), h1=(u+v)*t, h2=(1+u+v)*t, h3=u*s.

All eight operands are nonconstant affine forms. Both codes have rank two. Then

    u*s + v*t = h3 + h1 + (h0+h3)*(h1+h2).

No affine-XOR reconstruction exists: in any affine-XOR combination the coefficients of u*t and v*t coincide, while in the target they differ. Direct truth-table replay confirms nine attained words and feasibility. Add independent identity products to obtain counterexamples for every m>=2 at the same r=2. Any affine-XOR reconstruction of the extension would restrict to one for the two-pair example. At least m+2 distinct entry signals must be used by any decoder on an affine nonlinear-only interface (else the r<=1 theorem, or the rank-m condition, contradicts it). The live output cone then requires >=m+1 decoder gates, hence G>=2m+3. In the explicit four-entry example G>=7>5 for the standard IP_2 construction. No exact affine counterexample decoder cost claimed.

## 3. Arbitrary nonlinear codes: the threshold is one

At r=0 for arbitrary bijective code maps, the previous bilateral saturation theorem proves exact 4m-3 for IP. This also forces affine-linear encodings up to the saturated entry-coordinate phases in the normalized model; see the proof in the bilateral handoff. At r=1 arbitrary nonlinear codes already break affine-XOR reconstruction. A two-pair witness with three entries is

    P=[0,1,3,7], Q=[0,7,6,5]     (x,y in binary order 0,1,2,3)
    h = P[x] & Q[y]
    target = parity(x & y).

Every port is nonconstant. The care table at h=0..7 is `[0,1,1,0,*,0,1,1]`. A constant-plus-XOR decoder would require constant 0 and weights at bits 0 and 1 both one (h=0,1,2), then bit 2 weight one (h=5); this would give zero at h=6, a contradiction. Padding by independent identity products again gives nonlinear-only examples for all m>=2 and the same redundancy. This is a feasibility separation, not a circuit saving.

**Exhaustive gate-cost check:** all injective 2-bit-to-3-bit maps with no constant coordinates (1536 maps per side) were enumerated in C++ and paired. Compute the actual decoder care table by testing all 16 input pairs; reject collisions of opposite labels. For each feasible care table test all 16 affine-XOR decoders. Then calculate exact 3-input AIG minima by enumerating complement-normalized gate-column sets breadth first. Constants and input literals free. In a minimum circuit no gate needs to duplicate a column up to complement, and equivalent column sets have identical possible extensions. This enumerates all 256 full truth tables through cost 6 (counts by cumulative budget 0..6: 8,32,96,126,230,238,256). Minimum over completions of each care table is exact in this standalone decoder model.

| Result | Count |
|---|---:|
| Code pairs | 2,359,296 |
| Feasible | 5,598 |
| Nonlinear-only | 1,536 |
| Nonlinear-only and both affine | 0 |
| Distinct feasible care/label tables | 157 |
| Distinct nonlinear-only tables | 64 |

Exact standalone decoder cost distribution among all feasible pairs: cost 2:90, cost 3:3438, cost 4:1932, cost 6:138. **All 1,536 nonlinear-only pairs have decoder minimum 4**, so their entry-only mixed cost is exactly 3+4=7, versus 5 for the standard two-pair circuit. Pure-side code generation is free; these are not full circuit costs. This enumeration does not prove any cost lower bound of seven for all larger IP encoders or for arbitrary topologies. The one-bit-redundancy nonlinear counterexamples show why the affine rigidity argument cannot be used without an encoding hypothesis.

## 4. Recommendation

We now know the first redundancy allowing nonlinear-only reconstruction for the three code models (homogeneous r=4 for m>=3; affine r=2 for m>=2; arbitrary r=1 for m>=2), with exact small decoder costs. Further threshold work on these interfaces is unlikely by itself to establish L-clb-036: even tight mixed-IP costs are linear and conditional on an entry architecture. Prioritize the independent robust SAT Lean track; for exploratory superlinear research, move to new multi-partition accounting methods or new hard SAT restrictions that cannot be handled by short local interfaces. No claim of a superlinear bound, or of an improvement to the current proposed 2n-o(n) SAT coefficient. The previous pending work follows for reference.

## 5. Reproduction

Extract `affine_certificate.py` and run it with Python 3 (stdlib only). Extract `nonlinear.cpp`, compile with `g++ -O3 -std=c++17 nonlinear.cpp -o nonlinear`, run `./nonlinear > nonlinear.log` and extract/run `cost.py` in the same directory. All three ran successfully locally. No native Percy verdicts, third-party Python modules, or unsupported external dependencies used.

### `affine_certificate.py`

```python
"""Finite affine-hyperplane certificate and independent local obstruction audit."""
from itertools import product
from random import Random

def basis(vs):
    b={}
    for v in vs:
        while v:
            i=v.bit_length()-1
            if i in b:v^=b[i]
            else:b[i]=v;break
    return b

def member(x,b):
    for i,v in sorted(b.items(),reverse=True):
        if x>>i&1:x^=v
    return x==0

def case(n,a,b,ap,bp):
    P=[p for p in range(1<<n) if (p&a).bit_count()%2==ap]
    Q=[q for q in range(1<<n) if (q&b).bit_count()%2==bp]
    ai=a&-a;bi=b&-b
    def comp(p,bit):return (p&(bit-1))|((p>>1)&~(bit-1))|(1<<(n-1))
    def outer(p,q):return sum(q<<(n*i) for i in range(n) if p>>i&1)
    seen={};K=[]
    for p in P:
        for q in Q:
            z=outer(comp(p,ai),comp(q,bi));h=p&q
            if h in seen:K.append(z^seen[h])
            else:seen[h]=z
    dim=n*n-len(basis(K));lr=len(basis(h|1<<n for h in seen))
    return dim,lr

def finite():
    counts=[];deg=[]
    for n in range(2,8):
        seen=set();count=0;bad=0;total=0
        for a in range(1,1<<n):
            for b in range(1,1<<n):
                t=((a&b).bit_count(),(a&~b).bit_count(),(b&~a).bit_count())
                if t in seen:continue
                seen.add(t)
                for ap,bp in product(range(2),repeat=2):
                    dim,lr=case(n,a,b,ap,bp);total+=1
                    if a.bit_count()>=2 and b.bit_count()>=2:
                        assert dim==lr;count+=1
                    if dim!=lr:
                        assert t==(0,1,1) and ap==bp==1 and dim==lr+1;bad+=1
        counts.append(count);deg.append(total-count)
        assert bad==1
    assert counts==[4,20,56,116,204,324]
    print('finite nonconstant cases',counts,sum(counts),'degenerate cases',sum(deg))

def forms(n,a,b,ap,bp,p,q):
    P=[i for i in range(n) if i!=p]+[n];Q=[i for i in range(n) if i!=q]+[n]
    D={ (i,j):k for k,(i,j) in enumerate(product(P,Q)) }
    h=[]
    for i in range(n):
        A=([j for j in P[:-1] if a>>j&1]+([n] if ap else [])) if i==p else [i]
        B=([j for j in Q[:-1] if b>>j&1]+([n] if bp else [])) if i==q else [i]
        h.append(sum(1<<D[u,v] for u in A for v in B))
    return D,h

def local(n,a,b,ap,bp,F,p,q,D,h):
    piv=sorted({p,q});eq={}
    for (i,j),k in D.items():
        if (i==j and i not in piv) or (i==n and j==n):continue
        v=(F>>k)&1;z=sum(((h[t]>>k)&1)<<l for l,t in enumerate(piv))
        assert z.bit_count()<=1 # one common pivot or disjoint parity supports
        if not z and v:bad=[(i,j)];break
        if z and (z,1-v) in eq:bad=[(i,j),eq[z,1-v]];break
        eq[z,v]=(i,j)
    else:return None
    J=set(piv)
    for u,v in bad:J.update(i for i in (u,v) if i<n)
    for mask in (a,b):
        if sum((mask>>i)&1 for i in J)<2:
            J.add(next(i for i in range(n) if (mask>>i)&1 and i not in J))
    return J

def audit():
    rng=Random(261126);norecon=recon=0;largest=0
    for k in range(2000):
        n=rng.randrange(2,31)
        a=rng.randrange(1,1<<n);b=rng.randrange(1,1<<n)
        if min(a.bit_count(),b.bit_count())<2:continue
        if a&b:p=q=((a&b)&-(a&b)).bit_length()-1
        else:p=(a&-a).bit_length()-1;q=(b&-b).bit_length()-1
        ap,bp=rng.randrange(2),rng.randrange(2);D,h=forms(n,a,b,ap,bp,p,q);const=1<<D[n,n]
        L=basis(h+[const]);F=0
        if k%2:
            for z in h+[const]:
                if rng.randrange(2):F^=z
        else:F=rng.getrandbits(n*n)
        J=local(n,a,b,ap,bp,F,p,q,D,h)
        assert (J is None)==member(F,L)
        if J is None:recon+=1;continue
        norecon+=1;largest=max(largest,len(J));assert len(J)<=7
        # Restrict coefficients directly, then independently check span membership.
        ids=sorted(J);nn=len(ids);ix={j:i for i,j in enumerate(ids)};ix[n]=nn
        aa=sum(((a>>j)&1)<<ix[j] for j in ids);bb=sum(((b>>j)&1)<<ix[j] for j in ids)
        DD,hh=forms(nn,aa,bb,ap,bp,ix[p],ix[q]);FF=sum(((F>>k)&1)<<DD[ix[i],ix[j]] for (i,j),k in D.items() if i in ix and j in ix)
        assert aa.bit_count()>=2 and bb.bit_count()>=2
        assert not member(FF,basis(hh+[1<<DD[nn,nn]]))
    print('local obstruction audit',recon,norecon,'max restricted ports',largest)

def witness():
    # r=2 affine example: source u,v; query s,t.
    seen={}
    for u,v,s,t in product(range(2),repeat=4):
        h=(u*(1^s),(u^v)*t,(1^u^v)*t,u*s)
        z=sum(b<<i for i,b in enumerate(h));f=u*s^v*t
        assert h[3]^h[1]^((h[0]^h[3])*(h[1]^h[2]))==f
        assert seen.setdefault(z,f)==f
    assert not any(all(((a&z).bit_count()%2)^c==f for z,f in seen.items()) for a in range(16) for c in range(2))
    print('affine counterexample verified, attained words',len(seen))
if __name__=='__main__':
    finite();audit();witness()

```

### `nonlinear.cpp`

```cpp
#include <array>
#include <iostream>
#include <vector>
#include <map>
using namespace std;
using Code=array<int,4>;
bool affine(const Code &p){return !(p[0]^p[1]^p[2]^p[3]);}
bool nonconstant(const Code&p){int a=7,b=0;for(int x:p){a&=x;b|=x;}return a==0&&b==7;}
int main(){vector<Code> codes;for(int a=0;a<8;a++)for(int b=0;b<8;b++)for(int c=0;c<8;c++)for(int d=0;d<8;d++)if(a!=b&&a!=c&&a!=d&&b!=c&&b!=d&&c!=d&&nonconstant({a,b,c,d}))codes.push_back({a,b,c,d});long long total=0,feasible=0,nonlinear=0,affineonly=0;bool printed=false;map<int,int> all,nonlin;
for(auto P:codes)for(auto Q:codes){++total;array<int,8> tab;tab.fill(-1);bool ok=true;for(int x=0;x<4&&ok;x++)for(int y=0;y<4;y++){int h=P[x]&Q[y],v=__builtin_parity(x&y);if(tab[h]>=0&&tab[h]!=v){ok=false;break;}tab[h]=v;}if(!ok)continue;++feasible;bool lin=false;for(int a=0;a<8;a++)for(int c=0;c<2;c++){bool match=true;for(int h=0;h<8;h++)if(tab[h]>=0&&(__builtin_parity(a&h)^c)!=tab[h]){match=false;break;}if(match)lin=true;}int care=0,pos=0;for(int h=0;h<8;h++)if(tab[h]>=0){care|=1<<h;pos|=tab[h]<<h;}int key=care*256+pos;++all[key];if(!lin){++nonlin[key];++nonlinear;if(affine(P)&&affine(Q))++affineonly;if(!printed){printed=true;cout<<"witness P ";for(int a:P)cout<<a<<" ";cout<<" Q ";for(int a:Q)cout<<a<<" ";cout<<" labels ";for(int a:tab)cout<<a<<" ";cout<<"\n";}}}
for(auto [k,c]:all)cout<<"table "<<k/256<<" "<<k%256<<" "<<c<<" "<<nonlin[k]<<"\n";
cout<<"codes "<<codes.size()<<" pairs "<<total<<" feasible "<<feasible<<" nonlinear-only "<<nonlinear<<" both affine "<<affineonly<<"\n";}

```

### `cost.py`

```python
from collections import Counter
from itertools import combinations_with_replacement,product
from pathlib import Path
M=255
norm=lambda x:min(x,x^M)
prim=tuple(sorted([0]+[norm(sum((r>>i&1)<<r for r in range(8))) for i in range(3)]))
mins={c:0 for c in prim}
states={prim}
for g in range(1,7):
 nex=set()
 for s in states:
  for a,b in combinations_with_replacement(s,2):
   for pa,pb in product((0,M),repeat=2):
    z=norm((a^pa)&(b^pb))
    if z in s:continue
    mins.setdefault(z,g)
    if len(mins)<128:nex.add(tuple(sorted(s+(z,))))
 print('layer',g,'states',len(states),'columns',len(mins)*2)
 if len(mins)==128:break
 states=nex
assert len(mins)==128
A=Counter();N=Counter();U=Counter();W=Counter()
for line in Path(__file__).with_name('nonlinear.log').read_text().splitlines():
 if not line.startswith('table '):continue
 _,care,p,c,nc=line.split();care,p,c,nc=map(int,(care,p,c,nc));g=min(g for z,g in mins.items() if (z&care)==p or ((z^M)&care)==p)
 A[g]+=c;N[g]+=nc;U[g]+=1;W[g]+=bool(nc)
print('all',A,'nonlinear-only',N,'unique tables',U,'unique nonlin tables',W)

```


---

# Previous pending research (archive; current priorities above)

# Research handoff — sharp three-redundancy linear reconstruction theorem

**Agent priority:** continue the end-to-end robust-identifier SAT proof, not an optional native filter. Repository rechecked read-only at `e73ee0f037dda1b83e84e116463515b579d17b39`; `NOTES_ORIENTATION_QUOTIENT.md` blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`, `RESEARCH_NOTES.md` blob `677f9cbdfaf642613ef84db92161d1a78c655254`, unchanged. The external SAT theorem `sat_six_lower'`, transfer, six-bit identity, and robust block-product gate elimination are already Lean-checked per repository. Remaining robust SAT premises: PS_d existence by counting, unit-clause helper identity, length arithmetic (start at multiples of six). Do not duplicate checked work or submit externally. Earlier unreviewed material follows this section. This round is computer-assisted mathematics about a particular mixed interface, NOT an unrestricted superlinear SAT bound; no Lean proof, novelty claim, or native speedup.

## 1. Sharp threshold for homogeneous linear measurement decoding

Work over F2. Let x,y be m-bit vectors, and E=m+r entry signals `h_i=(a_i dot x)(b_i dot y)` where the a_i span m dimensions. For inner product, feasibility forces both a_i and b_i to span m dimensions. All other mixed gates are a Boolean decoder of h only; arbitrary pure-side homogeneous linear preprocessing is free. For matrices Z in F2^(m x m) let K be the kernel of the measurement map `L(Z)_i=a_i^T Z b_i`. The target may be any bilinear functional `T dot Z` (trace for standard inner product). A common Boolean decoder on rank-one inputs exists iff T annihilates every rank<=2 element of K, since precisely those matrices are differences of two rank<=1 matrices. A linear/XOR decoder exists iff T annihilates K.

**Theorem (paper reduction + exhaustive finite certificate): for r<=3, K is spanned by its rank<=2 elements.** Consequently Boolean decodability implies linear decodability for r=0,1,2,3, extending the prior r<=1 theorem. For full-rank inner product the threshold is sharp: at r=4 a nonlinear-only example already exists on m=3, and adjoining independent identity products gives examples for every m>=3. This is a statement about decoder feasibility, not equality of nonlinear and linear decoder *costs*.

### Proof: compression to matrices of at most four rows

Choose m independent a_i and transform row coordinates by the invertible matrix having those a_i as rows. The first m equations now constrain one row each. For a matrix Z in K, each row contributes a syndrome in F2^r to the remaining r equations. The sum of all row syndromes is zero. Split the rows into minimal nonempty zero-sum groups; singleton zero syndromes are allowed. Any group has at most r+1 elements (all but its last syndrome are independent). A matrix retaining just one such group of rows lies in K, and the group matrices sum to Z. This was the previous rank<=r+1 generation theorem.

Now r<=3, so each group retains t<=4 rows. Drop identically zero rows. Let W be its t-by-m row matrix of rank s. If s<=2 nothing needs proving. Otherwise factor W=V R with R a full-row-rank s-by-m matrix spanning the row space of W. The map X -> X R from t-by-s matrices to the original group rows preserves rank. The original m basis equations reduce to t row-local equations (some may be zero); the extra r equations reduce to at most three rank-one linear functionals on X, some possibly zero or equal. All these functionals vanish on V because W belongs to K. A rank<=2 decomposition of V respecting those compressed equations lifts to a rank<=2 decomposition of W in K. Thus it suffices to check only these cases:

- t=s=3: by taking R=W, V=I_3. At most six nonzero rank-one equations, all orthogonal to I_3. It suffices to check every six-element set of such equations, because smaller sets can be padded with other compatible equations. There are 21 distinct nonzero orthogonal rank-one matrices and C(21,6)=54,264 six-sets.
- t=4, s=4: take R=W and V=I_4. Four row-local equations `e_i b_i^T` with b_i's i-th coordinate zero (8 choices each, including zero), plus at most three extra nonzero rank-one equations orthogonal to I_4. There are 105 choices of extra rank-one equation. Pad to three distinct extras. All 8^4*C(105,3)=767,836,160 choices are checked below.
- t=4, s=3: permute rows so the first three are independent and choose those rows as R. V has rows (1,2,4,v) where masks encode three coordinates and v is nonzero. Permute the first three rows and corresponding compressed coordinates to make v one of 1,3,7. This preserves the family of equations, rank and decomposability. There are 4 possibilities for each row-local equation (including zero), 49 nonzero rank-one extra equations orthogonal to each V, and 4^4*C(49,3)=4,716,544 choices for each of the three representatives.

This list is exhaustive; in particular **the rectangular rank-three case cannot be omitted**. The compressed certificates allow zero/repeated equations and do not assume the compressed query vectors have full rank. Row-local equations are crucial in the four-row cases: arbitrary sets of seven rank-one equations in 4x4 matrices can fail rank-two generation. For example H=[51,8706,187,39321,48048,2,4368] has a rank-four element I_4 outside the low-rank span, but its source-vector rank is only three (four redundant measurements relative to source rank). It is not a counterexample to this theorem.

### Finite certificate, executed

The standalone C++17 checker below enumerates each small matrix of rank<=2 as an XOR of two rank-one matrices (zero included). For each normalized W, compute P={Z: rank Z<=2 and rank(Z+W)<=2}. For each measurement equation h, store the bitset of elements of P annihilated by h. If the intersection for the chosen equations is nonempty, W is the sum of two kernel elements of rank<=2. Otherwise build the binary linear span of ALL rank<=2 matrices annihilated by the constraints and verify W is in that span. A zero intersection alone is not a contradiction. The checker uses no solver and no floating point arithmetic.

| Matrix and W | Cases checked | Span fallbacks | Failed decompositions |
|---|---:|---:|---:|
| 3x3 identity | 54,264 | 0 | 0 |
| 4x3, fourth row 1 | 4,716,544 | 252 | 0 |
| 4x3, fourth row 3 | 4,716,544 | 252 | 0 |
| 4x3, fourth row 7 | 4,716,544 | 216 | 0 |
| 4x4 identity | 767,836,160 | 44,840 | 0 |
| Total | 782,040,056 | 45,560 | 0 |

The final symmetry-free replay took 1.395 s on this container with g++ -O3. Earlier independent variants computed ranks by Gaussian elimination instead of rank-one sums: all 20,349 five-sets and all 54,264 six-sets on 3x3 pass the two-term test; 218 row-permutation orbits in 4x4, 40,866,280 cases, 2,664 span fallbacks, all pass; the same rectangular counts independently reproduce. The case counts are exhaustive finite checks, not a random test or a formal proof in Lean. Re-run the complete checker before relying on it. If formalizing, avoid a giant uncategorized `decide` on 782 million instances; seek a smaller algebraic certificate or use the symmetry reductions with a verified checker. This is secondary to the currently nearly complete SAT proof.

## 2. Consequences for mixed-gate cost and sharpness

Use the preceding handoff's parity-on-an-active-cube proof. Since linear reconstruction exists whenever the entry interface is feasible for 0<=r<=3, select m independent source forms from the support of the reconstruction. A query-code parity-check matrix with r rows permits a word supported on those m entries with at least m-r ones (correct the syndrome of the all-ones word on the selected basis with at most r flips). Fix the query to that word. All E entry gates disappear, and the decoder on the independent active ports computes their full parity. Thus

    G >= E + 3 max(0,m-r-1).

For m>r this is G>=4m-2r-3; in particular the new r=2 and r=3 bounds are 4m-7 and 4m-9 respectively (also take max with earlier unconditional mixed-gate bounds). This remains a lower bound, not an exact minimum for redundant interfaces, and uses the actual AND literals being homogeneous linear, with no late pure-side injection. The earlier r=0 exact cost 4m-3 is unchanged.

Sharpness: for m=3 use source masks A=[1,2,4,4,7,5,2], query masks B=[2,3,3,5,2,1,4]. Their kernel is {0,4,0x1d9,0x1dd} of ranks [0,1,3,3] and traces [0,0,1,1]. Thus a Boolean decoder exists, but no XOR decoder. Add independent identity products for m>3. A nonlinear decoder is the original decoder XOR the added products, while any linear reconstruction would restrict to a linear reconstruction of the original example. Redundancy remains 4, so the threshold is sharp for every m>=3. Verified directly for m=3..7 (all 21,824 input pairs in total). For m<=2 all matrices have rank<=2 so no such separation is possible.

No gate saving in this particular smallest counterexample: each of the seven entry coordinates is essential on the care set. The following attained entry words differ only in the indicated bit and have opposite target labels (0-based bit indices):

| bit | entry word 1 | entry word 2 | labels |
|---:|---:|---:|---|
| 0 | 2 | 3 | 0,1 |
| 1 | 1 | 3 | 0,1 |
| 2 | 2 | 6 | 0,1 |
| 3 | 0 | 8 | 0,1 |
| 4 | 0 | 16 | 0,1 |
| 5 | 0 | 32 | 0,1 |
| 6 | 6 | 70 | 1,0 |

A binary-gate decoder needs at least 7-1 gates (trimmed output cone support bound). Thus this encoder needs at least 7+6=13 mixed gates; ordinary three-pair IP has 9. No exact minimum for the decoder is claimed. More generally a nonlinear-only feasible IP measurement list cannot have a feasible sublist of <=m+3 entries, or the theorem would yield a linear reconstruction using the original list. Any decoder must use >=m+4 distinct entry signals, so a live entry-only circuit has at least m+4 entry gates and m+3 decoder gates, hence >=2m+7 total. For exactly m+4 entries all are indispensable. This does not exclude nonlinear-encoding savings in larger cases. A nonlinear decoder on a linearly decodable interface may still be cheaper than computing the XOR of all selected entries, although the parity restriction gives the bound above.

## 3. Reproduction

Save the C++ block as `small_kernel_certificate.cpp`; run `g++ -O3 -std=c++17 small_kernel_certificate.cpp -o small_kernel_certificate && ./small_kernel_certificate`. No other files needed. The Python block independently checks the nonlinear-only example, care sensitivity, kernel ranks, and padded examples. This is exact finite evidence supporting the all-m compression theorem, not a Lean verification. No repository files modified. The meaningful unresolved next target is arbitrary nonlinear/affine encodings or late pure-side injection; more experiments on homogeneous linear encodings with r<=3 are not necessary. L-clb-036 remains open.

```cpp
// Standalone certificate for <=3 redundant homogeneous bilinear measurements.
// Matrices over F2, row-major, packed into <=16 bits.
#include <array>
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
using Mask = array<uint64_t,9>; // at most 560 two-term witnesses
int dot(int x,int y){return __builtin_parity((unsigned)(x&y));}
int outer(int a,int b,int t,int s){int z=0;for(int i=0;i<t;++i)if(a>>i&1)z|=b<<(s*i);return z;}
void insert(array<int,16>& b,int x){while(x){int j=31-__builtin_clz((unsigned)x);if(b[j])x^=b[j];else{b[j]=x;return;}}}
bool member(const array<int,16>& b,int x){while(x){int j=31-__builtin_clz((unsigned)x);if(b[j])x^=b[j];else return false;}return true;}
Mask meet(Mask a,const Mask& b){for(int i=0;i<9;i++)a[i]&=b[i];return a;}
bool intersects(const Mask& a,const Mask& b){for(int i=0;i<9;i++)if(a[i]&b[i])return true;return false;}
struct Test {
 int t,s,W,lim; vector<int> H,L,P; vector<Mask> masks; long long total=0,fallback=0;
 Test(int t_,int s_,int W_):t(t_),s(s_),W(W_),lim(1<<(t*s)),masks(lim){
  vector<int> one{0}; for(int a=1;a<(1<<t);a++)for(int b=1;b<(1<<s);b++)one.push_back(outer(a,b,t,s));
  vector<bool> low(lim,false);for(int a:one)for(int b:one)low[a^b]=true;
  for(int z:one)if(z&&!dot(z,W))H.push_back(z);
  for(int z=0;z<lim;z++)if(low[z]){L.push_back(z);if(low[z^W])P.push_back(z);}
  if(P.size()>576)throw runtime_error("mask too small");
  auto build=[&](int h){for(int i=0;i<(int)P.size();i++)if(!dot(h,P[i]))masks[h][i/64]|=uint64_t(1)<<(i%64);};
  build(0);for(int h:H)build(h);
 }
 void check(const vector<int>& constraints,const vector<int>& candidates){
  ++fallback;array<int,16> basis{};for(int z:candidates){bool ok=true;for(int h:constraints)if(dot(z,h)){ok=false;break;}if(ok)insert(basis,z);}
  if(!member(basis,W))throw runtime_error("rank-two span certificate failed");
 }
 // All six arbitrary rank-one constraints for 3x3 identity. Smaller sets pad.
 void square3(int next,vector<int>& chosen,Mask m){
  if(chosen.size()==6){++total;if(!intersects(m,masks[0]))check(chosen,L);return;}
  for(int i=next;i<=(int)H.size()-(6-(int)chosen.size());i++){chosen.push_back(H[i]);square3(i+1,chosen,meet(m,masks[H[i]]));chosen.pop_back();}
 }
 // Four row-local constraints, including zero, plus three distinct extra rank-one constraints.
 void four_rows(){
  for(int base=0;base<lim;base++){
   vector<int> bh;bool valid=true;Mask bm=masks[0];
   for(int i=0;i<t;i++){int h=base&(((1<<s)-1)<<(s*i));if(dot(h,W)){valid=false;break;}bh.push_back(h);bm=meet(bm,masks[h]);}
   if(!valid)continue;
   vector<int> bl;for(int z:L){bool ok=true;for(int h:bh)if(dot(h,z)){ok=false;break;}if(ok)bl.push_back(z);}
   for(int a=0;a<(int)H.size();a++){Mask am=meet(bm,masks[H[a]]);for(int b=a+1;b<(int)H.size();b++){Mask ab=meet(am,masks[H[b]]);for(int c=b+1;c<(int)H.size();c++){
    ++total;if(intersects(ab,masks[H[c]]))continue;
    // bl already satisfies the four row constraints; only the extra three remain.
    check({H[a],H[b],H[c]},bl);
   }}}
  }
 }
 void report(){cout<<t<<"x"<<s<<" W="<<W<<" constraints="<<H.size()<<" low="<<L.size()<<" two_term="<<P.size()<<" cases="<<total<<" span_fallback="<<fallback<<"\n";}
};
int main(){
 Test a(3,3,1|(2<<3)|(4<<6));vector<int> chosen;a.square3(0,chosen,a.masks[0]);a.report();
 for(int v:{1,3,7}){Test b(4,3,1|(2<<3)|(4<<6)|(v<<9));b.four_rows();b.report();}
 Test c(4,4,0x8421);c.four_rows();c.report();
}
```

```python
# Independent check of sharpness, with no dependencies.
def parity(x): return x.bit_count() & 1

def code(A,x): return sum(parity(a&x)<<i for i,a in enumerate(A))

def outer(a,b,m): return sum(b<<(m*i) for i in range(m) if a>>i&1)

def rank(vs):
    basis={}
    for v in vs:
        while v:
            j=v.bit_length()-1
            if j in basis: v^=basis[j]
            else: basis[j]=v; break
    return len(basis)

A=[1,2,4,4,7,5,2]; B=[2,3,3,5,2,1,4]
H=[outer(a,b,3) for a,b in zip(A,B)]
K=[z for z in range(512) if all(not parity(z&h) for h in H)]
assert K==[0,4,0x1d9,0x1dd]
assert [rank((z>>(3*i))&7 for i in range(3)) for z in K]==[0,1,3,3]
assert [parity(z&0x111) for z in K]==[0,0,1,1]
pairs=0
for m in range(3,8):
    a=A+[1<<i for i in range(3,m)]; b=B+[1<<i for i in range(3,m)]
    D={}
    for x in range(1<<m):
        for y in range(1<<m):
            h=code(a,x)&code(b,y); f=parity(x&y)
            assert D.setdefault(h,f)==f
            pairs+=1
    I=sum(1<<(m*i+i) for i in range(m)); H=[outer(x,y,m) for x,y in zip(a,b)]
    assert rank(H+[I])==rank(H)+1
    if m==3:
        assert len(D)==43
        for i,(u,v) in enumerate([(2,3),(1,3),(2,6),(0,8),(0,16),(0,32),(6,70)]):
            assert u^v==1<<i and D[u]!=D[v]
assert pairs==21824
print('sharpness and indispensable ports verified',pairs)
```

---

# Earlier research (r<=1 proof superseded by the new r<=3 theorem; other results retained)

# Research handoff — higher-weight derivatives and linear redundant entry encodings

**Priority for the agent:** repository now at `e73ee0f037dda1b83e84e116463515b579d17b39`. `SatBridge/SixQ.lean` contains `sat_six_lower'`: for Q>=2, a fan-in-at-most-two external AND/OR/NOT circuit deciding external SAT at length 6Q has `8*Q <= D.size+3`; `sat_not_size_133` rules out size slope 1.33 plus an arbitrary constant. Commit reports `lake build SatBridge` and standard axioms only; I inspected the theorem statements, did not rerun Lean. Do not duplicate the model transfer (`transfer`), six-bit identity (`word_mem_sat`), or this end-to-end theorem. Reuse these and `block_restriction_lower` for the 2n-o(n) bound; prioritize the PS_d finite counting theorem, unit-clause helper identity, and length arithmetic (start on multiples of six). General additive weights and other residues remain separate pending tasks. No external submission or repository write. Both requested notes read after experiments: orientation blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`, research blob `677f9cbdfaf642613ef84db92161d1a78c655254`.

This round's result is conditional on **entry-only, homogeneous linear port codes**, with an additional general semantic test for arbitrary nonlinear port codes. It does not give a new unrestricted SAT lower bound. Earlier pending research is archived below; no obligation to implement all of it.

## 1. Higher-weight fiber derivatives (arbitrary encodings)

Consider IP_m(x,y)=x dot y over F2. Suppose a common mixed circuit first computes E products h_i=p_i(x) AND q_i(y), and every other mixed gate has only mixed operands. Pure-side computations are free. Thus there is a Boolean decoder of h (possibly complemented), with no direct bypass of the interface. Both p and q must be injective because all rows and columns of IP are distinct. The following necessary test permits arbitrary nonlinear p,q and arbitrary decoder topology. For a set D of entry indices, let

    W_D = span_F2 { x+x' : p(x) and p(x') agree outside D }.

For any y with q_i(y)=0 for every i in D, the two entry vectors agree on the pairs in this definition, so `y in W_D^perp`. In particular the number of y's with those zero controls is at most `2^(m-dim W_D)`. Also `dim W_D >= max(0,m-E+|D|)`: each fiber of the projection to the complement of D is contained in one coset of W_D, and there are at most 2^(E-|D|) fibers. This does not require a single-coordinate codeword neighbor. Compute W_D with one representative per fiber and Gaussian elimination, since differences within any fiber are generated by differences to its representative. For a fixed y, the test with D exactly its zero set is **equivalent** to the existence of a decoder for x dot y from h when y is separately known. This is not a sufficiency theorem for a single common decoder without y. The symmetric test applies to q. Enumerating every D is exponential in E; test selected masks or actual zero sets. This is a semantic interface check, not a native runtime improvement or an unrestricted lower bound. On a sample of 640 nonlinear code pairs (m=2..5, E=m+1 or m+2), 57,600 directional fiber-span checks agree with direct per-y fiber enumeration, including 320 planted feasible encoders containing the usual identity products. No separation of two directional tests from exact common decodability occurred in this sample; no equivalence claimed.

## 2. Exact semantic criterion for homogeneous linear codes

Now assume **the actual AND operand literals** at the entry gates are homogeneous linear functions: p_i(x)=a_i dot x, q_i(y)=b_i dot y. Affine constants and nonlinear pure encodings are not covered by the following rank argument. Write A,B for the lists of vectors; both span F2^m. Use Z=xy^T as an m by m matrix, and define the linear measurement map

    L(Z)_i = a_i^T Z b_i,
    K = ker L.

The target is trace Z. For any two rank-one matrices (including zero), the difference of their measurements vanishes precisely when their difference is in K. Conversely every matrix of rank <=2 is the sum of at most two rank-one matrices over F2. Thus **an arbitrary Boolean decoder exists iff trace vanishes on every matrix in K of rank <=2.** This is exact, even if the code is redundant. A linear decoder (XOR of a subset of entry outputs) exists iff trace vanishes on all of K, equivalently I_m lies in the linear span of a_i b_i^T. The distinction is important: linear encodings do not automatically imply linear decoding. Exact finite test: group rank-one matrices by their measurement word and reject a fiber with two different trace values. This is equivalent to exhaustive pair testing but can also compute the span of low-rank kernel elements from differences to one representative per fiber. Cost exponential in m, not a general scalable proof procedure.

## 3. One redundant entry: nonlinear decoding cannot improve feasibility

Let E=m+r and choose m independent a_i. Change the row basis of Z by this invertible matrix; matrix rank is preserved. The first m measurement equations now impose a separate homogeneous condition on each row. The remaining r measurement equations give r-bit syndromes for each row; Z belongs to K iff the sum of those syndromes is zero. Partition this zero-sum list into minimal nonempty zero-sum sublists (including singleton zeros). Each such sublist has at most r+1 elements: a minimal zero-sum list of nonzero vectors has its first k-1 vectors independent, so k-1<=r. Keep the original rows in that sublist and set all other rows to zero. Each resulting matrix belongs to K and has rank <=r+1, and their sum equals Z. Undo the basis change. Thus K is spanned by elements of rank <=r+1.

For r<=1 these ranks are <=2, so common Boolean decodability forces trace to vanish on the entire kernel. An XOR decoder therefore exists whenever any decoder exists. This is a theorem on feasibility, not a claim that the given decoder has the same gate cost as an XOR decoder. No exact-synthesis solver needed.

## 4. A near-saturated mixed-gate lower bound

Suppose E=m+r homogeneous linear entry pairs, with a common Boolean decoder, and that a linear reconstruction exists (automatic for r<=1 by section 3). Let S be a subset with `I_m=sum_(i in S) a_i b_i^T`. Its source vectors span m dimensions. Choose m of those indices forming a basis J. The query code image has dimension m in F2^E, so it has a parity-check matrix H with r rows. Start with word v equal to one on J and zero outside. The syndrome Hv is in the span of H columns indexed by J. Choose at most r of those columns whose sum equals Hv, and flip those coordinates. The resulting word q* is in the query code image, still zero outside J, with at least m-r ones. There is a query y* producing it.

Fix y=y*. Every entry gate becomes a constant or its source operand; all E entry gates disappear. The active source forms are independent, since their indices are in J, so the active outputs range over a full cube of dimension k>=m-r. On this cube the decoder computes parity of all k active outputs (all are in S), by the linear reconstruction identity. The classical free-NOT AIG parity lower bound is 3(k-1) for k>=1 (Schnorr; see previous proof). Therefore the original mixed circuit needs at least

    G >= E + 3 max(0,m-r-1).

In particular for 0<=r<m, `G>=4m-2r-3`. For one redundant entry, **G>=4m-5** without any restriction on decoder fan-out. The r=0 bound is the previous exact 4m-3; for r=1 this is only a lower bound, not an exact optimum. For r>=4 the linear reconstruction assumption must be proved for that code; the new first section establishes automatic reconstruction for r<=3. This covers arbitrary redundant linear port codes satisfying that assumption and excludes savings of a linear number of gates with o(m) redundant entries. It does not cover general mixed gates that inject extra pure-side signals later, affine/nonlinear port codes, or all unrestricted circuits.

## 5. Explicit barrier: nonlinear decoder genuinely needed

For m=3 use seven entries, source masks A=[1,2,4,4,7,5,2] and query masks B=[2,3,3,5,2,1,4]. Bit i of a mask selects source/query variable i. Store Z in row-major bit order (bit 3*i+j). Direct Gaussian elimination or exhaustive 9-bit enumeration gives

    K = {0x000, 0x004, 0x1d9, 0x1dd}
    ranks = [0,1,3,3]
    traces = [0,0,1,1].

By section 2 an arbitrary decoder exists, but no XOR decoder exists. All 64 input pairs agree on the 43 attained entry words. This rules out extending section 3 solely by the linearity of the port codes. It is not a claim that this encoder saves gates versus ordinary IP. A general high-redundancy example for every odd m>=3: use all off-diagonal products x_i*y_j (i!=j) and (x_0 XOR x_i)*(y_0 XOR y_i) for i=1..m-1. The kernel consists of scalar multiples of I_m (off-diagonal entries vanish and diagonal entries agree); rank m for its nonzero element and trace one for odd m. So a nonlinear decoder exists with E=m^2-1, but linear reconstruction fails. The small r=4 example above is stronger at m=3. The new first section closes r=2 and r=3 using a finite matrix certificate.

## 6. Executed verification and next steps

The script below is Python stdlib only. Results: 612 exhaustive full-rank ordered nonzero linear code pairs at m=2,E=2/3; 1,440 random full-rank code pairs at m=3..5,r=0..3; 720 random kernel-generation checks (r<=1), in addition to the 612 exhaustive cases; 202 feasible cases in the exhaustive+random pool with the active-cube witness checked; 960 planted linear-reconstruction examples (m=2..8,r<=4) with every source assignment checked against parity on the independent active ports; two larger nonlinear-only examples plus the explicit seven-entry example; 640 nonlinear pairs and 57,600 fiber-span checks as above. All assertions passed. No solver-based minimum, native benchmark, formal proof check, or literature novelty claim. These tests support the finite premises and constructions; the unbounded lower bound follows from the proof, not from sampling. The known parity lower bound is discussed in https://www.math.toronto.edu/rossman/2429-L2.pdf .

The new first section closes the r<=3 gap. Next: derive a bound for nonlinear codebooks via the dimensions of W_D. Do not assume high-density codebooks contain large full coordinate cubes (even parity code is a counterexample). The stronger theorem is still linear and interface-conditional; no solution of L-clb-036 or improved SAT coefficient. Continue the robust identifier Lean proof in parallel.

### Reference implementation (`linear_redundancy_check.py`)

```python
"""Exact entry-only linear-code semantics and gate lower-bound certificates."""
from itertools import product,combinations
from random import Random
from collections import Counter

def span(xs):
    b={}
    for x in xs:
        while x:
            j=x.bit_length()-1
            if j in b:x^=b[j]
            else:b[j]=x;break
    return b

def rank(xs):return len(span(xs))
def contains(b,x):
    while x:
        j=x.bit_length()-1
        if j not in b:return False
        x^=b[j]
    return True

def parity(x):return x.bit_count()&1

def outer(x,y,m):return sum((y if (x>>i)&1 else 0)<<(m*i) for i in range(m))
def target(m):return sum(1<<(i*m+i) for i in range(m))
def code(A,x):return sum(parity(a&x)<<i for i,a in enumerate(A))
def measurements(A,B,m):return [outer(a,b,m) for a,b in zip(A,B)]
def linear_reconstruction(A,B,m):
    # recover a subset mask if the identity is in the measurement span
    bs={}
    for i,v in enumerate(measurements(A,B,m)):
        c=1<<i
        while v:
            j=v.bit_length()-1
            if j in bs:w,d=bs[j];v^=w;c^=d
            else:bs[j]=(v,c);break
    v=target(m);c=0
    while v:
        j=v.bit_length()-1
        if j not in bs:return None
        w,d=bs[j];v^=w;c^=d
    return c

def collision_test(A,B,m):
    # independent exact test using input pairs, not the kernel formulation
    seen={}
    for x in range(1<<m):
        p=code(A,x)
        for y in range(1<<m):
            h=p&code(B,y);z=parity(x&y)
            if h in seen and seen[h]!=z:return False
            seen[h]=z
    return True

def kernel_test(A,B,m):
    H=measurements(A,B,m);I=target(m)
    # enumerate differences of two rank-one matrices, includes rank <= 1
    one={outer(x,y,m) for x in range(1<<m) for y in range(1<<m)}
    good={}
    for z in one:
        q=code(H,z);t=parity(I&z)
        if q in good and good[q]!=t:return False
        good[q]=t
    return True

def low_rank_span_check(A,B,m):
    H=measurements(A,B,m)
    one={outer(x,y,m) for x in range(1<<m) for y in range(1<<m)}
    groups={}
    for z in one:groups.setdefault(code(H,z),[]).append(z)
    # differences to one representative span all pairwise differences
    lo=rank(z^g[0] for g in groups.values() for z in g)
    return lo,m*m-rank(H)

def witness(A,B,m,c):
    # Kill unselected entry coordinates and enough selected ones to leave a basis.
    # Among q words satisfying these zeros, choose one with few additional zeros.
    E=len(A);allbits=(1<<E)-1
    keep=[]
    for i,a in enumerate(A):
        if (c>>i)&1 and rank([A[j] for j in keep]+[a])>len(keep):keep.append(i)
    assert len(keep)==m
    K=sum(1<<i for i in keep)
    qs=[(code(B,y),y) for y in range(1<<m)]
    q,y=max(((q,y) for q,y in qs if q&~K==0),key=lambda v:v[0].bit_count())
    assert q.bit_count()>=max(0,m-(E-m))
    assert not (q&~c) and rank(A[i] for i in range(E) if q>>i&1)==q.bit_count()
    # Every active entry word occurs and IP equals its parity.
    seen=set()
    for x in range(1<<m):
        h=code(A,x)&q;seen.add(h)
        assert parity(h)==parity(x&y)
    assert len(seen)==1<<q.bit_count()
    return q.bit_count()

def construct(m,rng,r):
    # planted linear decoder: start with identity, add arbitrary extra measurements
    # apply paired invertible basis changes, use randomized order
    A=[1<<i for i in range(m)]; B=A.copy()
    for _ in range(m*3):
        i,j=rng.sample(range(m),2)
        # add row j to row i on A vectors; dual column operation on B vectors
        A=[a^((1<<i) if (a>>j)&1 else 0) for a in A]
        B=[b^((1<<j) if (b>>i)&1 else 0) for b in B]
    A += [rng.randrange(1,1<<m) for _ in range(r)]
    B += [rng.randrange(1,1<<m) for _ in range(r)]
    perm=list(range(m+r));rng.shuffle(perm)
    return [A[i] for i in perm],[B[i] for i in perm]

def main():
    rng=Random(261126);counts=Counter();weak=Counter()
    # Exhaust all ordered, nonzero port codes of length 2 or 3 at m=2.
    for E in (2,3):
        for A in product(range(1,4),repeat=E):
            for B in product(range(1,4),repeat=E):
                if rank(A)!=2 or rank(B)!=2:continue
                ok=collision_test(A,B,2);c=linear_reconstruction(A,B,2)
                assert ok==kernel_test(A,B,2)==(c is not None)
                assert low_rank_span_check(A,B,2)[0]==low_rank_span_check(A,B,2)[1]
                counts['exhaustive']+=1
                if ok:witness(A,B,2,c);counts['feasible']+=1
    # Full-rank random codes, with exact collision and kernel checks.
    for m in (3,4,5):
        for r in (0,1,2,3):
            for _ in range(120):
                E=m+r
                while True:
                    A=[rng.randrange(1,1<<m) for _ in range(E)]
                    B=[rng.randrange(1,1<<m) for _ in range(E)]
                    if rank(A)==rank(B)==m:break
                ok=collision_test(A,B,m);c=linear_reconstruction(A,B,m)
                assert ok==kernel_test(A,B,m)
                assert not (c is not None and not ok)
                if r<=1:
                    assert ok==(c is not None)
                    lo,k=low_rank_span_check(A,B,m);assert lo==k
                    counts['kernel_generation']+=1
                if ok and c is None:weak[m,r]+=1
                if c is not None:witness(A,B,m,c);counts['feasible']+=1
                counts['random']+=1
    for m in range(2,9):
        for r in range(0, min(4,m)+1):
            for _ in range(30):
                A,B=construct(m,rng,r);c=linear_reconstruction(A,B,m);assert c is not None
                witness(A,B,m,c);counts['planted']+=1
    # Counterexample to extending linear reconstruction to all redundancy:
    # all off-diagonal products plus m-1 diagonal-pair sums, m odd.
    for m in (3,5):
        A=[];B=[]
        for i in range(m):
            for j in range(m):
                if i!=j:A.append(1<<i);B.append(1<<j)
        for i in range(1,m):A.append(1|(1<<i));B.append(1|(1<<i))
        assert len(A)==m*m-1 and rank(measurements(A,B,m))==m*m-1
        assert collision_test(A,B,m) and kernel_test(A,B,m)
        assert linear_reconstruction(A,B,m) is None
        counts['nonlinear_counterexamples']+=1
    print(dict(counts));print('random feasible but nonlinear-only:',dict(weak))
if __name__=='__main__':main()


def fiber_spans(P,E):
    # W[D] spans differences of sources whose code agrees off D.
    W=[];M=(1<<E)-1
    for D in range(1<<E):
        rep={};diff=[]
        for x,p in enumerate(P):
            t=p&(M^D)
            if t in rep:diff.append(x^rep[t])
            else:rep[t]=x
        W.append(span(diff))
    return W

def directional(P,Q,E):
    W=fiber_spans(P,E);m=(len(P)-1).bit_length();M=(1<<E)-1
    for D,w in enumerate(W):assert len(w)>=max(0,m-E+D.bit_count())
    ok=all(all(not parity(y&v) for v in W[M^q].values()) for y,q in enumerate(Q))
    # Separate direct check: output known on each active-port fiber for fixed y.
    brute=True
    for y,q in enumerate(Q):
        seen={}
        for x,p in enumerate(P):
            h=p&q;z=parity(x&y)
            if h in seen and seen[h]!=z:brute=False
            seen[h]=z
    assert brute==ok
    if ok:
        for D,w in enumerate(W):assert sum(q&D==0 for q in Q)<=1<<(m-len(w))
    return ok,len(W)

def nonlinear_test():
    rng=Random(261127);checks=Counter();sep=None
    for m in (2,3,4,5):
        for r in (1,2):
            E=m+r
            for j in range(80):
                if j<40:
                    # Original identity products plus arbitrary nonlinear redundant ports.
                    P=[x|(rng.randrange(1<<r)<<m) for x in range(1<<m)]
                    Q=[y|(rng.randrange(1<<r)<<m) for y in range(1<<m)]
                    perm=list(range(E));rng.shuffle(perm)
                    P=[sum(((x>>i)&1)<<k for k,i in enumerate(perm)) for x in P]
                    Q=[sum(((y>>i)&1)<<k for k,i in enumerate(perm)) for y in Q]
                else:
                    P=rng.sample(range(1<<E),1<<m);Q=rng.sample(range(1<<E),1<<m)
                u,n=directional(P,Q,E);v,k=directional(Q,P,E)
                checks['fiber_span_checks']+=n+k;checks['code_pairs']+=1
                hmap={};ok=True
                for x,p in enumerate(P):
                    for y,q in enumerate(Q):
                        h=p&q;z=parity(x&y)
                        if h in hmap and hmap[h]!=z:ok=False
                        hmap[h]=z
                assert not ok or (u and v)
                if j<40:assert ok
                if u and v and not ok:
                    checks['directional_only']+=1
                    if sep is None:sep=(m,E,P,Q)
    # Explicit smaller nonlinear-only linear measurement example.
    A=[1,2,4,4,7,5,2];B=[2,3,3,5,2,1,4];m=3
    K=[z for z in range(1<<(m*m)) if not code(measurements(A,B,m),z)]
    assert K==[0,4,0x1d9,0x1dd]
    assert [rank((z>>(m*i))&7 for i in range(m)) for z in K]==[0,1,3,3]
    assert [parity(z&target(m)) for z in K]==[0,0,1,1]
    assert collision_test(A,B,m) and linear_reconstruction(A,B,m) is None
    print(dict(checks),'directional-only example:',sep)

if __name__=='__main__':nonlinear_test()

```

---

# Earlier research (archive; current priorities above)

# Research handoff — redundancy, reset forests, and two-sided rectangle covers

**Historical priority (superseded by current header):** the local Lean gate-elimination core for the robust identifier lower bound is now checked. Do not reprove it through the additive-weight recurrence. Read the updated `NOTES_SAT_ENCODING_BOUNDS.md` at [6884d92](https://github.com/Krapples/circuit-synthesis-research/commit/6884d92b020b183c48efc346ebf3fe9a45d7cc8f): `Robust.lean`, `BlockProduct.lean`, `block_restriction_lower`. The remaining SAT-side premises are the PS_d counting existence theorem, unit-clause helper identity, full support (start with L037 multiples of six), length padding, and external model translation. The agent reports `B >= n + q(2r-3d+3)` (one better than our original `n-1+...`) conditional on those premises. Complete that end-to-end; the six-bit XNOR route and general additive weight are separate pending tasks. For PS_d existence, count exactly `binom(r,d)*2^(r-d)*2*d*(d-1)` possible bad events on d-dimensional subcubes: ordered (fixed input u, tested input v), and phase of u. Each event equates `2^(d-2)` disjoint pairs of independent truth-table rows, so exactly `2^(2^r-2^(d-2))` full tables satisfy it. If the product of event count and that cardinality is smaller than `2^(2^r)`, there is a good table. This finite cardinality proof can avoid a probability library. Restricting further to d free variables preserves any failure, so the exact-d property suffices. The repo's threshold calculation scans powers of two: the first passing power is n=2^32, not the first even length. For its conservative explicit bound using h<=2^r and the exact PS_d union-bound d, the first passing even length is 3,762,291,468 (r=22,d=8,L=52). Derivation: let A=2r-3d+3, H=2^r+1, q=floor(n/L)-H>=1. The advantage n+Aq-floor(17n/12)+4 cannot increase between multiples of L. At n=Lk and A>0 it is positive iff (12A-5L)k>12(AH-4). For positive delta=12A-5L, take k=max(H+1, floor(12(AH-4)/delta)+1); for delta<=0 no advantage in the feasible range. Minimize over r=2..32; larger r cannot fit at any n<=2^32. This is a crossover of a conservative numeric lower bound, not a claim about true circuit minima or all possible helper tables.

This round's new results below concern mixed-gate accounting, not a new SAT coefficient. The previous three pending research sections are retained; older reviewed optional topology filters are summarized in the repository notes rather than repeated in full. No native changes, Lean verification of the new results, independent review, or novelty claim. Both requested repository notes were reread after experiments at `6884d92` (orientation blob `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`; research blob `f6c7abd063bf3ef8529c34e6a4e60caaaa3cb3b7`).

## 1. A reset-forest capacity theorem allowing arbitrary redundancy

Use the previous mixed-DAG model, with pure-side computations free, arbitrary complemented edges, trimmed mixed output cone, and no literal constant operands. Let E,U,Q,M count entry, source-controlled, query-controlled and two-mixed-input gates. Source operand occurrences a=E+U, query occurrences b=E+Q. Write e=M-E+1 for excess mixed edges (count multiplicity); G+1=a+b+e. Relax every pure operand occurrence to an independent bit, absorbing its phase. Let N_x be the number of distinct residuals on y when x varies; N_y symmetric. These cannot exceed relaxed profile counts. Put r=a-log2 N_x and s=b-log2 N_y (nonnegative, not necessarily integers).

Cut **all outgoing mixed edges** of each mixed wire with at least two reader occurrences. Let h be the number of such fork vertices, h<=e. The result is a forest rooted at the output and at the h fork vertices. Exactly e+h edges are removed; every removed edge starts at a component root. Each forest component is a tree of mixed gates, with removed operand occurrences replaced by placeholders. Components can be evaluated in increasing order of the original topological indices of their roots: an intercomponent edge runs from one root to a node with a path to another root. Thus there is no cyclic component dependency.

For source residual counting, mark all E and U gates (one independent source bit per mark). At each forest root traverse toward its operands, and at a marked node read its source bit. If 0, stop below it (its value is a constant 0); if 1, traverse its remaining mixed children. At unmarked nodes traverse all remaining children. Keep the tuple of visited source bits, with their IDs; removed operands are formal placeholders during this traversal. The tuple for all roots determines all component symbolic residual functions of query ports and placeholders, and therefore the actual full relaxed residual after substitution. Complemented edges do not affect this implication. Count these tuples exactly by a bottom-up forest DP:

    t(v) = product_{w child of v} t(w)       [unmarked]
    t(v) = 1 + product_{w child of v} t(w)   [marked]
    T_x = product_{v forest root} t(v).
    N_x <= T_x.

An empty product is 1. At a marked node the 0 branch yields one tuple; the 1 branch yields the Cartesian product of child tuples, disjoint from the 0 branch because its own bit is recorded. Independent source occurrences and disjoint forest subtrees justify multiplication. T_x is an exact count of the relaxed forest transcripts, NOT necessarily the exact number of residual Boolean functions. Real pure signals may be correlated; the relaxation only enlarges the possibilities.

Let I_x count marked nodes whose forest subtrees contain at least one other marked node. Such a node has child product t>=2, and `1+t <= (3/4)*2*t`. For other marks the ratio is exactly 1. Inductively

    N_x <= T_x <= 2^a (3/4)^I_x.

Each U with no marked descendant must have a removed mixed edge in its forest subtree (including at its own mixed operand). To see this, follow mixed predecessors in the original DAG: unless a removed edge is encountered, the path reaches an E or another marked U. The forest subtrees of these particular U nodes are disjoint: one cannot contain another marked node. Their witnessing removed edges are therefore distinct. At most e+h such U exist. Consequently

    I_x >= max(0, U-e-h),
    U <= e+h + r/log2(4/3) <= 2e + r/log2(4/3),
    Q <= e+h + s/log2(4/3) <= 2e + s/log2(4/3).

This is valid even when neither port code is a full cube. It charges source-control chaining to redundant encoding bits and mixed reconvergence simultaneously. In particular when e=0, U<=2.410*r and Q<=2.410*s. When r=0 there is a sharper result below. These are necessary resource inequalities, not an additive lower bound across overlapping partitions. Compute exact T_x and T_y in O(G) arithmetic operations (big integers may have O(a+b) bits), not exponential enumeration.

**Sharper saturation lemma.** If N_x=2^a, all relaxed source rows are distinct. For every E or U vertex there must be a path to the output avoiding all other source-marked vertices: set all other source ports to zero, and compare its two possible values. If no such path exists, these rows coincide. Remove the U mixed-input edges (one per U). Every marked vertex still reaches the output. Every remaining mixed vertex is reachable from some marked vertex in the forward graph (induct in topological order: Q and M have remaining mixed predecessors, E and U are marked). Let L be the vertices still reaching output. They contain all marked vertices, and require at least |L|-1 edges. Each vertex outside L has a remaining incoming mixed edge, distinct by destination, so the remaining graph has at least G-1 edges overall. Hence e>=U. Similarly, if N_y=2^b then e>=Q. This improves the forest bound at exact saturation without assuming a mixed tree.

## 2. Two-sided monochromatic rectangle covers: mixed-tree lower bound for inner product

A rectangle is a product of a set of source assignments and a set of query assignments. A signed pure-side leaf has a cover of size at most one rectangle for each output value. For a formula with child syntactic cover counts (T0,T1)=(a,b),(c,d), an AND has counts (a+c,b*d): cover its zeros by the union of child zero covers, and its ones by their pairwise intersections (intersection of rectangles is a rectangle). A complement swaps counts. These are upper bounds, not minimum cover sizes; they hold for arbitrary repeated/correlated pure-side leaf functions. Thus a mixed tree with L=G+1 pure-leaf occurrences yields a pair on the read-once count recurrence (with each occurrence treated as a distinct leaf).

For L>=1, either count is at most J(L), the maximum product of positive integers summing to L, which is at most 3^(L/3). Proof by induction: a one-leaf count is 1; products combine partitions; a sum of maxima from children both of size >=2 is at most their product; if one child is a single leaf, increase any part of a maximizing partition of the other child's size by one to obtain a product at least its old product plus 1. This includes the two-single-leaf case. Each integer k<=3^(k/3). Also

    T0*T1 <= L*3^(L/3).

Induct on the formula: at an AND `(a+c)*b*d = (a*b)*d + (c*d)*b`, bounded by `L1*3^(L1/3)*3^(L2/3) + L2*3^(L2/3)*3^(L1/3)`. Complement changes nothing. (Can improve the exponent by 1/3 by keeping the base L=1 tight.)

For IP_m(x,y)=x dot y over F2, any zero monochromatic rectangle A×B has size <=2^m: B is orthogonal to span A, and |A|<=2^dim(span A). Any nonempty one rectangle has size <=2^(m-1): choose x0 in A and D=span(A-x0), so B is orthogonal to D and lies in x0 dot y=1, a nonempty half of D^perp. The numbers of ones and zeros of IP are respectively 2^(m-1)*(2^m-1) and 2^(m-1)*(2^m+1). Thus every cover has at least `2^m-1` one rectangles and `2^(m-1)+1` zero rectangles. The mixed-tree count pair must dominate these two bounds.

    (2^m-1)(2^(m-1)+1) <= (G+1)*3^((G+1)/3).

It follows that any IP_m circuit with **no mixed reconvergence** needs at least `(6/log2 3)*m-O(log m)` mixed gates, about `3.78558*m-O(log m)`, allowing arbitrarily expensive pure-side logic and arbitrary redundancy. This is not a whole-circuit unrestricted bound; the condition is e=0. For general mixed DAGs, unfolding gives the same cover condition with L equal to the number of pure-leaf occurrences in the unfolded mixed tree. L is computed by propagating output path multiplicities backwards. In particular L<=(G+1-e)*2^e, since each path has at most the product of reader degrees as choices and d<=2^(d-1). This loses strength rapidly with e; do not substitute G+1 for L in a DAG. We use the rectangle argument in its strongest applicable model, not as a proof that reconvergence is expensive.

Finite improvement: use the Pareto frontier of (T0,T1) for each leaf budget, starting at (1,1) and combining `(a+c,b*d)` and its swap. Coordinatewise dominated pairs can be dropped safely because recurrence is monotone. This exactly enumerates the maximal **syntactic count pairs**, not the realizable IP functions. If no pair at L dominates the IP cover requirements, that leaf budget is excluded. Computed up to L=40:

| m | required tree leaves at least | mixed gates at least |
|---:|---:|---:|
| 2 | 5 | 4 |
| 3 | 8 | 7 |
| 4 | 11 | 10 |
| 5 | 14 | 13 |
| 6 | 17 | 16 |
| 7 | 21 | 20 |
| 8 | 24 | 23 |
| 9 | 28 | 27 |
| 10 | 31 | 30 |
| 11 | 35 | 34 |
| 12 | 39 | 38 |

Combine these with prior unconditional bounds; e.g. IP_2 actually needs at least 5 mixed gates from the earlier theorem, and the rectangle bound alone does not establish realizability at its first passing budget. Standard rectangle-cover background: Roughgarden, *Communication Complexity (for Algorithm Designers)*, https://www.timroughgarden.algorithmsilluminated.org/w15/l/w15.pdf . No literature novelty claim for rectangle covers or the resulting linear bound.

## 3. An entropy-based robustness result with one saturated side

Suppose IP_m has exactly a=m source occurrences but b=m+s query occurrences, with s>=0 an integer. Unlike bilateral saturation, do not assume the query code exhausts its port cube. The source code is a bijection; write alpha(p) for its inverse from the m-bit source port word to original x. For source entry coordinate i (one of E), let W_i=span{alpha(p) XOR alpha(p XOR e_i):all p}. Its dimension d_i>=1. If its corresponding entry query control q_i(y)=0, the output is independent of p_i, so y is orthogonal to W_i. Thus `Pr_y[q_i=0]<=2^(-d_i)` for uniform y. Let H2 denote binary entropy. The query port word determines y (all IP columns distinct), so its entropy is m and by subadditivity

    sum_{j=1}^{m+s} (1-H2(Pr[q_j=0])) <= s.

Each entry with d_i>=2 contributes at least `c=1-H2(1/4)=0.1887218755...`. Therefore at most s/c entry coordinates have d_i>=2. Let k be the number of entries with d_i=1. For such a coordinate all its derivatives equal the unique nonzero vector u_i of W_i, independent of p. These u_i are linearly independent: if a nonempty subset summed to zero, flipping that subset of p coordinates in succession would preserve alpha, violating injectivity. Choose y* with u_i dot y*=1 for all k of them (surjective system of independent linear equations). All their query controls equal 1. Fix y=y* and every other source port arbitrarily. The residual is parity on these k independent port bits, up to constant phase. Each of their entry gates aliases directly to its source bit and is eliminated. By the 3(k-1) free-complement AIG parity lower bound (proof in previous handoff), `G>=k+3(k-1)=4k-3` for k>=1 (trivial for k=0).

Consequently, with arbitrary reconvergence,

    G >= 4E - 4s/c - 3.

Use exact integer `floor(s/c)` when desired, or just keep real inequality. If E=m (no U gates), this is `G>=4m-O(s)`, so o(m) extra query occurrences cannot save a linear fraction of the saturated 4m-3 cost. In general the saturation lemma gives U<=e and E>=m-e. Substituting `G=2m+s+e-1` gives

    G >= (12m + 4s - 4s/c - 7)/5.

In particular when a=m and s=o(m), `G>=2.4m-o(m)` without requiring entry-only source logic. For s=0 the earlier stronger exact 4m-3 theorem still applies after constant cleanup. Symmetry permits swapping source and query sides. These are conditional bounds on occurrence budgets. They do NOT establish `C_mix(IP_m)=4m-3` for arbitrary redundant codes.

A concrete barrier to extending this proof to a=m+r with r>=1: the code p=(x,parity(x)) has 2^m words of length m+1 and contains no cube edge. Single-coordinate flips of p are then never valid inputs. The forced derivative proof cannot assume the presence of any full-cube direction in a dense code. The forest theorem above does not have this limitation, but is weaker semantically. A possible next step is to use higher-weight differences on actual code fibers, without paying exponentially for their length.

## 4. Executed verification and implementation

`redundant_mixing_check.py` is Python 3 stdlib. Extract `mixed_profiles.py` and `bilateral_check.py` from the retained handoffs below into the same directory; run `python redundant_mixing_check.py`. No SAT solver results needed. Local replay passed:

- 13,001 fully live relaxed descriptions through five mixed gates, 26,002 directional forest checks. 137,932 source/query assignment transcript comparisons; identical transcripts always give identical full residual tables; DP count equals independently enumerated tuple count. In 6,156 directional checks I>0 (4,416 with reconvergence); 4,700 exact saturation checks satisfy U<=e or Q<=e.
- Pareto frontiers through 40 leaves; 466 maximal count pairs at 40. Each count at most the integer-break bound; all products satisfy L*3^(L/3). 65,259 nonempty rectangle enumeration checks for m=1..3, verifying the size bounds for monochromatic rectangles. The finite table is a lower-bound screen, not an exact synthesis result.
- 600 random source bijections and legal query encodings (m=2..7), 3,636 derivative/entropy/active-direction checks. Query encodings start with random supersets of the required parity supports and add raw query bits, then greedily remove those raw bits if injection survives. These test necessary code properties, not optimal circuit synthesis.
- Six explicit nonlinear-encoding mixed circuits m=3..8: alpha is a reversible Toffoli map, entry controls `q0=y0 OR y2`, `q1=y1 OR y2`, other entries q_i=y_i, with three extra query occurrences y0,y1,y2. Compute IP as XOR of h0*y0,h1*y1,h2,h0*h1*y2,h3,...; cost 4m+4 (constructive, not minimal); a=m, b=m+3. 87,360 exhaustive truth evaluations passed. These demonstrate actual non-affine saturated source codes, and validate that allowing redundant query ports is a substantive relaxation.

No contradiction to small unrestricted circuits has been obtained. No new SAT lower-bound coefficient or solution to L-clb-036. The best unconditional inner-product mixed bound from our work remains 2m+1 (m>=2); the new stronger bounds concern low-reconvergence or one-sided saturation. Do not spend native implementation time on these screens without a matching topology use case. Prioritize completing the SAT-side Lean obligations. Next theoretical focus: constraints on actual codeword differences when both sides are redundant; test on IP and list-disjointness, where small explicit circuits are known.

### Reference implementation (`redundant_mixing_check.py`)

```python
from math import log2,ceil
from itertools import product
from random import Random
from functools import lru_cache

# Pareto frontier of (T0,T1) syntactic cover counts with L leaves.
def pareto(xs):
    best=0; out=[]
    for a,b in sorted(set(xs),reverse=True):
        if b>best: out.append((a,b));best=b
    return tuple(out)

def fronts(n):
    F=[(),((1,1),)]
    for l in range(2,n+1):
        cand=[]
        for i in range(1,l//2+1):
            for a,b in F[i]:
                for c,d in F[l-i]:
                    x,y=a+c,b*d
                    cand.extend(((x,y),(y,x)))
        F.append(pareto(cand))
    return F

def tree_min(m,F):
    x,y=(1<<(m-1))+1,(1<<m)-1
    return next((l for l in range(1,len(F)) if any(a>=x and b>=y for a,b in F[l])),None)

def max_terms(l):
    if l<=1:return 1
    q,r=divmod(l,3)
    return 3**q if r==0 else (4*3**(q-1) if r==1 else 2*3**q)

def rectangle_tests():
    count=0
    for m in (1,2,3):
        N=1<<m; rows=[sum(((x&y).bit_count()%2)<<y for y in range(N)) for x in range(N)]
        for A in range(1,1<<N):
            for B in range(1,1<<N):
                vals={bool(rows[x]>>y&1) for x in range(N) if A>>x&1 for y in range(N) if B>>y&1}
                if len(vals)==1:
                    assert A.bit_count()*B.bit_count() <= (1<<(m-int(next(iter(vals)))))
                count+=1
    return count

def rank(vs):
    basis={}
    for v in vs:
        while v:
            k=v.bit_length()-1
            if k not in basis:basis[k]=v;break
            v^=basis[k]
    return len(basis)

def entropy(p):return -sum(v*log2(v) for v in (p,1-p) if v)

def entropy_tests():
    R=Random(261126);count=0; cases=0
    for m in range(2,8):
        N=1<<m
        for _ in range(100):
            alpha=list(range(N));R.shuffle(alpha)
            # Generate legal pure query gates at each entry: must be 1 if any
            # derivative of coordinate i has dot product 1 with y.
            ds=[{alpha[p]^alpha[p^(1<<i)] for p in range(N)} for i in range(m)]
            ranks=[rank(d) for d in ds]
            q=[]
            for d in ds:
                q.append([int(any((v&y).bit_count()%2 for v in d) or R.randrange(2)) for y in range(N)])
            # Add raw y bits to ensure injectivity. Then remove redundant
            # query bits greedily as long as injection remains; never remove entries.
            q.extend([[y>>i&1 for y in range(N)] for i in range(m)])
            for j in reversed(range(m,len(q))):
                new=q[:j]+q[j+1:]
                if len(set(zip(*new)))==N:q=new
            s=len(q)-m
            assert len(set(zip(*q)))==N
            bad=sum(r>1 for r in ranks)
            c=1-entropy(.25)
            assert bad*c <= s+1e-9
            for i,d in enumerate(ds):
                zeros=N-sum(q[i]);assert zeros<=1<<(m-ranks[i]);count+=1
            good=[i for i,r in enumerate(ranks) if r==1]
            dirs=[next(iter(ds[i])) for i in good]
            assert rank(dirs)==len(dirs)
            y=next(y for y in range(N) if all((v&y).bit_count()%2 for v in dirs))
            for p in range(N):
                for i in good:
                    assert ((alpha[p]^alpha[p^(1<<i)])&y).bit_count()%2==1 and q[i][y]
                    count+=1
            cases+=1
    return cases,count

if __name__=='__main__':
    F=fronts(40)
    for l in range(1,len(F)):
        for a,b in F[l]:
            assert max(a,b)<=max_terms(l)
            assert a*b<=l*3**(l/3)+1e-6*max(a*b,1)
    print('frontier sizes',[(i,len(F[i])) for i in (5,10,20,40)])
    print('tree minimum leaf bounds',[(m,tree_min(m,F)) for m in range(1,13)])
    print('rectangle checks',rectangle_tests())
    print('entropy checks',entropy_tests())

def forest_bound(spec,source='U'):
    n=len(spec); parents=[]; outdeg=[0]*n
    for op in spec:
        pp=() if op[0]=='E' else (op[1],) if op[0] in 'UQ' else (op[1],op[3])
        parents.append(pp)
        for v in pp:outdeg[v]+=1
    assert all(outdeg[:-1]) and outdeg[-1]==0
    e=sum(outdeg)-n+1
    forks={i for i,d in enumerate(outdeg) if d>1}
    roots=sorted(forks|{n-1})
    children=[tuple(v for v in pp if v not in forks) for pp in parents]
    controls={i:j for j,i in enumerate(i for i,op in enumerate(spec) if op[0] in ('E',source))}
    counts=[];size=[];internal=0
    for i,ch in enumerate(children):
        t=1;s=0
        for v in ch:t*=counts[v];s+=size[v]
        if i in controls:
            internal+=bool(s);t+=1;s+=1
        counts.append(t);size.append(s)
    total=1
    for i in roots:total*=counts[i]
    a=len(controls); U=sum(op[0]==source for op in spec)
    assert sum(size[i] for i in roots)==a
    assert internal>=U-e-len(forks)
    assert total*4**internal<=2**a*3**internal
    return total,internal,e,roots,children,controls

def forest_tests():
    from mixed_profiles import extensions,profile_tables
    from bilateral_check import live_all,transpose
    stats=[0]*5
    def check(spec,rows,c,q):
        for side,rr in [('U',rows),('Q',transpose(rows,q))]:
            t,I,e,roots,ch,ctrl=forest_bound(spec,side)
            a=len(ctrl);u=sum(op[0]==side for op in spec)
            assert len(set(rr))<=t
            if len(set(rr))==2**a:assert u<=e;stats[3]+=1
            # Independently enumerate each pattern of visited values.
            seen={}
            for w,row in enumerate(rr):
                todo=list(roots);pat=[]
                while todo:
                    i=todo.pop()
                    if i in ctrl:
                        v=w>>ctrl[i]&1;pat.append((i,v))
                        if not v:continue
                    todo.extend(ch[i])
                key=tuple(sorted(pat))
                assert key not in seen or seen[key]==row
                seen[key]=row
            assert len(seen)==t
            stats[0]+=1;stats[1]+=len(rr)
            if I:stats[2]+=1
            if e and I:stats[4]+=1
    def rec(cols,c,q,spec):
        if spec and live_all(spec):check(spec,cols[-1],c,q)
        if len(spec)==5:return
        for op,nc,cc,qq in extensions(cols,c,q):rec(nc,cc,qq,spec+(op,))
    rec((),0,0,())
    return stats

if __name__=='__main__':
    print('forest tests',forest_tests())

def toffoli_examples():
    # Nonlinear bijection alpha(p)=p XOR ((p0*p1)<<2); m entries,
    # m+3 query occurrences, independent p bits. All XORs cost 3 ANDs.
    checks=0; counts=[]
    for m in range(3,9):
        ops=[]
        def gate(a,b):ops.append((a,b));return 2*(m+(m+3)+len(ops)-1)
        def xor(a,b):return gate(gate(a,b^1)^1,gate(a^1,b)^1)^1
        # leaves 0..m-1 are p; next m+3 are query occurrences.
        h=[gate(2*i,2*(m+i)) for i in range(m)]
        terms=[gate(h[0],2*(2*m)),gate(h[1],2*(2*m+1)),h[2],gate(gate(h[0],h[1]),2*(2*m+2))]+h[3:]
        out=terms[0]
        for t in terms[1:]:out=xor(out,t)
        assert len(ops)==4*m+4
        def eval_g(p,y):
            ys=[y>>i&1 for i in range(m)]; qs=[ys[0]|ys[2],ys[1]|ys[2]]+ys[2:]+ys[:3]
            vals=[p>>i&1 for i in range(m)]+qs
            def r(l):return vals[l//2]^(l&1)
            for a,b in ops:vals.append(r(a)&r(b))
            return r(out)
        for p in range(1<<m):
            alpha=p^(((p&3)==3)<<2)
            for y in range(1<<m):
                assert eval_g(p,y)==(alpha&y).bit_count()%2;checks+=1
        counts.append((m,len(ops)))
    return checks,counts

if __name__=='__main__':print('nonlinear code circuits',toffoli_examples())

```

---

# Earlier pending research (archive; follow the current priorities at the top)

# Research handoff — bilateral mixing, port slack, and inner product

**Priority:** continue the end-to-end Lean SAT bound (six-bit identity, L037 and external circuit-model translation), then the additive-weight and robust-identifier arguments. This section is a new paper proof about mixed-gate accounting, not a stronger SAT coefficient or a solution to L-clb-036. No native implementation is recommended. Earlier pending proofs and reference implementations follow as an archive. Repository read-only at [0b839bf](https://github.com/Krapples/circuit-synthesis-research/commit/0b839bfe70e66eb700264b0f83c619fafa1f3243); both requested notes reread after the experiments, unchanged (orientation `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`, research `7ba5ee58a5d9b0ee5610c75f184b8d018235694f`). The local XNOR, excess restriction, and composition theorems are Lean-checked; do not duplicate. Recursive additive weights do not require exact circuit minima or Percy UNSAT certificates. No repo writes, independent proof review, or new Lean proof this round.

## 1. Simultaneous mixed-gate slack identity for a partition

AIG AND gates, free constants and complement edges; trim to one output and simplify literal constants. Partition primary inputs into K disjoint nonempty blocks. A wire is pure if its syntactic ancestry lies in one block, mixed if it contains at least two. Assume the output is mixed (otherwise the mixed count is zero and the following connected-cone accounting is unnecessary). Let G be the number of live mixed gates. All successors of a mixed wire are mixed. The mixed DAG is therefore connected toward the output.

For block i define N_i to be the number of distinct residual functions **on all other blocks** as the assignment to block i varies. This direction matters: it is NOT the earlier cofactor count on block i with all other inputs fixed. Put d_i=ceil(log2 N_i). Let p_i be the number of pure-i operand occurrences at mixed gates, b_i the number of distinct underlying pure-i wire IDs among those occurrences (ignore phases), and let e be the number of mixed-to-mixed operand occurrences minus G-1 (nonnegative, count multiplicity). For each i the vector of pure-i wire values determines the entire residual function of the other inputs, since all dependence on i reaching the mixed DAG through pure-i computations enters by these ports. Hence d_i<=b_i<=p_i. Counting the two operand slots of each mixed gate gives `sum p_i = 2G - (G-1+e) = G+1-e`. Thus the exact resource identity is

    G = sum_i d_i - 1 + e + sum_i(p_i-b_i) + sum_i(b_i-d_i).

All three slack terms are nonnegative: reconvergence in the mixed DAG, repeated pure-port occurrences, and excess distinct port bits beyond the minimum information capacity. In particular `G >= sum_i ceil(log2 N_i)-1`. This is simultaneous across every **disjoint partition**. Do not sum this lower bound over overlapping partitions; the same mixed gate can satisfy many tests. Since d_i<=|block_i|, the elementary joint bound alone is at most linear.

For two blocks write E/U/Q/M for entry (one pure operand from each side), source-controlled (one pure-source operand plus mixed predecessor), query-controlled (one pure-query operand plus mixed predecessor), and merge (two mixed operands) counts, as in the preceding handoff. Let a=E+U and b=E+Q be source/query operand occurrences. Then e=M-E+1 and G+1=a+b+e. If the target has N_x and N_y distinct rows and columns, respectively,

    G >= ceil(log2 N_x) + ceil(log2 N_y) - 1.

This improves the one-sided Fibonacci bound on symmetric high-diversity targets. All pure-source and pure-query preprocessing may be arbitrary and free. Relax the two pure operands of each entry, and the pure operand of every U/Q gate, into fresh independent binary ports; pure phases are absorbed into the port values. Actual source/query assignments choose port words (possibly a subset of the full port cube). Original target rows/columns cannot be more numerous than the relaxed ones.

## 2. Equality characterization: disjointness, not arbitrary high diversity

Suppose N_x=2^r, N_y=2^s with r,s>=1 and G=r+s-1. Then a=r, b=s, e=0. Each side's actual port words must exhaust its cube, and the relaxed rows and columns are all distinct. The mixed DAG is a tree (G-1 mixed edges, every nonoutput mixed wire has exactly one mixed reader occurrence). A source-controlled gate cannot have another source-controlled gate on its unique path to output: setting the latter's control absorbing would make the former's port irrelevant under that fixed setting, contradicting distinctness of all rows. Similarly for query-controlled gates. Every U gate has an entry ancestor, which is source-controlled, so U=0; likewise Q=0. Consequently r=s=E and M=E-1.

The remaining tree is a signed AND formula on E independent entry products h_i=p_i q_i. At p=0 all products are zero. Since the rows for the zero and i-th unit source port words differ, the formula is sensitive to every h_i at h=0. At each internal AND, both signed child literals must be 1 at the baseline: otherwise varying at least one child cannot change that gate, so some leaf would not be sensitive. Thus all internal gate-to-gate phases are positive and all leaf phases negative (for E>=2); the formula is the NOR of h_i up to its output phase. E=1 is immediate. The function on the ports is exactly OR_i(p_i q_i) or its complement. For a general original target the source/query code maps need not be one-to-one, but their ranges exhaust the cubes. This is a semantic equality characterization, not just a capacity bound.

## 3. Inner product: normalized bilateral saturation forces exact cost 4m-3

Let IP_m(x,y)=sum_i x_i y_i mod 2 with m>=1 independent bits on each side. All 2^m rows and all 2^m columns are distinct; its columns, as functions on x, form an F2-linear space, containing zero and otherwise only balanced functions. The same holds for rows. We give a stronger theorem in the following **conditional** model: exactly m pure-source operand occurrences and m pure-query operand occurrences at mixed gates (a=b=m), and no constant live mixed wire. In particular any mixed-gate-minimal realization is free of constant mixed gates (otherwise replace it by a free constant), but not every mixed-gate-minimal realization has a=b=m. Do not assert the exact cost for arbitrary circuits with redundant ports.

Both port maps are bijections, since the original source and query each have 2^m assignments and full row/column diversity. In the relaxed skeleton we may express the actual target on port words p,q as `alpha(p) dot beta(q)`, where alpha and beta are the inverse bijections into F2^m. Relabel the entry port pairs as (p_i,q_i), i=1..E; the other ports belong to U/Q gates.

**Entry-pair lemma.** For any entry i, flipping p_i alone cannot affect the output at q_i=0, because p_i occurs only in the entry gate. For each p, the nonzero vector delta=alpha(p) XOR alpha(p XOR e_i) annihilates all beta(q) with q_i=0. That set has exactly 2^(m-1) vectors; it must be the full hyperplane delta^perp, so delta is its unique nonzero normal u_i, independent of p. Therefore `u_i dot beta(q)=q_i` for all q. Symmetrically there is a constant nonzero v_i=beta(q) XOR beta(q XOR e_i), with `alpha(p) dot v_i=p_i`. In particular `u_i dot v_j = [i=j]` by taking an entry flip in the latter identity. Both families are linearly independent. This is stronger than mere injectivity of the port codes.

**No U or Q gate can occur.** Suppose the first U/Q gate is a U with fresh source control p_j, j outside the entry set. Its other signed input F is a Boolean function solely of earlier entry products, because every earlier mixed gate is E or M. Fix p_i=1 at all entries (and fix the remaining source ports other than p_j arbitrarily). If F can be zero, choose entry query bits z with F=0. F stays zero for every q in the fiber q_E=z, so flipping p_j cannot change the circuit output anywhere on this fiber. However delta=alpha(p) XOR alpha(p XOR e_j) is nonzero and has delta dot v_i=0 for all entries i. The beta(q) in the fiber form a full affine coset of W=intersection_i ker(u_i dot -): this follows from bijectivity of beta and the entry lemma. The orthogonal complement of W is span{u_i}, and its intersection with the annihilator of all v_i is zero by the dual pairing. Thus delta is nonzero on W, and the target derivative delta dot beta(q) takes both values on this fiber. Contradiction. If F cannot be zero, the mixed predecessor is constant (since the full independent entry product cube is feasible when all entry source controls are 1); this would be a constant live mixed wire in the original circuit, excluded by the hypothesis. A first Q is ruled out by the symmetric proof. Hence U=Q=0, E=m, and u_i,v_i are dual bases. It follows that the relaxed target is exactly XOR_i(p_i q_i).

Fix p_i=1 at every entry, leaving independent q_i as the entry gate outputs. The M-gate tail must compute parity on these m inputs. Parity has AIG AND cost exactly 3(m-1), with free complements. For completeness, the lower bound follows by induction on m in a minimum trimmed AIG. Every input must have at least two distinct reader gates: if only one reader, its other input is independent of that primary, and setting it to its controlling value destroys essentiality under some restriction, incompatible with parity. Degenerate constant/alias gates are absent from a minimum. Choose a first gate h on two distinct primaries, one of them x. Fix x to the absorbing value for h. If x has >=3 readers, >=3 gates disappear. If exactly two readers h,k and h has a successor distinct from k, then h,k and that successor disappear. In the remaining case h has only k as successor and k reads x and h. Since k is canalizing in x, the two-gate subcircuit computes a function of the two primaries realizable by at most one AND with free phases/constants: on k's absorbing x value it is constant, and on the other it is a literal or constant. This contradicts minimality. The output cannot be h while a live reader k exists. In all remaining minimum cases a restriction leaves parity (up to phase) on m-1 inputs and eliminates at least three gates. Base m=1 costs zero. Three ANDs per XOR attain the bound.

We conclude `G >= m + 3(m-1) = 4m-3` under normalized bilateral saturation. This is attained by m pair products followed by a parity tree (or chain). Hence the exact minimum **in this conditional class** is 4m-3. In contrast, the disjointness-style OR of m pair products has identical row and column cardinalities but needs exactly 2m-1 mixed gates. This separates actual Boolean semantics from capacity even when preprocessing on both sides is free.

## 4. Unconditional inner-product consequence: G >= 2m+1 for m>=2

First, rule out *any mixed tree with one saturated side* for IP_m (allow redundancy on the other side). Suppose a=m. Saturation of source ports excludes U gates in a tree by the unique-path argument of Section 2, so E=m. Starting at output, strip the root chain of Q gates to the first M gate (there must be one for m>=2). Its two child trees contain disjoint nonempty source port sets A,B, together all m source port bits. For each fixed actual query, every Q gate on the stripped chain must be neutral if the column is nonconstant, so the root M is observed with one fixed phase for all nonconstant columns. Since the source port map is bijective, any nonzero column of IP is balanced over the full source port cube. Depending on the root phase, its ones or zeros set is the rectangle `S_A times S_B`. Its size is exactly 2^(m-1). The two positive factors |S_A| and |S_B| are therefore powers of two, bounded by 2^|A| and 2^|B|; at least one attains its full cube size. Thus each nonzero column depends solely on A or solely on B. But all rows are distinct, so there is a nonconstant column of each kind, and their XOR depends on both A and B. Closure of the IP columns under XOR contradicts the rectangle property. The symmetric proof rules out a mixed tree when b=m.

Now suppose a circuit for IP_m has G<=2m. Choose a mixed-gate-minimal realization with arbitrary pure-side logic free. It has no constant mixed wire, since replacement by a constant and trimming cannot increase any mixed-gate count. We have a,b>=m, e>=0 and G+1=a+b+e. If e=0 then at least one of a,b equals m, and the tree case just ruled this out. If e>=1 then a=b=m, e=1 and normalized bilateral saturation gives G>=4m-3>2m for m>=2, also impossible. Thus

    2m+1 <= C_mix(IP_m) <= 4m-3   (m>=2).

At m=2 this is exact (five). At m=1 the minimum is one. For m>=3 we do not claim the unconditional minimum. More precisely the slack identity says that any circuit beating 4m-3, after removal of constant mixed wires, must have a redundant pure-port occurrence budget on at least one side; if either side is saturated, the mixed DAG must also reconverge. This is a first semantic obstruction to using the same mixed resources as disjointness. It does not prove that redundant encodings are expensive enough to yield a superlinear bound.

## 5. Executed verification, limits, and next step

The following script imports `mixed_profiles.py` from the preceding section (extract the code block there); run `python bilateral_check.py` in the same directory. Python 3 stdlib, no SAT solver. All assertions passed:

- Enumerated 68,321 ordered relaxed descriptions of 1..5 gates, including 13,001 fully live descriptions. For the latter, joint capacities, port/edge identities, and saturation implications checked. 148 bilateral saturation cases; 6 equality cases all OR-of-products up to output phase; 5 normalized saturated IP-equivalent cases. Independently searched all distinct row/column submatrices for IP_2 up to separate permutations and output phase (arbitrary pure preprocessing): zero hits below five gates, 12 descriptions at five gates. Row/column test uses the zero row/column and complement-of-permutation 3x3 submatrix pattern.
- 3,000 random actual AIGs with 2,074 live mixed cones; actual bilateral counts all obey the new bound. For 2,073 small cones (<=8 mixed gates), relaxed counts also checked. There were 635 bilateral saturation cases, 633 tight cases and 621 normalized IP-equivalent cases (mostly single entry gates). No inference of frequency in larger synthesized circuits.
- 90,048 dual-basis entry identity tests and 320,832 nonentry fiber tests for dimensions 2..7, with random invertible bases and independently permuted nonentry coordinates. These test the linear-algebra premises, not a search over all circuits of arbitrary size.
- 87,380 direct truth evaluations of explicit m=1..8 IP constructions, all matching the formula and 4m-3 gate count.
- 3,000 random circuits partitioned into 2..5 blocks; 2,671 live mixed cones, 9,377 actual block profile checks, and the exact nonnegative slack identity for every cone. 1,158 tight cases; reconvergence in 374, repeated pure ports in 1,153, excess distinct ports in 1,084 (overlap allowed). Not a native benchmark.

**Research implication:** this result is about unrestricted mixed AIGs (not restricted monotone circuits), but the exact stronger IP cost needs saturation and absence of constant live mixed wires. The unconditional bound is still linear, and IP has an explicit linear-size AIG. No new SAT lower-bound coefficient, no solution to L-clb-036. No novelty claim; related communication-complexity literature includes Roychowdhury et al., *Lower Bounds on Threshold and Related Circuits via Communication Complexity*, https://docs.lib.purdue.edu/ecetr/306/ (different circuit models; we do not transfer their bounds). The next useful step is to replace the full-cube bijection arguments by constraints on dense subsets of the port cube (a=m+r, b=m+s) and count the cost of redundancy jointly with reconvergence. The multi-block identity can be used as a diagnostic, but overlapping partitions cannot be charged additively without a further theorem. Retain the list-disjointness sorting-network negative control and do not activate the optional topology filters in native synthesis.

### Reference implementation (`bilateral_check.py`)

```python
"""Tests for bilateral mixed-gate bounds. Run beside mixed_profiles.py (previous handoff)."""
from itertools import combinations
from random import Random
from collections import Counter
from mixed_profiles import extensions, profile_tables, reset_counts, extract


def live_all(spec):
    live=set(); todo=[len(spec)-1]
    while todo:
        i=todo.pop()
        if i in live: continue
        live.add(i); op=spec[i]
        if op[0] in ('U','Q'): todo.append(op[1])
        elif op[0]=='M': todo.extend((op[1],op[3]))
    return len(live)==len(spec)


def transpose(rows,q):
    return tuple(sum(((v>>j)&1)<<i for i,v in enumerate(rows)) for j in range(1<<q))


def ip_equivalent(rows,q):
    # With both alphabets saturated and of same width: the rows are a vector
    # space over F2 and all evaluations (columns) are distinct functionals.
    rs=set(rows)
    return len(rs)==len(rows)==1<<q and 0 in rs and len(set(transpose(rows,q)))==1<<q and all(a^b in rs for a in rs for b in rs)


def ip2_submatrix(rows,q):
    # Arbitrary pure preprocessing selects four distinct rows/columns, and
    # either output phase is allowed. A 2-bit IP table up to permutations:
    # one zero row and column, and 3x3 block with two ones per row/column.
    rs=list(set(rows)); mask=(1<<(1<<q))-1
    if len(rs)<4 or q<2:return False
    for phase in (0,mask):
        vals=[v^phase for v in rs]
        for zero in vals:
            care=mask^zero
            if care.bit_count()<4:continue
            others=list(set(v&care for v in vals)-{0})
            if len(others)<3:continue
            for a,b,c in combinations(others,3):
                if (care&~(a|b|c) and a&b&~c and a&c&~b and b&c&~a):return True
    return False


def check_matrix(spec,rows,c,q,stats,small=False):
    G=len(spec); counts=Counter(op[0] for op in spec); E,U,Q,M=(counts[t] for t in 'EUQM')
    assert c==E+U and q==E+Q and M>=E-1
    assert c+q==G+1-(M-E+1)
    nr=len(set(rows)); nc=len(set(transpose(rows,q)))
    lx=(nr-1).bit_length(); ly=(nc-1).bit_length()
    assert lx<=c and ly<=q and lx+ly<=G+1
    stats['live']+=1
    if nr==1<<c and nc==1<<q:
        stats['bilateral_saturated']+=1
        if M==E-1:
            assert U==Q==0 and c==q==E
            # In port order each entry uses the next source and query bit.
            want=tuple(sum(bool(a&b)<<b for b in range(1<<q)) for a in range(1<<c))
            mask=(1<<(1<<q))-1
            assert rows==want or rows==tuple(v^mask for v in want)
            stats['tight']+=1
        if c==q and (ip_equivalent(rows,q) or ip_equivalent(tuple(v^((1<<(1<<q))-1) for v in rows),q)):
            # Nonconstant intermediate gates; checking this condition on the
            # relaxed circuit suffices for this finite sample.
            if all(len(set(r))>1 or len(set(transpose(r,qq)))>1 for i in range(1,G+1) for r,cc,qq in [profile_tables(spec[:i])]):
                assert U==Q==0 and G>=4*c-3
                stats['ip_saturated']+=1
    if small and G<=5:
        if nr>=4 and nc>=4 and ip2_submatrix(rows,q):
            assert G>=5
            stats['ip2_'+str(G)]+=1


def exhaustive():
    stats=Counter(); counts=Counter()
    def rec(cols,c,q,spec):
        g=len(spec)
        if g:
            counts[g]+=1
            if live_all(spec):check_matrix(spec,cols[-1],c,q,stats,small=True)
        if g==5:return
        for op,nc,cc,qq in extensions(cols,c,q):rec(nc,cc,qq,spec+(op,))
    rec((),0,0,())
    assert list(counts.values())==[1,5,65,1625,66625]
    assert stats['ip2_5']>0
    print('enumeration',dict(counts),'live tests',dict(stats))


def raw_random(seed=261127):
    R=Random(seed); stats=Counter()
    for _ in range(3000):
        n=R.randrange(4,9);G=R.randrange(2,13); A=R.randrange(1,(1<<n)-1);B=((1<<n)-1)^A
        gates=[]; mask=(1<<(1<<n))-1
        vals=[sum((r>>i&1)<<r for r in range(1<<n)) for i in range(n)]
        for j in range(G):
            a,b=R.sample(range(n+j),2);a=2*a+R.randrange(2);b=2*b+R.randrange(2);gates.append((a,b));vals.append((vals[a//2]^(mask if a&1 else 0))&(vals[b//2]^(mask if b&1 else 0)))
        out=2*(n+G-1)+R.randrange(2); f=vals[out//2]^(mask if out&1 else 0)
        def subs(m):return [a for a in range(1<<n) if a&m==a]
        aa,bb=subs(A),subs(B)
        rows=tuple(sum((f>>(a|b)&1)<<j for j,b in enumerate(bb)) for a in aa)
        cols=tuple(sum((f>>(a|b)&1)<<j for j,a in enumerate(aa)) for b in bb)
        nr,nc=len(set(rows)),len(set(cols));spec=extract(n,gates,out,A)
        if not spec:continue
        c=sum(op[0] in ('E','U') for op in spec);q=sum(op[0] in ('E','Q') for op in spec)
        assert nr<=1<<c and nc<=1<<q and (nr-1).bit_length()+(nc-1).bit_length()<=len(spec)+1
        stats['actual']+=1
        if len(spec)<=8:
            r,cc,qq=profile_tables(spec); assert (c,q)==(cc,qq)
            check_matrix(spec,r,c,q,stats)
    print('random',dict(stats))


def dot(a,b):return (a&b).bit_count()&1

def combine(basis,mask):
    r=0
    for i,b in enumerate(basis):
        if mask>>i&1:r^=b
    return r


def fiber_checks(seed=261128):
    R=Random(seed); checks=Counter()
    for m in range(2,8):
        for e in range(1,m+1):
            for _ in range(8):
                u=[1<<i for i in range(m)]
                for _ in range(20):
                    i,j=R.sample(range(m),2);u[i]^=u[j]
                v=[next(a for a in range(1<<m) if all(dot(b,a)==int(i==j) for j,b in enumerate(u))) for i in range(m)]
                h=(1<<e)-1; pa=list(range(1<<(m-e)));pb=pa.copy();R.shuffle(pa);R.shuffle(pb)
                alpha=[combine(u,(a&h)|(pa[a>>e]<<e)) for a in range(1<<m)]
                beta=[combine(v,(b&h)|(pb[b>>e]<<e)) for b in range(1<<m)]
                assert len(set(alpha))==len(set(beta))==1<<m
                for i in range(e):
                    for a in range(1<<m):
                        assert alpha[a]^alpha[a^(1<<i)]==u[i] and dot(alpha[a],v[i])==a>>i&1
                        assert beta[a]^beta[a^(1<<i)]==v[i] and dot(beta[a],u[i])==a>>i&1
                        checks['entry']+=2
                for i in range(e,m):
                    for a in range(1<<m):
                        d=alpha[a]^alpha[a^(1<<i)]
                        assert d and all(dot(d,w)==0 for w in v[:e])
                        for z in range(1<<e):
                            assert {dot(d,beta[b]) for b in range(z,1<<m,1<<e)}=={0,1}
                            checks['fiber']+=1
    print('dual-basis / fiber checks',dict(checks))


def ip_construction(m):
    spec=[('E',)]*m; out=0; phase=0
    for i in range(1,m):
        # XOR of literal on out with entry i: (a & !b) | (!a & b)
        spec.append(('M',out,phase,i,1)); a=len(spec)-1
        spec.append(('M',out,phase^1,i,0)); b=len(spec)-1
        spec.append(('M',a,1,b,1));out=len(spec)-1;phase=1
    return spec,phase


def constructions():
    checks=0
    for m in range(1,9):
        spec,p=ip_construction(m);rows,c,q=profile_tables(spec);mask=(1<<(1<<q))-1
        assert c==q==m and len(spec)==4*m-3
        for a,row in enumerate(rows):
            assert row^(mask if p else 0)==sum(dot(a,b)<<b for b in range(1<<m));checks+=1<<m
    print('IP construction truth evaluations',checks)

def multiblock(seed=261129):
    R=Random(seed);stats=Counter()
    for _ in range(3000):
        n=R.randrange(4,10);k=R.randrange(2,min(n,5)+1);ng=R.randrange(2,17)
        assignment=list(range(k))+[R.randrange(k) for i in range(n-k)];R.shuffle(assignment)
        sup=[1<<a for a in assignment];gates=[];mask=(1<<(1<<n))-1
        vals=[sum((r>>i&1)<<r for r in range(1<<n)) for i in range(n)]
        for j in range(ng):
            a,b=R.sample(range(n+j),2);a=2*a+R.randrange(2);b=2*b+R.randrange(2)
            gates.append((a,b));sup.append(sup[a//2]|sup[b//2]);vals.append((vals[a//2]^(mask if a&1 else 0))&(vals[b//2]^(mask if b&1 else 0)))
        live=set();todo=[n+ng-1]
        while todo:
            v=todo.pop()
            if v in live:continue
            live.add(v)
            if v>=n:todo.extend(l//2 for l in gates[v-n])
        mixed={v for v in live if sup[v].bit_count()>1};G=len(mixed)
        if not G:continue
        p=[0]*k;distinct=[set() for _ in range(k)];edges=0
        for v in mixed:
            for l in gates[v-n]:
                u=l//2
                if u in mixed:edges+=1
                else:
                    i=sup[u].bit_length()-1;p[i]+=1;distinct[i].add(u)
        b=[len(x) for x in distinct];e=edges-G+1;assert e>=0
        f=vals[-1];D=[]
        for i in range(k):
            A=sum(1<<j for j in range(n) if assignment[j]==i);B=((1<<n)-1)^A
            aa=[x for x in range(1<<n) if x&A==x];bb=[x for x in range(1<<n) if x&B==x]
            N=len({sum((f>>(a|z)&1)<<j for j,z in enumerate(bb)) for a in aa})
            D.append((N-1).bit_length());stats['block']+=1
        assert all(d<=x<=y for d,x,y in zip(D,b,p))
        assert G==sum(D)-1+e+sum(y-x for x,y in zip(b,p))+sum(x-d for x,d in zip(b,D))
        stats['circuit']+=1;stats['tight']+=G==sum(D)-1
        stats['reconvergence']+=bool(e);stats['repeated_port']+=sum(p)>sum(b);stats['redundancy']+=sum(b)>sum(D)
    print('multi-block',dict(stats))

if __name__=='__main__':
    exhaustive();raw_random();fiber_checks();constructions();multiblock()

```

---

# Earlier pending research (historical handoffs)

# Research handoff — mixed-gate accounting and early-mixing capacity

**Priority:** continue the end-to-end Lean SAT theorem first. This new paper theorem counts gates that mix two input blocks, even when all computations entirely on either side are free. It addresses the raw-input bypass loophole in the previous interface theorem, but only gives a linear bound per partition. It is not a solution to L-clb-036 or an improved SAT coefficient. Keep it as a structural proof/audit, not a default native optimization. The earlier pending material is preserved below; its repository snapshots are historical.

Both `sat-search/NOTES_ORIENTATION_QUOTIENT.md` and `RESEARCH_NOTES.md` were reread after the experiments, at [0b839bf](https://github.com/Krapples/circuit-synthesis-research/commit/0b839bfe70e66eb700264b0f83c619fafa1f3243), unchanged (blob SHAs `7f8d2056a2bbb016007db86fa4d59c374b30ebc2`, `7ba5ee58a5d9b0ee5610c75f184b8d018235694f`). The XNOR, excess restriction, and combining lemmas are already Lean-checked in the local model; do not duplicate them. Next formalize the six-bit encoding identity and external circuit translation, using L037 on multiples of six before handling other lengths. The additive weights are recursive truth-table weights, not exact circuit minima; no Percy UNSAT certificate is required for computing them. No repository changes or new Lean verification here.

## 1. Unconditional mixed-gate capacity theorem

Split primary inputs into source x and query y. Work with a trimmed single-output AIG, complemented edges and constants free. A gate is mixed if its syntactic ancestor inputs include both x and y. Let G be the number of mixed gates, and N the number of distinct Boolean functions of y obtained as x varies. Pure-source and pure-query gates are **not charged**. In particular the theorem holds with arbitrary Boolean functions available free on either side. If the output is pure, N<=2.

Relax the circuit by replacing every pure-source operand occurrence at a mixed gate by a fresh independent control bit, and every pure-query operand occurrence by a fresh independent query bit. The signed values of the original pure wires define a simultaneous setting of those independent ports for each x or y. Thus the number of profiles in the original function is no greater than the number in the relaxed circuit: identifying/restricting query columns can merge profiles but cannot create new ones, and the original source assignments use only some of the independent control settings. Literal constants can be simplified first or treated as restricted pure ports. The relaxation preserves the number of mixed gates. A gate may be an entry (E: one pure operand from each side), a source-controlled gate (U: one pure source and one mixed operand), a query-controlled gate (Q: one pure query and one mixed operand), or a binary mixed merge (M: two mixed operands). Pure literal phases can be absorbed into the independent port assignments. Internal phases are retained.

**Theorem:** for G>=1, N<=F_(G+2), where F_0=0, F_1=1 are Fibonacci numbers. In particular

    G >= log_phi(N) - O(1) = 1.44042009... * log2(N) - O(1),

where phi=(1+sqrt(5))/2. The same bound holds for distinct source residuals when varying y, by symmetry, so take the maximum of the two bounds, not their sum.

Proof: at G=1, an entry gate offers at most two query profiles. At G=2, after trimming the first entry feeds the output gate; the second gate is U or Q (or a degenerate repeated operand). A unary controlled gate adds at most one constant profile, a fixed query operand cannot increase the number, so N<=3. For G>=3 choose an earliest mixed gate, necessarily an entry with one pure-source and one pure-query operand. Use the relaxed independent source bit at that gate. Setting it neutral replaces the gate by its pure-query literal, leaving at most G-1 mixed gates. Setting it absorbing replaces the gate by a constant and eliminates at least one more mixed gate: it has a live successor, necessarily mixed, which is now a constant or alias. Simplify both restrictions and reclassify any now-pure wires. Every original profile lies in the union of the two restricted profile families, so N<=F_(G+1)+F_G. If a restricted output becomes pure, it has at most two profiles, covered by the inductive bound (both remaining budgets >=1). For circuits of at most G gates the same result holds by monotonicity. No independence of actual pure-side signals, restriction preservation of essential inputs, or exact synthesis minimum is assumed.

The previous boundary/merge inequality implies about 1.31546 log2 N mixed gates when applied to the relaxed mixed-only skeleton; the new universal coefficient is 1.44042. Both can be useful on a specified topology. This is a lower bound on mixed gates, **not** just on total gates; pure-gate lower bounds can be added when independently established for those disjoint gate categories.

## 2. Exact saturation theorem and a redundancy-sensitive test

Let U be the number of mixed gates with a pure-source operand (E or U), each with its own independent control in the relaxation. Let M=G-U. Thus N<=2^U. Call a controlled gate terminal if it reaches the output by a path with no other controlled gate. Let T be the number of terminal controlled gates. By traversing backwards from the output and stopping at controlled gates, the truncated graph has T controlled leaves and at most M noncontrolled gates, so T<=M+1 (edge count on the connected DAG, noncontrolled fan-in at most two).

If all T terminal controls are absorbing, the output profile is independent of the other U-T controls. All 2^(U-T) settings in this subcube collapse to one profile. Consequently

    N <= 2^U - 2^(U-T) + 1.

In particular, if N=2^U then T=U and

    G >= 2U-1.

For a selector with m independent data bits and one selected query per bit, N>=2^m. If exactly m source-controlled mixed gates are used (no redundant controls), G>=2m-1. This is unconditional for every such circuit and permits arbitrary free pure-source/query preprocessing and arbitrary mixed fanout. An OR of m gated data bits attains 2m-1 using one-hot pure-query signals. With more controls the exact saturation conclusion need not hold.

A finer topology test: for any independent control setting a, traverse backwards from the output; stop at every absorbing controlled gate; record only active (neutral) controls that are reached. Change all unreached controls to absorbing. This cannot change the output profile: all paths from unreached gates already hit an absorbing gate, and the reached subgraph and its values remain unchanged. Therefore the canonical active-set map c(a) satisfies c(c(a))=c(a), and

    N <= |{c(a): a in {0,1}^U}| <= 2^U-2^(U-T)+1.

This is an upper bound on achievable profiles, not an exact semantic count; different canonical settings can still yield identical Boolean functions. Enumerating settings is exponential in U; use only a small cap. It captures simultaneous blocking by multiple controls, not just unary-chain dominance. In a small relaxed skeleton, one can additionally enumerate the actual row truth tables on all independent query ports to get the exact relaxed capacity (still only an upper bound for the original circuit). This is a necessary condition, not a sufficient condition for a target profile matrix or SAT topology.

## 3. Finite mixed-gate maxima and exact small selectors

The reference enumerates all ordered relaxed skeletons with at most six mixed gates, using E/U/Q/M and both old-wire phases. Pure port occurrences are fresh and their phases are absorbed into assignments. A merge of a wire with itself or its complement simplifies to an alias/constant, so need not be enumerated for the maximum at a given budget; this does not lose a circuit with at most that many mixed gates. Unused gates are allowed (only broaden the enumeration); every trimmed acyclic skeleton admits a topological order. All counts below are computed, not solver verdicts. The attained maxima for budgets 1..6 are:

| G | Ordered descriptions at G | Maximum N over relaxed skeletons at most G |
|---:|---:|---:|
| 1 | 1 | 2 |
| 2 | 5 | 3 |
| 3 | 65 | 4 |
| 4 | 1,625 | 5 |
| 5 | 66,625 | 8 |
| 6 | 4,064,125 | 9 |

Use B(0..6)=(2,2,3,4,5,8,9), then B(g)=B(g-1)+B(g-2) for g>=7, by the same proof. E.g. B(7)=17 and B(8)=26. A selector with m=2,3,4,5 data bits must have 2^m profiles, hence needs at least 3,5,7,9 mixed gates respectively, matching the one-hot construction. These exact small minima are finite-enumeration results, not formally checked certificates. For m>=6 the finite recurrence is just a lower bound and we do not claim exact mixed-gate additivity or a general 2m-1 mixed bound without saturation.

For context, the *total data-bearing* gate lower bound of 2m-1 for selectors is elementary, even allowing query-only logic free: no output gate can read a raw data bit, since fixing that bit to its controlling value would make the output constant even on a query selecting another bit. Set a data bit to absorb one of its live readers; that gate and a distinct successor disappear, and the other m-1 data bits are still selectable. Iterate down to two data bits (which need at least three mixed gates by the small bound above). This does not establish the same bound on mixed gates alone, because deleted gates may be pure-source gates. The distinction between mixed and total cost is the point of the new accounting.

## 4. Executed tests and limits

Run the embedded `mixed_profiles.py` (Python 3 standard library). It exhaustively evaluated 4,132,446 ordered descriptions through six gates. On 5,000 seeded random AIGs (4..9 primary inputs, 2..18 raw gates, random nonempty splits), 3,715 had live mixed gates; all actual residual counts satisfy the new bounds. On the 3,122 cases with N>1, Fibonacci alone improves the old mixed-skeleton boundary/merge bound clipped by source control count and trivial assignment/function counts in 27 cases; the exact-small-base recurrence gives 143 additional improvements over min(old,Fibonacci); canonical reset counting improves min(old,exact-base recurrence) in 359 cases. These are upper bounds on residual diversity of specified circuits, not solver exclusions or runtime speedups. 3,637 relaxed skeleton counts (G<=7) were also computed exactly and the canonical representative replay checked row equality for all control settings. 300 were independently checked by direct Boolean assignment evaluation. 1,517 saturated examples satisfy the 2U-1 constraint. 8,192 selected-output evaluations across one-hot selector constructions on 2..9 bits pass. No assertion failures. Finite tests support the arguments; no Lean proof or independent review yet.

**Limit for L-clb-036:** any single source/query split has log2 N<=|x|, so even a perfect capacity-to-gate coefficient of two would still be linear. Summing these demands over overlapping partitions is not justified: one broadly mixed gate may pay for many of them. The new theorem makes the price of early mixing explicit but does not prove a superlinear price. Next investigate whether the *same* mixed gates can realize joint target profile matrices for several partitions, rather than merely achieving adequate capacity in each. Keep the sorting-network and superconcentrator negative controls from earlier work. No novelty claim, no new SAT lower-bound coefficient, no external submission.

### Reference implementation

```python
from random import Random

# Each independent control assignment indexes a row of a truth table on q.
# Separate pure-source/query input occurrence for every port is a relaxation.
# Represent every existing wire as tuple of rows; fresh leaves expand the cube.
def extensions(cols,c,q):
    mask=(1<<(1<<q))-1
    expanded=tuple(tuple(x|(x<<(1<<q)) for x in col)*2 for col in cols)
    yield ('E',), expanded+((0,)*(1<<c)+(mask<<(1<<q),)*(1<<c),),c+1,q+1
    # One fresh control or one fresh query; the old literal phase is material.
    for i,col in enumerate(cols):
        for p in (0,1):
            vals=tuple(x^(mask if p else 0) for x in col)
            yield ('U',i,p),tuple(col*2 for col in cols)+((0,)*(1<<c)+vals,),c+1,q
            yield ('Q',i,p),tuple(tuple(x|(x<<(1<<q)) for x in col) for col in cols)+(tuple(x<<(1<<q) for x in vals),),c,q+1
        for j in range(i):
            for p in (0,1):
                for s in (0,1):
                    v=tuple((x^(mask if p else 0))&(y^(mask if s else 0)) for x,y in zip(col,cols[j]))
                    yield ('M',i,p,j,s),cols+(v,),c,q

def fib(n):
    a,b=0,1
    for _ in range(n):a,b=b,a+b
    return a

def enumerate_small(maxg=5):
    best=[0]*(maxg+1);counts=[0]*(maxg+1);witness=[None]*(maxg+1)
    def rec(cols,c,q,spec):
        g=len(cols)
        if g:
            counts[g]+=1; N=len(set(cols[-1]))
            if N>best[g]:best[g]=N;witness[g]=spec
            assert N<=fib(g+2),(spec,N)
        if g==maxg:return
        for op,nc,cc,qq in extensions(cols,c,q):rec(nc,cc,qq,spec+(op,))
    rec((),0,0,())
    return counts,best,witness


def budget_bound(g):
    # At most g mixed gates, including pure output case.
    B=[2,2,3,4,5,8,9]
    while len(B)<=g:B.append(B[-1]+B[-2])
    return B[g]

def extract(n,gates,out,A):
    # Literal 2*v+phase, primaries 0..n-1; no special constants.
    support=[1<<i for i in range(n)]; B=((1<<n)-1)^A
    for a,b in gates:support.append(support[a//2]|support[b//2])
    live=set();todo=[out//2]
    while todo:
        v=todo.pop()
        if v in live:continue
        live.add(v)
        if v>=n:todo.extend(l//2 for l in gates[v-n])
    mix=lambda v:bool(support[v]&A and support[v]&B)
    ids={}; spec=[]
    for v in sorted(live):
        if not mix(v):continue
        a,b=gates[v-n]; i,j=a//2,b//2
        if mix(i) and mix(j):
            op=('M',ids[i],a&1,ids[j],b&1)
        elif mix(i) or mix(j):
            if mix(j):a,b=b,a;i,j=j,i
            op=('U' if support[j]&A else 'Q',ids[i],a&1)
        else:op=('E',)
        ids[v]=len(spec);spec.append(op)
    return spec

def profile_tables(spec):
    cols=();c=q=0
    for op in spec:
        t=op[0]; mask=(1<<(1<<q))-1
        if t=='E':
            cols=tuple(tuple(x|(x<<(1<<q)) for x in col)*2 for col in cols)+((0,)*(1<<c)+(mask<<(1<<q),)*(1<<c),);c+=1;q+=1
        elif t in ('U','Q'):
            _,i,p=op;vals=tuple(x^(mask if p else 0) for x in cols[i])
            if t=='U':cols=tuple(col*2 for col in cols)+((0,)*(1<<c)+vals,);c+=1
            else:cols=tuple(tuple(x|(x<<(1<<q)) for x in col) for col in cols)+(tuple(x<<(1<<q) for x in vals),);q+=1
        else:
            _,i,p,j,s=op
            cols+= (tuple((x^(mask if p else 0))&(y^(mask if s else 0)) for x,y in zip(cols[i],cols[j])),)
    return cols[-1],c,q

def direct_profiles(spec):
    C=sum(op[0] in ('E','U') for op in spec);Q=sum(op[0] in ('E','Q') for op in spec)
    rows=[]
    for a in range(1<<C):
        row=0
        for b in range(1<<Q):
            c=q=0; vals=[]
            for op in spec:
                t=op[0]
                if t=='E':v=(a>>c&1)&(b>>q&1);c+=1;q+=1
                elif t=='U':v=(vals[op[1]]^op[2])&(a>>c&1);c+=1
                elif t=='Q':v=(vals[op[1]]^op[2])&(b>>q&1);q+=1
                else:v=(vals[op[1]]^op[2])&(vals[op[3]]^op[4])
                vals.append(v)
            row|=vals[-1]<<b
        rows.append(row)
    return tuple(rows)

def reset_counts(spec):
    # Terminal controls: those reachable backwards without crossing a control.
    C={i:j for j,i in enumerate(i for i,op in enumerate(spec) if op[0] in ('E','U'))}
    def walk(a):
        todo=[len(spec)-1];seen=set();active=0;visited=0
        while todo:
            i=todo.pop()
            if i in seen:continue
            seen.add(i);op=spec[i]
            if i in C:
                bit=1<<C[i];visited|=bit
                if not a&bit:continue
                active|=bit
            if op[0] in ('U','Q'):todo.append(op[1])
            elif op[0]=='M':todo.extend((op[1],op[3]))
        return active,visited
    T=walk(0)[1].bit_count(); U=len(C); G=len(spec)
    assert T<=G-U+1
    images={walk(a)[0] for a in range(1<<U)}
    assert all(walk(a)[0]==a for a in images)
    return len(images),T,tuple(walk(a)[0] for a in range(1<<U))

def test(seed=261126):
    R=Random(seed); stats={'live':0,'nontrivial':0,'fib_improves':0,'small_improves':0,'reset_improves':0,'relaxed':0,'canonical_replay':0,'independent':0,'saturated':0,'tight':0}
    for _ in range(5000):
        n=R.randrange(4,10);g=R.randrange(2,19)
        A=R.randrange(1,(1<<n)-1);B=((1<<n)-1)^A
        gates=[];mask=(1<<(1<<n))-1
        vals=[sum(((r>>i)&1)<<r for r in range(1<<n)) for i in range(n)]
        for j in range(g):
            a,b=R.sample(range(n+j),2);a=2*a+R.randrange(2);b=2*b+R.randrange(2);gates.append((a,b));vals.append((vals[a//2]^(mask if a&1 else 0))&(vals[b//2]^(mask if b&1 else 0)))
        out=2*(n+g-1)+R.randrange(2); f=vals[out//2]^(mask if out&1 else 0)
        def subs(m):
            a=m
            while True:
                yield a
                if not a:break
                a=(a-1)&m
        N=len({sum(((f>>(a|b))&1)<<j for j,b in enumerate(subs(B))) for a in subs(A)})
        spec=extract(n,gates,out,A);G=len(spec)
        if not G:assert N<=2;continue
        U=sum(op[0] in ('E','U') for op in spec);M=G-U
        assert N<=min(1<<U,budget_bound(G));stats['live']+=1
        if N>1:stats['nontrivial']+=1
        base=min(1<<U,3**(2*M+1),1<<A.bit_count(),1<<(1<<B.bit_count()))
        if N>1 and fib(G+2)<base:stats['fib_improves']+=1
        if N>1 and budget_bound(G)<min(base,fib(G+2)):stats['small_improves']+=1
        if N==(1<<U):assert G>=2*U-1;stats['saturated']+=1
        if U<=12:
            canon,T,rep=reset_counts(spec);stats['canonical_replay']+=1
            assert N<=canon<= (1<<U)-(1<<(U-T))+1
            if N>1 and canon<min(base,budget_bound(G)):stats['reset_improves']+=1
            if G<=7:
                rows,c,q=profile_tables(spec);K=len(set(rows));stats['relaxed']+=1
                assert N<=K<=min(canon,budget_bound(G))
                assert all(rows[a]==rows[b] for a,b in enumerate(rep))
                if K==budget_bound(G):stats['tight']+=1
                if stats['independent']<300:
                    assert rows==direct_profiles(spec);stats['independent']+=1
    print(stats)

# Exact selector construction: independent data controls, free one-hot query functions.
def selector_checks():
    checks=0
    for k in range(2,10):
        spec=[('E',)]*k;o=0
        for i in range(1,k):spec.append(('M',o,1,i,1) if i==1 else ('M',o,0,i,1));o=len(spec)-1
        # Output complemented: OR of entry outputs. Each query unit vector selects its data bit.
        rows,c,q=profile_tables(spec);assert c==q==k and len(set(rows))==1<<k
        for a,row in enumerate(rows):
            for i in range(k):assert ((row>>(1<<i))&1)^1==((a>>i)&1);checks+=1
        C,T,_=reset_counts(spec);assert C==1<<k and T==k
    print('selector evaluations',checks)

if __name__=='__main__':
    counts,best,witness=enumerate_small(6)
    assert counts==[0,1,5,65,1625,66625,4064125]
    assert best==[0,2,3,4,5,8,9]
    print('enumeration',counts,best)
    test();selector_checks()

```

---

# Research handoff — mandatory query interfaces and forced Boolean derivatives

**Priority for the agent:** finish the SAT encoding/model-transfer proof before integrating optional topology filters. This update proves a new necessary semantic condition for *every* AIG with a source/query partition, gives a strict separation from the earlier support and subset-capacity tests, and gives an exact reduced oracle for the resulting relaxed interface problem. It does not establish a superlinear unrestricted SAT lower bound or L-clb-036. Earlier pending research is retained below; the historical snapshots are not current status reports.

Repository checked read-only at [0b839bf](https://github.com/Krapples/circuit-synthesis-research/commit/0b839bfe70e66eb700264b0f83c619fafa1f3243). Both requested notes were read: orientation unchanged (`7f8d2056a2bbb016007db86fa4d59c374b30ebc2`); `RESEARCH_NOTES.md` changed (`7ba5ee58a5d9b0ee5610c75f184b8d018235694f`). The repo reports successful Lean checks of `xnorConj_lower`, `excess_restriction` (essential fixed inputs, nonconstant restriction), and `xnorConj_restriction_lower`. The last theorem gives `C(f) >= |F| + 4q - 1` when restriction of essential inputs F leaves q independent XNORs. These pieces are DONE; do not reimplement. Still pending: string identity, even-n support, tails, external counted-basis transfer, additive-weight theorem and mixed-block chain. The new work below is mathematical plus Python verification, not new Lean theorems. No repository writes.

**Clarification to the latest SAT proof notes:** the reviewed recursive `weight` in `sat-search/experiments/additive_sat_weight.py` does not need any exact 4-input gate minima. It uses nonzero truth tables, trimming, literal factors, cofactors, and signed-AND module quotients; all costs are recursive weights. Prove its lower-bound induction once, then check the four finite weight calculations with a Lean executable truth-table recurrence. Percy UNSAT certificates are not needed for this particular theorem. They are relevant to separate exact-minimum claims. This should simplify the formalization roadmap for 17n/12 and the pending robust-identifier 2n-o(n) result below.

## 1. Mandatory interface extraction

Let independent source bits be x in F2^n and let q be query/context bits. Assume the target satisfies f(x,q_i)=x_i for selected queries q_i (a complemented demanded bit works equally well). For arbitrary AIG topology, compute syntactic primary support of every wire. Walk backward from output, stopping at every wire with no query ancestor; ignore constants. The resulting frontier includes raw source inputs and computed source-only gates E_j(x). For each q_i, substitute query constants into the downstream circuit, treating the frontier wires as formal independent inputs, and simplify only sound identities (constant propagation, aliases, complements, structural hashing suffice). Let S_i be the raw input indices and K_i the computed frontier wires on which the resulting decoder syntactically depends. Then necessarily

    x_i = D_i(x[S_i], E[K_i](x)).

The interface is mandatory, not assumed in a decomposition of the target. Actual semantic support of the independent decoder could be used for further pruning. If i is in S_i the obligation is trivial. Otherwise every pair a,b with a_i != b_i and a[S_i]=b[S_i] must be distinguished by at least one E_j, j in K_i. Computed ports may be arbitrarily correlated; no independent-output assumption is made in the necessity direction. In the relaxed problem, an arbitrary choice of port functions satisfying all pair conditions permits unrestricted decoders, by assigning each observed decoder input its unique demanded bit. This is exact for the relaxed interface, not for realizing the ports/decoders in a fixed AIG gate budget. The reference extractor is for one demand per selected context, using ordinary AIG ANDs with free complemented edges.

## 2. Forced Boolean derivative theorem

Use Boolean derivative Delta_d E_j(x)=E_j(x) XOR E_j(x XOR d), for nonzero d in F2^n. A query with i not in S_i imposes the universal obligation

    OR_(j in K_i) Delta_d E_j(x) = 1 for every x,
    whenever d_i=1 and d[S_i]=0.

If E_j has syntactic support P_j, any unit vector outside P_j has constant derivative 0. For a given function, the directions with constant derivative form a linear subspace V_j; their constant values form a linear functional ell_j: V_j -> F2. This follows from

    Delta_(u+v) E_j(x) = Delta_u E_j(x) XOR Delta_v E_j(x XOR u).

Maintain a certified subspace and functional in a GF(2) echelon basis for each port. It may be a strict subset of the actual constant-derivative space. For an obligation (d,K), evaluate ell_j(d) where d is in the known subspace. A known 1 discharges it. Discard known 0 ports. If no port remains, the topology is impossible. If exactly one remains, its derivative must be identically 1: extend its subspace/functional. Otherwise defer. Iterate to a fixed point. Every successful extension adds an independent basis direction; there are at most n*k extensions. Explicit obligations are exponential in n, so this is a small-source-block tool, not a polynomial-time general synthesis algorithm. Restricting to a subset of obligations remains a sound rejection test. A certificate consists of the original supports, obligations and sequence of forced extensions, ending in all zero derivatives for one obligation; replay is integer XOR elimination.

### Strict separation from support and subset-capacity tests

Take three source bits a,b,c and two computed ports with allowed supports {a,b}, {a,c}. Query a has no raw side information and only port 0; query b has raw c and ports 0,1; query c has raw b and only port 1. Each difference has a syntactically capable available port. All subset confusion-graph capacity tests pass (one bit suffices for each singleton; two bits suffice for each pair and the whole three-bit instance because b,c have mutual side information). But the first query forces E_0=a or NOT a, independent of b. The second query can recover b only through E_0, since E_1 cannot depend on b and c is fixed. Contradiction. Equivalently it forces Delta_b E_0=1 despite Delta_b E_0=0. Both ports can be actual source-only AND gates; use branches selected by query constants with raw dependencies as above. The reference constructs this concrete topology and checks the extracted masks. The same separation persists for arbitrarily many disjoint copies: capacity tests factor over copies (the independence number of the disjunctive product of confusion graphs multiplies), whereas one impossible copy suffices for propagation rejection. Tests run on 1–4 copies, full subset baseline on 1–2 copies. This is a wrong-topology example, not a lower bound for the minimum selector circuit.

## 3. Exact quotient closure and gate-budget consequences

For each consistent known basis V_j with functional ell_j, choose a linear complement W_j. Write x=v+w uniquely, v in V_j and w in W_j. All functions satisfying the known derivatives, and only those functions, have the form

    E_j(v+w)=ell_j(v) XOR H_j(w),

where H_j is arbitrary. If d_j=n-dim(V_j), only 2^d_j truth-table entries are unknown; one entry can be fixed to zero because complementing a port is harmless in the relaxed interface. Enumerate 2^(2^d_j-1) candidate functions, rather than 2^(2^|P_j|-1). The reference enumerates residual pair obligations after discharging all known-1 constraints and omitting known-0 ports. Candidate functions cover bitsets of pairs; choose one per port whose union covers all residual obligations. Dominated coverage sets can be removed because the relaxed model puts no cost on the individual functions. This is an exact finite oracle for that relaxed model; do NOT use it to certify a concrete topology as realizable without checking gates. When all d_j<=1, every remaining H_j is affine, so linear parity-mask search is complete (constants/complements immaterial). With d_j<=1 and at most two unknown ports per obligation, the residual choice problem is 2-SAT. No blanket linear-code sufficiency claim for larger quotient dimensions.

**Gate count, using actual mandatory interfaces.** For a circuit with no semantically constant/neutral gates (in particular a minimum AIG), take r distinct demanded inputs not present among their respective raw sides. Take the union of their available computed-port cones, with g live gates and k distinct internal output wires. Every demanded input must occur at least twice as a gate operand in this union: with just one occurrence, its sole AND has another operand independent of that input, and that other operand can be set to its controlling value. The selected receiver would then see identical raw side bits and computed ports on both assignments differing only in the demanded bit. Count operands: at least 2r from these inputs and at least g-k from internal gates that are not ports. Hence g >= 2r-k. This applies to any subset of distinct demanded inputs and the corresponding union of cones. Do not sum overlapping cone lower bounds. If simplifying a nonminimal circuit, re-extract the interface first. For each port, if t unit directions are forced to derivative 1, fixing other inputs leaves parity or its complement on t bits. The reviewed additive-weight recurrence gives w(parity_t)=3t-2 (t>=1), so its cone has at least 3(t-1) AIG gates. This is a lower bound on the actual cone, not a claim of the full-circuit minimum. The parity gate bound here uses the earlier reviewed, not yet Lean-checked weight theorem.

## 4. A limitation: first-moment Fourier relaxations add nothing after closure

Write F_j(x)=(-1)^E_j(x), with normalized Fourier coefficients hat(F_j)(s). Parseval gives sum_s hat(F_j)(s)^2=1. The probability that a derivative is 1 at a uniformly random x is the sum of these nonnegative squared coefficients over parity masks s with s dot d=1 (the autocorrelation identity). Thus for each obligation, a necessary relaxation is sum over available ports of these probabilities >=1. The support of the Fourier distribution is confined to affine masks satisfying s dot v=ell_j(v) for every known basis direction v, including the zeros outside P_j. An LP over arbitrary distributions on those masks seems promising, but **after forced-derivative closure it can never reject more instances**: the uniform distribution on each nonempty affine mask set gives derivative probability 0 or 1 on known directions and exactly 1/2 on every unknown direction, by pairing masks with opposite dot products. Every remaining obligation has either a known 1 or at least two unknown ports, so the inequality holds. This proves a barrier for this particular first-moment relaxation. It says nothing about higher moments, joint correlations, or gate costs. An exploratory SciPy LP on the 516 propagation survivors found zero exclusions, as the proof predicts; do not add an LP to the native solver. The theorem makes reproducing that LP unnecessary.

## 5. Executed checks and recommendation

Reproduction: extract the code block below to `semantic_ports.py` and run `python3 semantic_ports.py` (standard library only; seed 261126). 3,000 random draws, 2,880 kept (2–4 inputs, 1–3 computed ports, each support <=3). Exact nonlinear oracle independently enumerates unrestricted Boolean port functions and pair coverage. Of 2,880 relaxed interfaces, 506 feasible, 2,374 impossible. Previous combined baseline excludes 2,329; derivative propagation alone excludes 2,364; combined excludes 2,371, including 42 extra exclusions (baseline alone catches seven that propagation misses). The remaining three impossible cases are detected by exact quotient closure. No false rejection in either test. Quotient oracle agrees with independent full oracle on all 516 propagation survivors, reducing aggregate candidate port truth tables (before dominance pruning, sum across ports/instances) from 21,720 to 6,346 (70.8% fewer). On 342 of those instances all quotient dimensions <=1; linear search agrees with exact as proved. All 506 feasible random interfaces happen to have a linear solution; not a general theorem.

200 planted selector AIGs, 3–7 source inputs, actual computed ports and raw side-information routes: 54,816 source/query truth evaluations, 821 demanded source instances with no direct raw bypass, 98,256 evaluations of inferred basis derivatives, 5,920 subset-cone slot bounds (55 tight), 249 nontrivial parity-cone bounds (161 tight), all pass. Four planted incompatible topology families reject, baseline passes both small cases checked. No native C++ integration, SAT solver verdict, independent reviewer, or Lean proof is claimed in this round.

**Recommendation:** keep this as a targeted topology/partial-synthesis filter, not a default solver pass. It is a stronger semantic test than width counting, and the quotient oracle supplies exact small-interface ground truth. It does not show all small SAT circuits have a restrictive enough frontier: a circuit may pass the demanded raw bit directly to the decoder or mix query bits with sources early. E.g. a selector can gate each raw input by its address indicator and OR the results, bypassing computed pure-source ports entirely. Next mathematical challenge: obtain a size-dependent constraint on such bypasses/early mixing for a SAT restriction, so that semantic interface costs can be charged across many queries without double-counting. Do not equate the 70.8% option count decrease with runtime or a general circuit lower bound. For Lean, prioritize the already pending SAT theorem chain above; the new local lemma can be formalized independently from GF(2) derivative identities if useful.

```python
"""Mandatory query interfaces and forced Boolean derivatives (Python 3)."""
from itertools import combinations, product
from random import Random
from collections import Counter
from functools import lru_cache

def bits(x):
    while x:
        b=x&-x; yield b.bit_length()-1; x^=b

def subsets(x):
    s=x
    while True:
        yield s
        if not s:return
        s=(s-1)&x

class Basis:
    def __init__(self):self.rows={}
    def reduce(self,d,p=0):
        while d:
            i=d.bit_length()-1
            if i not in self.rows:break
            a,b=self.rows[i];d^=a;p^=b
        return d,p
    def value(self,d):
        a,b=self.reduce(d);return b if not a else None
    def add(self,d,p):
        a,b=self.reduce(d,p)
        if not a:return -1 if b else 0
        self.rows[a.bit_length()-1]=(a,b);return 1

def obligations(n,queries):
    # query=(demand primary i, raw side mask, available computed-port mask)
    return sorted({(D,K) for i,S,K in queries if not S>>i&1
                   for D in subsets(((1<<n)-1)^S) if D>>i&1})

def propagate(n,supports,queries):
    B=[Basis() for _ in supports]
    for j,P in enumerate(supports):
        for i in range(n):
            if not P>>i&1:B[j].add(1<<i,0)
    obs=obligations(n,queries); trace=[]
    while True:
        changed=False
        for D,K in obs:
            vals=[(j,B[j].value(D)) for j in bits(K)]
            if any(v==1 for j,v in vals):continue
            unknown=[j for j,v in vals if v is None]
            if not unknown:return False,B,trace,(D,K)
            if len(unknown)==1:
                j=unknown[0];assert B[j].add(D,1)==1
                trace.append((D,K,j));changed=True
        if not changed:return True,B,trace,None

def linear_code(supports,n,queries):
    obs=obligations(n,queries)
    for rows in product(*(list(subsets(P)) for P in supports)):
        if all(any((rows[j]&D).bit_count()%2 for j in bits(K)) for D,K in obs):return rows
    return None

@lru_cache(None)
def alpha(sides):
    n=len(sides)
    ok=[D for D in range(1,1<<n) if all(sides[i]&D for i in bits(D))]
    adj={a:sum(1<<b for b in ok if a!=b and all(sides[i]&(a^b) for i in bits(a^b))) for a in ok}
    best=1
    def rec(p,k):
        nonlocal best
        best=max(best,k)
        while p and k+p.bit_count()>best:
            b=p&-p;p^=b;rec(p&adj[b.bit_length()-1],k+1)
    rec(sum(1<<a for a in ok),1);return best

def subset_capacity(n,supports,queries):
    # Fix other primary bits and count only ports relevant to the remaining
    # sources and available to at least one chosen receiver.
    Q=[(i,S,K) for i,S,K in queries if not S>>i&1]
    assert len({i for i,S,K in Q})==len(Q)
    for I in range(1,1<<len(Q)):
        A=[Q[i] for i in bits(I)];mask=sum(1<<i for i,S,K in A)
        s=tuple(sum(((S>>v)&1)<<j for j,(v,_,_) in enumerate(A)) for i,S,K in A)
        ports=0
        for i,S,K in A:
            for j in bits(K):
                if supports[j]&mask:ports|=1<<j
        if (1<<ports.bit_count())*alpha(s)<1<<len(A):return False
    return True

def coverage_oracle(n,supports,queries):
    # Exact unrestricted Boolean port functions, from all unordered pairs.
    tasks=[]
    for i,S,K in queries:
        if S>>i&1:continue
        for a,b in combinations(range(1<<n),2):
            if ((a^b)>>i&1) and not ((a^b)&S):tasks.append((K,a,b))
    full=(1<<len(tasks))-1
    options=[]
    for j,P in enumerate(supports):
        ids=list(bits(P));size=1<<len(ids)
        compress=lambda a:sum(((a>>v)&1)<<i for i,v in enumerate(ids))
        relevant=[(1<<i,compress(a),compress(b)) for i,(K,a,b) in enumerate(tasks) if K>>j&1 and (a^b)&P]
        cov=set()
        for t in range(0,1<<size,2):
            cov.add(sum(bit for bit,a,b in relevant if ((t>>a)^(t>>b))&1))
        opts=[]
        for c in sorted(cov,key=int.bit_count,reverse=True):
            if not any(c&~d==0 for d in opts):opts.append(c)
        options.append(opts)
    options.sort(key=len)
    suffix=[0]*(len(options)+1)
    for i in reversed(range(len(options))):
        suffix[i]=suffix[i+1]
        for c in options[i]:suffix[i]|=c
    def rec(i,c):
        if c==full:return True
        if i==len(options) or c|suffix[i]!=full:return False
        return any(rec(i+1,c|v) for v in options[i])
    return rec(0,0)

def quotient_oracle(n,supports,queries,B):
    # For each port, enumerate free Boolean values only on quotient cosets.
    # Exact within this explicit truth-table model; independent port functions
    # are permitted, so feasibility is not an AIG realization certificate.
    tasks=[]
    for D,K in obligations(n,queries):
        vals=[(j,B[j].value(D)) for j in bits(K)]
        if any(v==1 for j,v in vals):continue
        K=sum(1<<j for j,v in vals if v is None)
        if not K:return False,0,0,False
        for a in range(1<<n):
            if a<a^D:tasks.append((K,a,a^D))
    full=(1<<len(tasks))-1;opts=[];old=0;new=0;affine=True
    for j,(P,b) in enumerate(zip(supports,B)):
        free=[i for i in range(n) if i not in b.rows]
        dim=len(free);affine &= dim<=1
        old+=1<<( (1<<P.bit_count())-1 )
        new+=1<<( (1<<dim)-1 )
        def rep(a):
            p=0
            for i,(v,c) in sorted(b.rows.items(),reverse=True):
                if a>>i&1:a^=v;p^=c
            r=sum(((a>>i)&1)<<k for k,i in enumerate(free));return r,p
        rp=[rep(a) for a in range(1<<n)]
        rel=[(1<<i,*rp[a],*rp[c]) for i,(K,a,c) in enumerate(tasks) if K>>j&1]
        cov=set()
        for H in range(0,1<<(1<<dim),2):
            cov.add(sum(bit for bit,a,p,c,q in rel if ((H>>a)^(H>>c)^p^q)&1))
        O=[]
        for C in sorted(cov,key=int.bit_count,reverse=True):
            if not any(C&~d==0 for d in O):O.append(C)
        opts.append(O)
    opts.sort(key=len);suffix=[0]*(len(opts)+1)
    for i in reversed(range(len(opts))):
        suffix[i]=suffix[i+1]
        for c in opts[i]:suffix[i]|=c
    def rec(i,c):
        if c==full:return True
        if i==len(opts) or c|suffix[i]!=full:return False
        return any(rec(i+1,c|v) for v in opts[i])
    return rec(0,0),old,new,affine


def baseline(n,supports,queries):
    return (all(any(supports[j]&D for j in bits(K)) for D,K in obligations(n,queries))
            and subset_capacity(n,supports,queries))

class AIG:
    def __init__(self,n):self.n=n;self.g=[];self.hash={}
    def AND(self,a,b):
        if a==0 or b==0 or a==b^1:return 0
        if a==1:return b
        if b==1 or a==b:return a
        p=tuple(sorted((a,b)))
        if p not in self.hash:
            self.g.append(p);self.hash[p]=2*(self.n+len(self.g))
        return self.hash[p]
    def OR(self,a,b):return self.AND(a^1,b^1)^1
    def XOR(self,a,b):return self.OR(self.AND(a,b^1),self.AND(a^1,b))
    def parity(self,seq):
        x=0
        for a in seq:x=self.XOR(x,a)
        return x
    def columns(self):
        mask=(1<<(1<<self.n))-1
        V=[0]+[sum(((r>>i)&1)<<r for r in range(1<<self.n)) for i in range(self.n)]
        def read(l):return V[l//2]^(mask if l&1 else 0)
        for a,b in self.g:V.append(read(a)&read(b))
        return V
    def table(self,out):return self.columns()[out//2]^(((1<<(1<<self.n))-1) if out&1 else 0)

def select(aig,n,branches):
    # Gate each port separately by the query before decoder parity, so raw
    # bypass inputs and computed source-only ports are actual frontier wires.
    r=(len(branches)-1).bit_length();out=0
    for q,seq in enumerate(branches):
        en=1
        for j in range(r):en=aig.AND(en,2*(n+j+1)^(1-((q>>j)&1)))
        out=aig.OR(out,aig.parity(aig.AND(en,a) for a in seq))
    return out

def extract(aig,out,n,tests):
    """Actual mandatory frontier, per-query structural simplification.
    Tests = (query assignment, demanded source index). No claim a wrong target
    equals the circuit: the returned obligations are necessary if it does.
    """
    parents=[()]*(aig.n+1)+[tuple(l//2 for l in g) for g in aig.g]
    sup=[0]+[1<<i for i in range(aig.n)]
    for a,b in parents[aig.n+1:]:sup.append(sup[a]|sup[b])
    P=(1<<n)-1; frontier=set();todo=[out//2];seen=set()
    while todo:
        v=todo.pop()
        if v in seen:continue
        seen.add(v)
        if not sup[v]&~P:
            if v:frontier.add(v)
        else:todo.extend(parents[v])
    raw=sorted(v for v in frontier if v<=n)
    ports=sorted(v for v in frontier if v>n)
    F=raw+ports;pos={v:i for i,v in enumerate(F)};queries=[]
    for q,i in tests:
        dec=AIG(len(F));memo={0:0}
        def walk(v):
            if v not in memo:
                if v in pos:memo[v]=2*(pos[v]+1)
                elif v<=aig.n:memo[v]=(q>>(v-n-1))&1
                else:
                    a,b=aig.g[v-aig.n-1]
                    memo[v]=dec.AND(walk(a//2)^(a&1),walk(b//2)^(b&1))
            return memo[v]
        z=walk(out//2)^(out&1); ds=[0]+[1<<i for i in range(len(F))]
        for a,b in dec.g:ds.append(ds[a//2]|ds[b//2])
        d=ds[z//2]
        S=sum(1<<(v-1) for j,v in enumerate(raw) if d>>j&1)
        K=sum(1<<j for j,v in enumerate(ports) if d>>(j+len(raw))&1)
        queries.append((i,S,K))
    return [sup[v] for v in ports],queries,ports

def test_planted(rng):
    checks=0; demanded=0;forced=0;slot_checks=0;parity_checks=0;slot_tight=0;parity_tight=0
    for case in range(200):
        n=rng.randrange(3,8);r=(n-1).bit_length();a=AIG(n+r);x=[2*(i+1) for i in range(n)]
        unused=set(range(n));branch=[None]*n
        while unused:
            i=min(unused);mask=(1<<i)|rng.randrange(1<<n)
            if rng.randrange(4)==0:mask=1<<i
            h=a.parity(x[j] for j in bits(mask))
            for j in list(unused):
                if mask>>j&1:
                    branch[j]=[h]+[x[t] for t in bits(mask^(1<<j))];unused.remove(j)
        out=select(a,n,branch);P,Q,ports=extract(a,out,n,[(i,i) for i in range(n)])
        tt=a.table(out)
        for i in range(n):
            for xx in range(1<<n):assert ((tt>>(xx|(i<<n)))&1)==((xx>>i)&1);checks+=1
        valid,B,trace,bad=propagate(n,P,Q);assert valid,(P,Q,bad)
        C=a.columns()
        for j,b in enumerate(B):
            for D,p in b.rows.values():
                for xx in range(1<<n):assert ((C[ports[j]]>>xx)^(C[ports[j]]>>(xx^D)))&1==p;forced+=1
        demanded+=sum(not S>>i&1 for i,S,K in Q)
        def cone(J):
            seen=set();todo=[ports[j] for j in bits(J)]
            while todo:
                v=todo.pop()
                if v<=a.n or v in seen:continue
                seen.add(v);todo.extend(l//2 for l in a.g[v-a.n-1])
            return seen
        R=[(i,K) for i,S,K in Q if not S>>i&1]
        for I in range(1,1<<len(R)):
            K=0
            for j in bits(I):K|=R[j][1]
            lb=2*I.bit_count()-K.bit_count();g=len(cone(K))
            assert g>=lb;slot_checks+=1;slot_tight+=g==lb
        for j,b in enumerate(B):
            t=sum(b.value(1<<i)==1 for i in range(n))
            if t>=2:
                g=len(cone(1<<j));assert g>=3*(t-1);parity_checks+=1;parity_tight+=g==3*(t-1)
    return checks,demanded,forced,slot_checks,slot_tight,parity_checks,parity_tight

def main():
    rng=Random(261126); stats=Counter();examples={}
    for z in range(3000):
        n=rng.choice([2,3,4]); k=rng.choice([1,2,3]);P=[rng.randrange(1,1<<n) for _ in range(k)]
        Q=[(i,rng.randrange(1<<n)&~(1<<i),rng.randrange(1,1<<k)) for i in range(n)]
        if max(p.bit_count() for p in P)>3:continue
        base=baseline(n,P,Q); valid,B,tr,bad=propagate(n,P,Q);lin=linear_code(P,n,Q);exact=coverage_oracle(n,P,Q)
        assert not exact or (base and valid)
        assert lin is None or exact
        if valid:
            qok,old,new,affine=quotient_oracle(n,P,Q,B)
            assert qok==exact
            stats['quotient_calls']+=1;stats['raw_options']+=old;stats['quotient_options']+=new
            stats['affine_complete']+=affine
            if affine:assert (lin is not None)==exact
            stats['both_prior_pass_exact_reject']+=base and not exact
        stats['cases']+=1;stats['base_reject']+=not base;stats['prop_reject']+=not valid
        stats['exact_reject']+=not exact;stats['linear_feasible']+=lin is not None
        if base and not valid:
            stats['extra_reject']+=1;examples.setdefault('extra',(n,P,Q,tr,bad))
        if valid and not exact:stats['incomplete']+=1;examples.setdefault('incomplete',(n,P,Q,tr,bad))
        if exact and lin is None:stats['nonlinear_only']+=1;examples.setdefault('nonlinear',(n,P,Q,tr,bad))
    print('random',dict(stats));print('examples',examples)
    print('planted',test_planted(rng))
    # Strict separation on an actual AIG topology and wrong selector target.
    for q in range(1,5):
        n=3*q;r=(n-1).bit_length();a=AIG(n+r);branch=[]
        for t in range(q):
            x,y,z=[2*(3*t+i+1) for i in range(3)]
            h=a.AND(x,y);k=a.AND(x,z)
            branch.extend([[h],[h,k,z],[k,y]])
        out=select(a,n,branch);P,Q,ports=extract(a,out,n,[(i,i) for i in range(n)])
        assert P==[p<<(3*t) for t in range(q) for p in (3,5)]
        assert Q==[(3*t+i,S<<(3*t),K<<(2*t)) for t in range(q) for i,S,K in ((0,0,1),(1,4,3),(2,2,2))]
        assert not propagate(n,P,Q)[0]
        # Full subset capacity exponential in q, only replay q<=2 here.
        if q<=2:assert baseline(n,P,Q)
    print('planted incompatible topology families',4)

if __name__=='__main__':main()

```

---


---

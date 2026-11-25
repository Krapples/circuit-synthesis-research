"""Bounded rerun of the 12 free-NOT excess-5 searches that phase-first / phase-certificate leave open at 120 s, with the
'phase-certificate-fastkey' completion and, matched, plain 'phase-certificate' (symmetry_limit=1 cache keys), one process per search, fixed cap. Witnesses are
rebuilt by ordered_quotient_core.reconstruct; an empty result is provisional under search_exact's contract.
Writes results/fastkey_e5.jsonl. Usage: python experiments/fastkey_e5.py [seconds]"""
import json, os, sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
from phase_first_layout import one_job
CASES = ('comparator-04', 'comparator-08', 'complete-5', 'complete-6', 'hypergraph-05', 'hypergraph-09', 'hypergraph-10',
         'hypergraph-15', 'hypergraph-20', 'petersen-10', 'random-monotone-05', 'threshold-5-3')

if __name__ == '__main__':
    # Matched: each mode runs all 12 searches at once (same load); modes one after the other on an idle machine.
    seconds = float(sys.argv[1]) if len(sys.argv) > 1 else 300
    out = open(os.path.join(HERE, 'results', 'fastkey_e5.jsonl'), 'w', encoding='utf-8')
    for mode in ('phase-certificate-fastkey', 'phase-certificate'):
        with Pool(len(CASES), maxtasksperchild=1) as p:
            for nm, md, r in p.imap_unordered(one_job, [(c, mode, seconds, 5) for c in CASES]):
                out.write(json.dumps(dict(case=nm, mode=md, cap=seconds, **r)) + '\n'); out.flush()
                print(f"{md:26} {nm:20} {r['status']} {r['result']} {r['seconds']}s calls={r['phase_calls']}", flush=True)

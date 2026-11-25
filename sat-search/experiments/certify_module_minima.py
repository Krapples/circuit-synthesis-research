"""Certify minima found through module preprocessing without relying on the module theorem.

For each case in results/module_core_minima.jsonl with a verified lifted witness at M (basis general =
counted NOT, and monotone), try to prove exact sizes M-1 and M-2 UNSAT for the original function with the
independent reference encoder and a DRUP proof checked by the RUP checker (verify/evidence.py). A case whose
two exclusions are checked is a CERTIFIED minimum; a time-limited call that does not finish leaves it
rule-dependent (resting on the module theorem). Writes results/module_minima_certificates.jsonl.
Usage: python experiments/certify_module_minima.py [max_n] [seconds_per_call]"""
import json, os, sys, time
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'verify')); sys.path.insert(0, os.path.join(HERE, 'experiments'))
import reference as ref
from certify_synthesis import check_proof
from signed_bound_compare import cases, restrict_essential, monotone_terms


def checked(n, tt, G, basis, seconds):
    t0 = time.time()
    w, info = ref.sat_exists(n, tt, G, basis, proof=True, seconds=seconds)
    if info.get('undecided'):
        return dict(kind='open', seconds=round(time.time() - t0, 1))
    if w is not None:
        return dict(kind='CONTRADICTION', circuit=w)
    if info.get('trivial'):
        return dict(kind='checked_unsat', trivial=True)
    proof = list(info['proof'])
    if not proof or proof[-1].split() != ['0']:
        proof.append('0')
    steps = check_proof(info['vars'], info['cnf'], proof)
    return dict(kind='checked_unsat', proof_steps=steps, cnf_clauses=len(info['cnf']), seconds=round(time.time() - t0, 1))


def certify(item):
    name, n, f, basis, M, seconds = item
    ex = {}
    for G in (M - 1, M - 2):
        if G < n - 1:
            ex[G] = dict(kind='checked_unsat', reason='below n - 1 (read counting)')
            continue
        ex[G] = checked(n, f, G, basis, seconds)
    grade = 'CERTIFIED' if all(e['kind'] == 'checked_unsat' for e in ex.values()) else         'CONTRADICTION' if any(e['kind'] == 'CONTRADICTION' for e in ex.values()) else 'rule-dependent'
    return dict(case=name, basis=basis, n=n, minimum=M, grade=grade, exclusions=ex)


if __name__ == '__main__':
    from multiprocessing import Pool
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    seconds = float(sys.argv[2]) if len(sys.argv) > 2 else 900
    found = {json.loads(l)['case']: json.loads(l) for l in open(os.path.join(HERE, 'results', 'module_core_minima.jsonl'))}
    items = []
    for name, fam, n0, f0 in cases():
        r = found.get(name)
        if r is None:
            continue
        n, f, _ = restrict_essential(n0, f0)
        if n > max_n:
            continue
        for basis in ('general', 'monotone'):
            M = r.get(f'{basis}_min')
            if M is not None and r.get(f'{basis}_witness_verified') is True:
                items.append((name, n, f, basis, M, seconds))
    print(f'{len(items)} (case, basis) minima to certify, one worker each', flush=True)
    out = open(os.path.join(HERE, 'results', 'module_minima_certificates.jsonl'), 'a', encoding='utf-8')
    with Pool(max(1, min(11, len(items)))) as p:
        for rec in p.imap_unordered(certify, items):
            out.write(json.dumps(rec) + chr(10)); out.flush()
            print(f'{rec["case"]} {rec["basis"]}: minimum {rec["minimum"]} {rec["grade"]} '
                  f'{ {g: e["kind"] for g, e in rec["exclusions"].items()} }', flush=True)

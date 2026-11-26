#!/usr/bin/env python3
"""Proof-producing replay for the nine-gate core of L-meta-16102.

Premise: the paper reduction in two_fork_handoff.md (not yet Lean checked).
Requires the native workspace's python-sat and an independent drat-trim executable.
The checker verdict certifies the CNF, not the Lean circuit-to-CNF theorem.
Run --self-test without either dependency to check the added syntax/path clauses.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
from threading import Timer
from time import monotonic

HERE = Path(__file__).resolve().parent


def added_clauses(n, ops, sel, fresh):
    """Return clauses for exactly one live internal NOT and positive bypass.

    sel[j,slot] contains earlier wire choices then one missing-operand flag.
    The fresh() callback returns an unused positive CNF variable.
    """
    end = max(ops)
    C = []
    nots = [v[2] for v in ops.values()]
    C.append(nots)
    C.extend([-a, -b] for a, b in itertools.combinations(nots, 2))
    C.append([-ops[end][2]])
    for j, (a, o, u) in ops.items():
        L, R = sel[j, 0], sel[j, 1]
        # Binary gates need both operands; archived encoder enforces distinct/order.
        C.extend(([-a, -L[-1]], [-a, -R[-1]],
                  [-o, -L[-1]], [-o, -R[-1]]))
        # The lone NOT has a prior gate as first operand and no second operand.
        C.extend(([-u, *L[n:j]], [-u, R[-1]]))
    # good[i] asserts there is a directed path to the output avoiding the NOT.
    # Encode only the existence implication, with edge witnesses.
    good = {i: fresh() for i in range(end + 1)}
    aux = {}
    C.append([good[end]])
    for i in range(n):
        C.append([good[i]])
    for i in range(end):
        choices = []
        for j in range(max(n, i+1), end+1):
            for t in (0, 1):
                a = fresh()
                aux[i, j, t] = a
                choices.append(a)
                C.extend(([-a, good[j]], [-a, -ops[j][2]],
                          [-a, sel[j, t][i]]))
        C.append([-good[i], *choices])
    return C, good, aux


def self_test():
    """Check the extra clauses on every small candidate syntax and bypass path.

    No SAT solver: set the explicit syntax variables and construct the witness
    path flags deterministically. Also test every assignment to good flags on
    each rejected proper internal-NOT graph, ensuring no false bypass witness.
    """
    n, end = 2, 5
    counter = 0
    def fresh():
        nonlocal counter
        counter += 1
        return counter
    ops = {j: [fresh() for _ in range(3)] for j in range(n, end+1)}
    sel = {(j,t): [fresh() for _ in range(j+1)]
           for j in ops for t in (0,1)}
    C, good, aux = added_clauses(n,ops,sel,fresh)
    def sat(C, assignment):
        return all(any((l>0)==(abs(l) in assignment) for l in c) for c in C)
    tested = accepted = rejected = path_flag_checks = 0
    # Include degenerate/invalid cases in a deterministic exhaustive product;
    # the proper-binary distinct-input convention belongs to the old encoder.
    candidates = []
    for j in ops:
        p = [(op, a, b) for op in (0,1)
             for a,b in itertools.combinations(range(j),2)]
        p += [(2,a,j) for a in range(j)]
        candidates.append(p)
    for gates in itertools.product(*candidates):
        base = set()
        for j,(op,a,b) in zip(ops,gates):
            base.update((ops[j][op],sel[j,0][a],sel[j,1][b]))
        not_positions = [j for j,(op,a,b) in zip(ops,gates) if op==2]
        internal = (len(not_positions)==1 and not_positions[0]!=end
                    and gates[not_positions[0]-n][1]>=n)
        reachable = {end}
        for j in reversed(list(ops)):
            op,a,b=gates[j-n]
            if j in reachable and op!=2:
                reachable.update((a,b))
        expected = internal and all(i in reachable for i in range(n))
        # All edge-witness variables that are consistent with the good flags.
        def assign(R):
            z=base|{good[i] for i in R}
            for (i,j,t),a in aux.items():
                op,x,y=gates[j-n]
                if j in R and op!=2 and (x,y)[t]==i:
                    z.add(a)
            return z
        assert sat(C,assign(reachable)) == expected
        if internal and not expected:
            for mask in range(1<<(end+1)):
                R={i for i in range(end+1) if mask>>i&1}
                assert not sat(C,assign(R))
                path_flag_checks += 1
        tested+=1
        accepted+=expected
        rejected+=not expected
    # Verify the expected symmetry reduction independently of PySAT.
    table=18445899635892944896
    perms=[p for p in itertools.permutations(range(6)) if all(
        (table>>x&1)==(table>>sum((x>>i&1)<<p[i] for i in range(6))&1)
        for x in range(64))]
    seen=set(); representatives=[]
    for op in (0,1):
        for pair in itertools.combinations(range(6),2):
            if (op,pair) in seen: continue
            representatives.append((op,pair))
            for p in perms:
                seen.add((op,tuple(sorted(p[i] for i in pair))))
    assert len(representatives)==22
    return dict(toy_syntax_cases=tested, accepted=accepted, rejected=rejected,
                exhaustive_negative_path_flag_checks=path_flag_checks,
                first_gate_representatives=len(representatives))


def load_archive():
    spec=importlib.util.spec_from_file_location(
        "lmeta16102_archive", HERE/"search-16102-full.py")
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    h=hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda:f.read(1024*1024),b""):
            h.update(chunk)
    return h.hexdigest()


def run_job(archive, first, job_id, out, args):
    C, ops, sel=archive.build(9)
    largest=max(abs(l) for c in C for l in c)
    def fresh():
        nonlocal largest
        largest+=1
        return largest
    extra,_,_=added_clauses(6,ops,sel,fresh)
    C.extend(extra)
    op,(a,b)=first
    C.extend(([ops[6][op]],[sel[6,0][a]],[sel[6,1][b]]))
    prefix=out/f"shard-{job_id:02d}"
    cnf=prefix.with_suffix(".cnf")
    proof=prefix.with_suffix(".drup")
    with cnf.open("x",encoding="ascii",newline="\n") as f:
        f.write(f"p cnf {largest} {len(C)}\n")
        for c in C: f.write(" ".join(map(str,c))+" 0\n")
    record=dict(job=job_id,first=first,variables=largest,clauses=len(C),
                cnf_sha256=sha(cnf),solver=args.solver,
                encoding="archived direct syntax + eight-binary reduction")
    start=monotonic()
    try:
        with archive.cs.Solver(name=args.solver,bootstrap_with=C,
                               with_proof=True) as solver:
            timer=Timer(args.timeout,solver.interrupt)
            timer.start()
            try:
                result=solver.solve_limited(expect_interrupt=True)
            finally:
                timer.cancel()
                timer.join()
            record.update(result="SAT" if result else "OPEN" if result is None else "UNSAT",
                          elapsed_s=round(monotonic()-start,3),
                          solver_stats=solver.accum_stats())
            if result is False:
                trace=solver.get_proof()
                if trace is None:
                    raise RuntimeError("solver did not return a proof")
                with proof.open("x",encoding="ascii",newline="\n") as f:
                    for line in trace: f.write(line.rstrip()+"\n")
                record.update(proof_sha256=sha(proof),proof_bytes=proof.stat().st_size)
            elif result is True:
                model=set(solver.get_model());gates=[]
                for j,choices in ops.items():
                    op=next(i for i,l in enumerate(choices) if l in model)
                    inputs=[i for t in (0,1) for i,l in enumerate(sel[j,t][:-1]) if l in model]
                    gates.append((op,inputs))
                archive.verify(gates)
                record["counterexample"]=gates
        if result is False:
            try:
                check=subprocess.run([args.proof_checker,str(cnf),str(proof)],
                                     capture_output=True,text=True,
                                     timeout=args.check_timeout,check=False)
                log=prefix.with_suffix(".verify.txt")
                log.write_text(check.stdout+"\n"+check.stderr,encoding="utf-8")
                record.update(verifier_returncode=check.returncode,
                              verifier_log_sha256=sha(log),
                              independently_verified=(check.returncode==0 and
                                  any(line.strip()=="s VERIFIED" for line in check.stdout.splitlines())))
            except (OSError,subprocess.TimeoutExpired) as exc:
                record.update(independently_verified=False, verifier_error=str(exc))
    except Exception as exc:
        record.update(error=str(exc),independently_verified=False)
    prefix.with_suffix(".json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
    return record


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--self-test",action="store_true")
    p.add_argument("--out",type=Path)
    p.add_argument("--job",type=int,action="append",help="0..21; repeat; omit for all")
    p.add_argument("--solver",default="glucose4")
    p.add_argument("--timeout",type=float,default=300)
    p.add_argument("--check-timeout",type=float,default=600)
    p.add_argument("--proof-checker",default="drat-trim")
    a=p.parse_args()
    if a.self_test:
        print(json.dumps(self_test(),indent=2));return
    if a.out is None: p.error("--out is required")
    archive=load_archive()
    jobs=[first for size,first in archive.jobs()
          if size==9 and first is not None and first[0] in (0,1) and len(first[1])==2]
    assert len(jobs)==22
    selected=list(range(22)) if a.job is None else sorted(set(a.job))
    if any(i<0 or i>=22 for i in selected):p.error("job must be 0..21")
    a.out.mkdir(parents=True,exist_ok=False)
    (a.out/"manifest.json").write_text(json.dumps(dict(
        all_representatives=jobs,selected=selected,
        archive_sha256=sha(HERE/"search-16102-full.py"),
        runner_sha256=sha(Path(__file__)),
        solver=a.solver,timeout=a.timeout,
        premise="two_fork_handoff.md: paper reduction, not Lean checked"),indent=2)+"\n")
    results=[]
    for i in selected:
        r=run_job(archive,jobs[i],i,a.out,a);results.append(r)
        print(json.dumps(r),flush=True)
        if r.get("result")=="SAT":break
    complete=(len(results)==22 and all(r.get("independently_verified") for r in results))
    print(json.dumps(dict(all_22_CNF_shards_independently_verified=complete,
                          lean_encoding_soundness_checked=False,
                          upstream_closed=False)),flush=True)

if __name__=="__main__":
    main()

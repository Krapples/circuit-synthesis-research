"""Capture and replay bounded regional queries and matched layout searches."""

import argparse
from _thread import interrupt_main
from collections import Counter
from functools import partial
import json
from pathlib import Path
from random import Random
from threading import Event, Thread
from time import perf_counter

from regional_completion_check import check_tree, make_completion, record_call
from module_contraction import simplify, vars as truth_variables
from port_certificates_check import bounded
from signed_bound_compare import cases, restrict_essential


MODES = ('dominance-branches', 'port-first', 'witness-cover', 'port-first-witness')
CORPUS = (('comparator-09', 5), ('random-monotone-10', 4), ('comparator-02', 5),
          ('graph-03', 4), ('comparator-04', 5))


def corpus_work():
    frozen = {name: (n, target) for name, _, n, target in cases()}
    for name, excess in CORPUS:
        n, target, _ = restrict_essential(*frozen[name])
        n, target, _ = simplify(n, target, False)
        yield name, n, target, excess, False, 'layout'


def timed(seconds, job, on_timeout):
    """Return partial metrics on Windows and let the parent enforce a hard cap."""
    done = Event()

    def alarm():
        if not done.wait(seconds):
            interrupt_main()

    timer = Thread(target=alarm, daemon=True)
    try:
        timer.start()
        return job()
    except KeyboardInterrupt:
        return {'status': 'TIMEOUT', **on_timeout()}
    finally:
        done.set()
        timer.join()


class Capture:
    def __init__(self, completion):
        self.completion = completion
        self.metrics = completion.metrics
        self.current = self.first = self.slowest = None
        self.calls = 0

    def __call__(self, m, ports, patterns, targets, signed):
        self.calls += 1
        self.current = dict(sequence=self.calls, query=(m, ports, patterns, targets, signed))
        if self.first is None:
            self.first = self.current
        started = perf_counter()
        answer = self.completion(m, ports, patterns, targets, signed)
        self.current.update(seconds=perf_counter() - started, status='SAT' if answer is not None else 'UNSAT')
        if self.slowest is None or self.current['seconds'] > self.slowest['seconds']:
            self.slowest = self.current
        self.current = None
        return answer

    def records(self):
        selected = {}
        for role, record in (('first', self.first), ('slowest-completed', self.slowest), ('in-flight', self.current)):
            if record is None:
                continue
            entry = selected.setdefault(record['sequence'], {**record, 'roles': []})
            entry['roles'].append(role)
        return list(selected.values())


def layout_job(work, mode, seconds, capture=False, input_symmetry=False):
    stats = Counter()
    completion = make_completion(mode)
    if capture:
        completion = Capture(completion)
    job = partial(record_call, work, mode, completion, stats, input_symmetry=input_symmetry)

    def snapshot():
        return dict(cache=completion.metrics(), stats=stats)

    result = timed(seconds, job, snapshot)
    if capture:
        result['calls'] = completion.records()
    return result


def regional_job(query, mode, seconds):
    m, ports, pats, targets, signed = query
    completion = make_completion(mode)

    def job():
        witness = completion(m, ports, pats, targets, signed)
        if witness is not None:
            check_tree(witness, m, ports, pats, targets, signed)
        return dict(status='SAT' if witness is not None else 'UNSAT', cache=completion.metrics(), witness=witness)

    return timed(seconds, job, lambda: dict(cache=completion.metrics()))


def instances(large):
    """The supplied generator with the same seed and row perturbations."""
    rng = Random(3892)
    for signed in (False, True):
        for j in range(20):
            m = 4 + j % 3 if large else (2 if j % 2 else 1)
            q = (3 if large else 5) + j % 3
            ports = tuple(range(q))
            pats = tuple(sorted(rng.sample(range(1 << q), min(16, 1 << q))))
            width = 1 << m
            small = (1 << width) - 1
            full = (1 << (len(pats) * width)) - 1
            cols = [sum(v << (k * width) for k in range(len(pats))) for v in truth_variables(m)]
            cols += [sum((small if p >> i & 1 else 0) << (k * width) for k, p in enumerate(pats)) for i in ports]
            cols = [v ^ (full if signed and rng.randrange(2) else 0) for v in cols]
            while len(cols) > 1:
                a = cols.pop(rng.randrange(len(cols)))
                b = cols.pop(rng.randrange(len(cols)))
                cols.append(a & b if rng.randrange(2) else a | b)
            targets = [(cols[0] >> (k * width)) & small for k in range(len(pats))]
            if j % 2:
                targets[rng.randrange(len(pats))] ^= 1 << rng.randrange(width)
            yield j, (m, ports, pats, tuple(targets), signed), j % 2 == 0


def stress_batch(work, mode, seconds):
    results = []
    for j, query, known in work:
        started = perf_counter()
        result = regional_job(query, mode, seconds)
        if known and result['status'] == 'UNSAT':
            raise AssertionError('rejected a generated witness')
        results.append(dict(case=j, m=query[0], signed=query[-1], known_sat=known,
                            seconds=perf_counter() - started, **result))
    return dict(status='OK', jobs=results)


def run(args, emit):
    modes = args.modes or MODES
    if args.experiment == 'stress':
        work = list(instances(args.large))
        expected = {}
        for mode in modes:
            for signed in (False, True):
                sample = [job for job in work if job[1][-1] == signed]
                result = bounded(stress_batch, (sample, mode, args.seconds), len(sample) * (args.seconds + .1) + 1)
                for job in result.get('jobs', ()):
                    key = signed, job['case']
                    if job['status'] != 'TIMEOUT':
                        assert expected.setdefault(key, job['status']) == job['status']
                emit(dict(mode=mode, signed=signed, **result))
        return

    expected = {}
    if args.experiment == 'isolated':
        if args.source is None:
            raise ValueError('isolated replay requires --source from capture')
        with args.source.open(encoding='utf-8') as stream:
            records = [json.loads(line) for line in stream]
        for record in records:
            if record['kind'] != 'capture':
                continue
            for call in record['calls']:
                for mode in modes:
                    result = bounded(regional_job, (call['query'], mode, args.seconds), args.seconds + 1)
                    if result['status'] != 'TIMEOUT':
                        key = record['case'], call['sequence']
                        verdict = expected.setdefault(key, call.get('status', result['status']))
                        assert verdict == result['status']
                    emit(dict(case=record['case'], sequence=call['sequence'], roles=call['roles'], mode=mode, **result))
        return

    capture = args.experiment == 'capture'
    for work in corpus_work():
        if args.cases and work[0] not in args.cases:
            continue
        for mode in MODES[:1] if capture else modes:
            result = bounded(layout_job, (work, mode, args.seconds, capture, args.input_symmetry), args.seconds + 1)
            if result['status'] != 'TIMEOUT':
                assert expected.setdefault(work[0], result['status']) == result['status']
            result.update(case=work[0], n=work[1], truth=hex(work[2]), excess=work[3], mode=mode,
                          input_symmetry=args.input_symmetry)
            emit(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('experiment', choices=('capture', 'isolated', 'layout', 'stress'))
    parser.add_argument('--source', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=float, required=True)
    parser.add_argument('--modes', choices=MODES, nargs='+')
    parser.add_argument('--large', action='store_true')
    parser.add_argument('--case', dest='cases', choices=tuple(name for name, _ in CORPUS), action='append')
    parser.add_argument('--input-symmetry', action='store_true')
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error('seconds must be positive')
    with args.output.open('x', encoding='utf-8') as stream:
        def emit(record):
            line = json.dumps(dict(kind=args.experiment, cap=args.seconds, **record), sort_keys=True)
            stream.write(line + '\n')
            stream.flush()
            print(line, flush=True)

        run(args, emit)


if __name__ == '__main__':
    main()

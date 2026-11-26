# Research workflow

Run commands from the repository root with Python 3.11 or later. The SAT adapter uses the
existing `cube_search.py` and independent `verify/manifest.py`. The administrative commands use
the existing authenticated `gh`, Git, and pinned Lean installations.

## Start or resume a research step

```powershell
python -B sat-search/workflow/research.py status --task L-meta-4653
python -B sat-search/workflow/research.py record --task L-meta-4653 --kind lean_checked --scope 'PG(2,4), monotone, OR-only budget 103, independent centers' --summary 'Lean checked the independent-center lower bound of 104 OR gates.' --open-obligation 'Prove the bound with unrestricted centers.' --next 'Analyze the forest projection.' --artifact sat-search/results/pg4_or_4653/README.md
```

Check the topic notes and previous evidence before proposing a run. Give each batch a decision to
inform and use an analytical bound or an independent small check to narrow the search when
possible. Add `--job` for active run IDs, `--lease-state` for a redacted status, and `--metrics`
for a JSON measurement record when available. Useful measurement fields include model calls,
uncached input tokens, output tokens, tool-result bytes, and verified progress. Use an existing
baseline and leave unavailable fields empty or null. Record the scope and strongest checked
result at meaningful milestones and link durable evidence from `RESEARCH_NOTES.md`. Local
`.research` survives context compaction. Keep archival proofs and reproducible records under
`sat-search/results` for handoffs to other machines.

## Run a bounded experiment

`research-batch/1` manifests contain a `decision` and a `jobs` list. Use
[smoke-batch.json](smoke-batch.json) as a whole-graph example. Every job has a unique `id` and
declares its scope, worker and memory estimates, and timeout policy. Start with a diagnostic
cap. The `timeout` fields are `initial`, `maximum`, and optional `factor` (default 2). On a
later invocation the runner records the previous open attempt and raises the cap up to the
ceiling. Review prior output before that invocation. Use `--repeat-reason` for an intentional
rerun with a completed record or exhausted cap. A cache entry with missing evidence requires
an explicit reason before replacement.

```powershell
python -B sat-search/workflow/research.py run sat-search/workflow/smoke-batch.json --workers 22
```

- `kind: cube` accepts `n`, `edges`, `size`, `basis` (`monotone` or `general`), optional `solver`
  and optional Boolean `symmetry` in `query`. This is the solver's whole-graph exact-total-gate
  model with essential inputs. It does not encode OR-only budgets, pinned gates, disconnected
  circuit padding, prescribed vertex roles, partial labels, or specialized pruning scopes.
- `kind: command` accepts literal `argv`, optional workspace-relative `cwd`, and `query`
  metadata. Use it for scoped solver jobs or another reusable experiment command. Set `cache`
  to `true` for deterministic commands and list all effective source, input, configuration and
  runtime files in `inputs`. Declare relevant non-secret variables in `environment_keys`.
  Keep credentials out of experiment arguments, inputs, and output. Generic command success is
  execution evidence. Verify and record its mathematical result with the scoped checker.
- `canonicalize graph.json` takes `n`, `edges`, and optional string `colors` and returns the
  vertex map. Exact canonicalization may fall back to the original labeling at its search
  bound. The cache can then miss equivalent labelings while keeping results sound. A graph cache
  hit retains its original evidence and records the current input map in `jobs.jsonl`. Translate
  primary-input references back through the inverse map and independently check a witness before
  using it under the original labels. Internal gate references stay as recorded.
- The run ledger reserves CPU slots and estimated memory across batches sharing the default
  state directory. Worker slots default to the lesser of 22 and available CPUs. Use `--workers`
  and `--memory-mib` to set budgets for the machine and specify job `workers` and `memory_mib`
  for unusual workloads. Memory reservations are admission estimates. Record measured peak RSS
  separately when comparing memory. The verification allowance and graceful shutdown can add
  time beyond the solver cap.

The default output is one JSON summary with wall time, summed job and solver-cube times,
duplicate counts, timeout rate, and up to three bounded actionable excerpts. `--verbose` adds
per-job console records. Each batch directory contains its manifest metadata, `jobs.jsonl`, and
`summary.json`. Each attempt directory holds `request.json`, `result.json`, complete `stdout.log`
and `stderr.log`, and the available solver and verification evidence. Terminal entries keep
their original scope and grade. `verified_sat` requires independent witness evaluation.
`solver_unsat` records a complete solver verdict at rule-dependent evidence grade. A timeout,
interruption, or incomplete search leaves its scope open. Cache hits do not change any of these
grades. The runner does not import historical experiments. Consult their documented coverage
before scheduling fresh experiments. Partial output is retained, with no automatic carry-over
of cube exclusions. For long studies use individually bounded, independently checked shards.

Run independent jobs in a background terminal or command session and retrieve the summary when
needed. For PowerShell, from the workspace root:

```powershell
New-Item -ItemType Directory -Force .research | Out-Null
Start-Process -FilePath (Get-Command python).Source -ArgumentList '-B','sat-search/workflow/research.py','run','sat-search/workflow/smoke-batch.json','--workers','22' -WorkingDirectory $PWD.Path -WindowStyle Hidden -RedirectStandardOutput .research/batch.out -RedirectStandardError .research/batch.err -PassThru
```

Use distinct redirect names for concurrent launches. A normal interrupt stops new scheduling,
asks the cube process to stop, and uses a bounded process-tree shutdown when necessary. After
an abrupt runner exit, `recover <attempt> --reason '…'` can retire a reservation on its original
host after recorded processes exit. Confirm the old worker tree is gone first. The command
preserves raw output and records an interrupted attempt.

## Keep administration separate

```powershell
python -B sat-search/workflow/research.py lean sat-search/lean --source sat-search/lean/AxiomsCheck.lean --timeout 90
python -B sat-search/workflow/research.py lean sat-search/lean --module CircuitLemmas --timeout 300
python -B sat-search/workflow/research.py pr 22538 --watch
python -B sat-search/workflow/research.py normalize path/to/selected-source.lean
python -B sat-search/workflow/research.py checkpoint path/to/selected-source.lean
```

- `lean` records the toolchain and Lake lockfiles and uses the project's incremental `.lake`
  dependencies. A source check still runs Lean. Keep Lake's caches in their matching workspace
  and use the official checker, permitted dependencies, axiom restrictions, and exact submitted
  commit verification for project submissions.
- Start `heartbeat <private-lease-file>` in a background terminal for a new lease, once per step.
  It checks upstream STOP, retries transient failures, and records redacted renewals separately
  from research results. Use an already healthy watcher for an active lease. The local stop file
  is `<step>.heartbeat-stop` beside the lease file. After a crash, check the lock's host and PID
  before removing a stale lock and restarting. Keep lease files private and use the project
  rules for claiming, submitting and releasing steps.
- `pr` queries project PRs through the authenticated CLI, stores selected metadata and bot
  verdicts, and emits only state changes in watch mode. Acceptance and merge are separate states.
- `checkpoint` normalizes the explicit text paths to UTF-8 with LF, stages them, and saves the
  staged diff and its whitespace check. Review the diff before using `--message` to create a
  focused local commit. The project submission and push workflow remains explicit.

Run the workflow regressions with `python -B -m unittest discover -s sat-search/workflow -p 'test_*.py' -v`.

The initial Windows validation used the existing 22-worker backend and Lean 4.36.0. The smoke
batch independently verified one two-gate path witness and reused it for the relabeled path
(1.328 s wall, 1.253 s summed job time, zero timeouts). After the runner changes, a cache-only
pass skipped both completed test entries in 0.022 s. The existing `AxiomsCheck.lean` completed
through the Lake wrapper in 33.676 s. The project PR check independently reported PR #22538 as
open with intake acceptance. The existing L-meta-4653 heartbeat continued throughout. Model
call, uncached-token, and tool-result-byte totals were unavailable for this milestone.

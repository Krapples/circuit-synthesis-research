# Research direction

Current priorities and closed directions. [AGENTS.md](../../AGENTS.md) holds the always-on rules.

## Priorities

Complete-function FPT synthesis, counted-NOT and nonmonotone synthesis, affine certificate
reconstruction, construction upper bounds, and hybrids with SAT. Audit proofs separately from the
prototypes that motivated them. Confirm a candidate with small independent enumeration or a formal
proof before making an asymptotic claim. Prefer general, mathematically motivated methods to
instance-specific rules, GPU work, repeated benchmark replays, or longer caps.

## Closed directions and what would reopen them

- The guarded family closes the universal `rank(H) <= 2e` direction.
- Sharing-only FPT for arbitrary partial labels: reopen only with a new restriction that addresses
  the known hardness.
- Explicit enumeration superseded by certificate completion: archived.
- Provider matching, exact rectangle allocation, capacity refinements: reopen on evidence of
  stronger whole-function bounds or an end-to-end benefit.
- SAT propagation changes: reopen with a measurable effect or a new sound pruning argument.

When closing a direction, record why and what result would justify reopening it.

## Current state

PR **#2707** (`feat(Ch5 #2700): Wall 3 R2.a — twistedPolytabloid_per_q_decomp
(extract Q_low ∪ Q_eq via IH, isolate residual Δ)`) merged in cycle
`810f89dc` (commit `6a918da`). Net diff: +313 / -0 across two files
(the second is its own progress handoff).

All changes are in
`EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`. The
PR closes #2700 (the R2.a deliverable from the Wall 3 R2 split
filed in cycle `810f89dc`). It introduces `twistedPolytabloid_per_q_decomp`
together with the inner-induction machinery that extracts the
`Q_low ∪ Q_eq` part of the twisted polytabloid sum using the outer
induction hypothesis on `srRank`, leaving the residual Δ for R2.b
(#2702) to handle.

The PR has not yet been audited. R2.b (#2702) and R2.c (#2703) are
both downstream consumers — getting the R2.a foundation right is
on the critical path for Wall 3.

## Deliverables

A review comment on PR #2707's commit (`6a918da` on `main`) posted
as a comment on this issue, with one of these verdicts:

1. **PASS** — the decomposition is mathematically sound, the
   inductive structure on `srRank` is correctly wired, and the
   residual Δ that R2.b will receive has the expected shape.
2. **PASS WITH FOLLOWUP** — same, but with specific cleanup items
   filed as new issues.
3. **FAIL** — list concrete problems that need a fix PR before R2.b
   (#2702) can proceed.

## Context

Read in order:

1. **PR #2707** diff:
   `gh pr diff 2707` (or
   `git show 6a918da -- EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`).
2. **Worker handoff**: `progress/20260504T083919Z_e2f6d440.md`
   (session `e2f6d440`, the cycle that produced #2707).
3. **The book's argument**:
   `blobs/Chapter5/SpechtModuleBasis.md` (the R2 paragraph) for the
   intended decomposition; cross-reference
   `blobs/Chapter5/PolyTabloid.md` (or whichever blob carries the
   q-orbit / Q_low / Q_eq language) for the index-set conventions.
4. **R2 ancestry**:
   - **R2.a target** spec: issue #2700 (now closed by this PR).
   - **R2.b downstream**: issue #2702
     (`twistedPolytabloid_residual_in_V` — consumes Δ).
   - **R2.c downstream**: issue #2703
     (`garnir_twisted_in_lower_span` final assembly).
   - **R1 sibling**: PR #2669 + #2670 (audited PASS by #2671).
5. **Q-high meditate notes**:
   `progress/q-high-involution.md` §5 documents the inner-induction
   strategy that R2.a should be implementing — verify the file
   matches.

## Verification

- [ ] **Targeted build**:
      `lake build EtingofRepresentationTheory.Chapter5.SpechtModuleBasis`
      finishes with no errors. The file may still carry sorries
      from R2.b / R2.c (those are different theorems); the audit is
      about whether the additions in #2707 are clean.
- [ ] **Sorry inventory**:
      `grep -nE '^\s*sorry|^\s*by sorry|:=\s*sorry|by\s+sorry' EtingofRepresentationTheory/Chapter5/SpechtModuleBasis.lean`
      should show only the pre-existing pair of Wall 3 sorries
      (`garnir_twisted_in_lower_span`, `twistedPolytabloid_pigeonhole_pair`)
      plus whatever the residual `twistedPolytabloid_residual_in_V`
      sorry is that R2.b will close. The new
      `twistedPolytabloid_per_q_decomp` itself must be `sorry`-free.
- [ ] **No `def`/`instance`/`abbrev` body is `sorry`** (project rule).
- [ ] **Inner induction on `srRank`** is correctly structured. In
      particular: the base case (`srRank = 0` or whatever the
      degenerate case is) must be proved, and the step case must
      actually use the outer IH at a strictly smaller `srRank`. A
      proof that pretends to recurse but doesn't decrease the
      measure is a FAIL.
- [ ] **The Q_low / Q_eq / Q_high partition** matches the book's
      conventions (and matches what `pigeonhole_pair` and the rest
      of Wall 3 already assume).
- [ ] **The residual Δ that R2.b will receive** has the shape that
      issue #2702's statement claims (lives in `V`, well-defined
      from the partition, no hidden dependency on undischarged
      assumptions).
- [ ] **No new universe instabilities / typeclass diamonds /
      `noncomputable` blow-ups** in the upstream file. Heartbeat
      bumps, if any, should be the minimum needed.
- [ ] **Naming convention consistency** with the existing
      `SpechtModuleBasis` lemmas (`twistedPolytabloid_*`,
      `polytabloid_*`).

If the audit passes, comment "PASS" on this issue and close it. If
followups are needed, file them as separate issues and cite the
numbers. If it fails, file a fix issue and link it — Wall 3 R2.b
(#2702) is sitting in the queue and will consume this work soon.

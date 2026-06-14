## Current state

PR **#2706** (`feat(Ch5 #2612): close schurModule_isSimple via C-4b
transfer (1 sorry pending C-4a aggregation)`) merged in cycle
`810f89dc` (commit `0ed49c7`). It introduced a new file
`EtingofRepresentationTheory/Chapter5/SchurModuleSimple.lean` (180
lines) plus an import in `Chapter5.lean`. Net diff: +296 / -0 across
three files (the third is its own progress handoff). The PR closes
the C-4c assembly target from #2612 modulo one well-localised sorry
that is now tracked by **#2708** (C-4a aggregation, currently
`blocked`).

The PR has not yet been audited. The companion C-4 review #2705
(filed cycle `bab8e3ff`) covers PR #2697 (β.2 Specht bridge) and
PR #2698 (C-4a-ii body) only; it does **not** cover #2706.

## Deliverables

A review comment on PR #2706's commit (now `0ed49c7` on `main`)
posted as a comment on this issue, with one of these verdicts:

1. **PASS** — proofs are sound, no hidden mathematical gaps, the
   single tracked sorry at `SchurModuleSimple.lean:148` is genuinely
   the C-4a aggregation hole and not a workaround for a deeper
   problem.
2. **PASS WITH FOLLOWUP** — same, but with specific cleanup items
   that the reviewer files as new issues (cite issue numbers).
3. **FAIL** — list concrete problems that need a fix PR before
   downstream work (#2708, #2493, #2482, #2483) can rely on this
   foundation.

## Context

Read in order:

1. **PR #2706** diff:
   `gh pr diff 2706` (or
   `git show 0ed49c7 -- EtingofRepresentationTheory/Chapter5/SchurModuleSimple.lean`).
2. **Worker handoff**: `progress/20260504T082119Z_a1a48844.md`
   (session `a1a48844`, the cycle that produced #2706). Records why
   one sorry was left and how it should aggregate.
3. **The single sorry**: `SchurModuleSimple.lean:148` —
   `schurModuleSubmodule_isSimple_centralizer`. Its statement is the
   aggregated C-4a obligation; #2708 is the follow-up that discharges
   it via `image_of_primitive_idempotent_isSimple_centralizer`
   (`PrimitiveIdempotentSimplicity.lean:220`).
4. **C-4b dependency**:
   `EtingofRepresentationTheory/Chapter5/SchurWeylGLTransfer.lean`,
   specifically `isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`
   — already audited PASS by #2691.
5. **The book's argument** (for sanity-checking the structure of the
   transfer): `blobs/Chapter5/Theorem5_22_1.md`, the C-4c paragraph.

## Verification

Targeted checks (please walk through these explicitly in the
verdict):

- [ ] **The new file builds**:
      `lake build EtingofRepresentationTheory.Chapter5.SchurModuleSimple`
      finishes with no errors or warnings (apart from the one
      expected `declaration uses 'sorry'`).
- [ ] **Sorry inventory**: `grep -nE '^\s*sorry|^\s*by sorry|:=\s*sorry|by\s+sorry' EtingofRepresentationTheory/Chapter5/SchurModuleSimple.lean`
      should return exactly one hit, at line 148, inside
      `schurModuleSubmodule_isSimple_centralizer`. Any other sorry
      (including inside `where` clauses, instance bodies, or proof
      obligations of `def`) is a FAIL.
- [ ] **No `def`/`instance`/`abbrev` body is `sorry`** (per the
      project rule "Definitions Must Be Constructed"). The
      `schurModuleSubmodule_diagonalActionImage_smul` and
      `schurModuleSubmodule_diagonalActionImage_module` instances in
      particular must be fully constructed.
- [ ] **`schurModuleSubmodule_smul_mem_aux`** correctly uses
      `diagonalActionImage_le_centralizer_symGroupImage` and
      `symGroupAlgHom_range` — verify the centralizer direction
      (it's the diagonal action that lives in the centralizer of
      `symGroupImage`, not the other way around) and that the
      commutation `youngSymEndo * b.val = b.val * youngSymEndo` is
      applied to the correct side.
- [ ] **The C-4c assembly `schurModule_isSimple`** correctly
      composes C-4a (sorry placeholder) with C-4b
      (`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple`).
      Sanity-check: the conclusion type is
      `IsSimpleModule (MonoidAlgebra k (GL (Fin N) k)) (SchurModule k N λ)`
      — verify the module structure matches what downstream consumers
      (#2493, #2482, #2483) will expect.
- [ ] **The sorry's hypotheses match what #2708 will provide**:
      `hf_zero`, `hf_block`, `hπ_idem`, `hπ_rank`, `hπ_special` (or
      whatever the exact names are in the file). Confirm the
      anticipated aggregation in #2708 can actually discharge this
      sorry without re-stating the lemma.
- [ ] **No silent `axiom`, `extend`, `@[simp]` order tricks, or
      type-class diamond hacks** introduced.
- [ ] **Heartbeat bumps**: if `maxHeartbeats` or
      `synthInstance.maxHeartbeats` was raised, confirm it's the
      minimum needed and document why (in the review comment).

If the audit passes, comment "PASS" on this issue and close it. If
followups are needed, file them as separate issues and cite the
numbers. If it fails, file a fix issue and link it.

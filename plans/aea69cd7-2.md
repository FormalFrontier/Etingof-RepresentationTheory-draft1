## Current state

Wave 62 landed PR #2912 (commit `ca2ce6e`, closes #2910) which added
`single_branch_leaf_both_extend_t122_per_kQ` at
`Chapter6/FieldGenericTpqr.lean:64`. It is the largest unaudited PR
from the wave (+531 lines / 2 files — by far the biggest of the
five wave-62 ports that landed without a dedicated review). The
helper handles the T(1, 2, 2) = D₅ sub-case of the
`single_branch_leaf_both_extend_per_kQ` dispatcher: when the single
degree-3 vertex `v₀` has a leaf and two arms each of length 2 ending
in leaves `b₂` and `b₃`, the Cartan form is positive definite, which
contradicts the assumed `h_not_posdef`. The proof is a port of the
universal T(1,2,2) posdef contradiction at
`Chapter6/InfiniteTypeConstructions.lean:7964-8352` (~390 lines of
quadratic-form expansion + `nlinarith` closing argument over six
named vertices).

The helper is currently dead weight in the literal sense — no
existing call site (`Grep "single_branch_leaf_both_extend_t122_per_kQ"`
returns only the definition) — but it is wired in by the
`single_branch_leaf_both_extend_per_kQ` dispatch that follows from
PR #2906 once the both-extend stub is filled. Auditing now (before
the dispatcher closes) is the right time: it isolates the audit
boundary to the T(1, 2, 2) posdef proof and lets later dispatcher
audits focus on the dispatch logic alone.

The helper carries `(F : Type) [Field F] [IsAlgClosed F]` plus
`(Q : @Quiver.{0,0} (Fin n))` and `hOrient` for API uniformity with
the sibling per-(F, Q) leaves, but the body explicitly notes that
`F`, `Q`, `hOrient` are not used substantively in this case (the
contradiction lives entirely at the level of integer-coefficient
positive-definiteness) — they are absorbed via
`let _ := F; let _ := Q; let _ := hOrient`.

No review has been filed for this helper. Given the size (~390 lines
of substantive math) and the future role (consumed by the
single-branch dispatcher closing soon), a dedicated fidelity audit
is warranted.

## Deliverables

Audit `single_branch_leaf_both_extend_t122_per_kQ`
(`Chapter6/FieldGenericTpqr.lean:64-…`) against the universal T(1,2,2)
posdef proof
(`Chapter6/InfiniteTypeConstructions.lean:7964-8352`). Five
deliverables. Write the audit report to
`progress/reviews/2026-05-19-t122-leaf-both-extend-per-kQ.md` using
the standard PASS / FAIL-with-fix-recommendations verdict structure.

1. **Signature fidelity.** Verify the helper takes the same six
   named vertices as the universal proof
   (`v₀, leaf, a₂, a₃, b₂, b₃`) and the same adjacency hypotheses
   (`h_leaf_adj`, `ha₂_adj`, `ha₃_adj`, `hb₂_adj`, `hb₃_adj`),
   degree hypotheses (`h_leaf_deg`, `hb₂_deg1`, `hb₃_deg1`), and
   distinctness hypotheses (`ha₂₃`, `ha₂_ne_leaf`, `ha₃_ne_leaf`,
   `hb₂_ne_v₀`, `hb₃_ne_v₀`), plus the three `Finset` equalities
   (`hS₀_eq`, `hb₂_eq`, `hb₃_eq`) that pin the neighbor lists. Plus
   `h_not_posdef`, `hconn`, `h_acyclic`, the standard adjacency
   bundle (`hsymm`, `hdiag`, `h01`), and the per-(F, Q) carriage
   `(F : Type) [Field F] [IsAlgClosed F] (Q : …) [Subsingleton …]
   (hOrient : …)`.
   * Confirm no degree hypothesis was silently dropped.
   * Confirm the three Finset-equalities match what the universal
     proof actually uses (the universal proof derives them via
     `hS₀_eq`, `hb₂_eq`, `hb₃_eq` from the dispatcher's context, so
     they should be hypotheses here too — not re-derived inside the
     body).
   * Confirm `[IsAlgClosed F]` is present (consistent with the
     other per-(F, Q) leaves in `FieldGenericTpqr.lean` even though
     the body does not use it). Note this is the opposite of the
     cycle-wrapper case (#2897); both decisions need to be coherent
     with the outer assembly's typeclass propagation.

2. **Quadratic form expansion fidelity.** The universal proof
   constructs the six-vertex quadratic form via named scalars
   `V, L, A₂, B₂, A₃, B₃` (or equivalent), expands
   `dotProduct x ((2•1 - adj).mulVec x)` symbolically, and closes
   via `nlinarith` after rewriting as a sum of squares. Verify the
   per-(F, Q) port:
   * Uses the *same* variable names (or documents any rename).
   * Uses the *same* expansion structure — same number of square
     terms, same coefficient grouping, same key `have`s.
   * Closes via the *same* tactic (`nlinarith` with the same
     `sq_nonneg` hints, or `linear_combination` if substituted).
   * No `simp` argument was added or removed that materially
     changes the normal form of the quadratic.

3. **Sum-of-squares closure fidelity.** The universal proof derives
   `B₃ = 0`, `A₃ = 0`, `B₂ = 0`, `A₂ = 0`, `L = 0`, `V = 0` in that
   order via `nlinarith` calls (each one peeling off one variable
   from the sum-of-squares decomposition). Verify the per-(F, Q)
   port preserves this *exact* peeling order — reordering would
   work but would make later side-by-side debugging harder if the
   universal proof ever needs to be edited. Then the final
   `apply hx; ext i; rcases h_all_named i with rfl | … | rfl` block
   must match the universal's case-list exactly.

4. **Neighbor-list lemma fidelity.** The universal proof derives
   six `_nbrs` lemmas (`hv₀_nbrs`, `hleaf_nbrs`, `ha₂_nbrs`,
   `ha₃_nbrs`, `hb₂_nbrs`, `hb₃_nbrs`) that constrain each vertex's
   adjacency outside the named six. Verify the per-(F, Q) port:
   * Has all six lemmas (none dropped, none merged into a different
     shape).
   * Derives each from the matching hypothesis (`hS₀_eq` for
     `hv₀_nbrs`, `hleaf_deg` for `hleaf_nbrs`, etc.) via the same
     pigeonhole argument as the universal.
   * Crucially: the per-(F, Q) port should NOT introduce any
     additional helper lemmas that the universal omits — those
     would indicate the reviewer of the original universal proof
     missed something, which would deserve a separate ticket
     against the universal.

5. **Carriage discharge.** Confirm `F`, `Q`, `hOrient` are
   explicitly absorbed by
   `let _ := F; let _ := Q; let _ := hOrient` (or an `_root_`
   suppression pattern) at the top of the body, and that they are
   not used anywhere downstream. The helper's docstring (lines 60-64
   per the `Read` excerpt) already claims this — verify the body
   matches the docstring.

If FAIL on any deliverable, file a fix issue and link it in the
report. If PASS, no code changes.

## Context

- Audit target:
  `Chapter6/FieldGenericTpqr.lean:64` —
  `single_branch_leaf_both_extend_t122_per_kQ`.
  Body spans roughly lines 64-590 (verify exact end via
  `Grep "^theorem \|^@\["` immediately after).
- Universal reference:
  `Chapter6/InfiniteTypeConstructions.lean:7964-8352` — universal
  T(1,2,2) posdef contradiction, inline inside the universal
  `single_branch_leaf_both_extend_…` dispatcher (no standalone
  universal theorem yet).
- Sibling per-(F, Q) leaves for stylistic comparison (same file):
  `single_branch_leaf_both_extend_b3leaf_per_kQ` (T(1, q, 2)
  partial, PR #2914), `single_branch_leaf_both_extend_b2leaf_per_kQ`
  (T(1, 2, r) partial, PR #2916). These use the
  `embed_t125_in_tree_per_kQ` shared helper for dispatch; T(1,2,2)
  does not because the case is closed by contradiction with
  posdef rather than embedding.
- Pattern reference (most recent substantive audit):
  `progress/reviews/2026-05-19-embed-t125-in-tree-per-kQ.md` (PR
  #2931 = #2928 closure). Same audit depth expected.
- Future call site: the
  `single_branch_leaf_both_extend_per_kQ` dispatcher (not yet
  closed; tracked by #2905 chain). The dispatcher will call
  `single_branch_leaf_both_extend_t122_per_kQ` in the
  `arm₂_deg1 ∧ arm₃_deg1` branch.
- Out of scope: the sibling T(1, q, 2) / T(1, 2, r) /
  Ẽ₇ (arms ≥ 3) helpers — they have their own audit issues
  (existing #2928, plus the wave-62 partials at #2914/#2916 may
  warrant separate reviews if the planner queues them).

## Verification

- Audit report posted at
  `progress/reviews/2026-05-19-t122-leaf-both-extend-per-kQ.md`
  with explicit per-deliverable verdict and supporting line
  references.
- For each of the five deliverables, either:
  * PASS with a concrete line-pair citation showing the per-(F, Q)
    text mirrors the universal text (modulo the documented
    carriage of `F`, `Q`, `hOrient`); or
  * FAIL with a fix issue filed and linked.
- The audit explicitly addresses the
  `let _ := F; let _ := Q; let _ := hOrient` carriage-discharge
  pattern, because this is the first wave-62 helper to use it
  visibly (other per-(F, Q) leaves *do* use `F`, `Q`, `hOrient` in
  their proofs).
- No code changes from this audit unless a deliverable surfaces a
  blocking inconsistency — even then, file a fix issue rather
  than patching in this PR.

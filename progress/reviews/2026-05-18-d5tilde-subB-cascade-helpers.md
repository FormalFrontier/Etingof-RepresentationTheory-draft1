# Audit — D̃₅ Sub B cascade helpers (PRs #2835, #2843, #2854)

Issue: #2858 (review). Parent: #2804.
Auditor session: `50db6933`. Date: 2026-05-18 (UTC).

Scope: `EtingofRepresentationTheory/Chapter6/FieldGenericD5Tilde.lean`,
focused review window lines 215–810. ℂ-source comparison against
`Chapter6/InfiniteTypeConstructions.lean:1569-1834`.

Build status confirmed locally: 2 declarations use `sorry` (line 528
`d5tildeRep_kQ_leaf_equalities`, line 849 `d5tildeRep_kQ_isIndecomposable`),
6 raw `sorry` keywords (5 inside the 31-branch case-split at
802/804/806/808/810 + 1 at the API stub). Matches `progress/sorry-landscape.md`.

## Verdicts

| PR    | Verdict             |
|-------|---------------------|
| #2835 | PASS-with-followups |
| #2843 | PASS                |
| #2854 | PASS-with-followups |

Follow-ups filed (none block this audit landing; see Section 4):

- Refactor: hoist `embed_sum_zero_F` and `center_decomp_F` into
  `FieldGenericStar.lean`; replace the local `have embed_sum_zero` /
  `have center_decomp` in `starRepGen_isIndecomposable` with the
  public theorems.
- Refactor: hoist `core_F` / `core3_F` / `gamma_containment_F` from
  the local `have` inside the canonical-orientation branch to
  top-level theorems before #2853 starts, so the 8 canonical-leaf
  sub-cases share the proof instead of duplicating it.

## 1. PR #2835 (helpers + API stubs) — PASS-with-followups

### Q1 — `embed_sum_zero_F` (line 215)

Statement:
```
(h : starEmbed1_F F m x + starEmbed2_F F m y = 0) : x = 0 ∧ y = 0
```
**Correct.** Mirrors the local `have embed_sum_zero` at
`FieldGenericStar.lean:114-135` of `starRepGen_isIndecomposable`,
character-for-character. Used twice in this PR's downstream (inside
`core_F` and `core3_F`); the index-shift bookkeeping in the
second-block case (lines 227–236) goes through `omega` cleanly. The
statement is the one #2853's non-canonical branches will need:
disjointness of `starEmbed1_F` and `starEmbed2_F` at the center is
independent of which direction the leaf-center edges go.

**Follow-up (cleanup, non-blocking).** `embed_sum_zero` is now stated
two places: as the public theorem here, and as a local `have`
inside `starRepGen_isIndecomposable` in `FieldGenericStar.lean`. The
import direction (`FieldGenericD5Tilde` imports `FieldGenericStar`)
means the public version cannot be used from `starRepGen_isIndecomposable`
without first moving the public theorem upstream into
`FieldGenericStar.lean`. Worth doing once; isolated cleanup PR.

### Q2 — `center_decomp_F` (line 240)

Statement:
```
w = starEmbed1_F F m (starFirst_F F m w) + starEmbed2_F F m (starSecond_F F m w)
```
**Correct.** Block-decomposition of any `(Fin (2 * (m + 1)) → F)` vector
via the half-block projections. Mirrors the local `have center_decomp`
at `FieldGenericStar.lean:270-278`; same content, with the more uniform
spelling via `starFirst_F` / `starSecond_F` instead of the inline
`fun i => w ⟨i.val, _⟩` / `fun i => w ⟨m + 1 + i.val, _⟩`.

This shape is the one a `Wmain v + Wother v = ⊤` decomposition at v=2
or v=3 would want: given `w ∈ ⊤`, the projection pair `(P1 w, P2 w)`
gives the natural decomposition into the two `starEmbed_i_F` images.

Not directly invoked by the canonical-orientation proof body of PR #2854
(which uses `IsCompl.sup_eq_top` + `Submodule.mem_sup` directly inside
`core_F`/`core3_F` to get explicit decomposition witnesses). But it will
be needed for the non-canonical e02-/e12-reversed branches in #2853,
where the rep map at v=2 is the projection `starFirst_F` and we need to
express elements of W(2) as image-of-leaf, which is the reverse of the
canonical pushforward.

**Follow-up (cleanup, non-blocking).** Same as Q1: deduplicate with the
local `have` in `FieldGenericStar.lean:270-278`.

### Q3 — `gamma_from_embed1_F` (line 254) and `gamma_from_embed2_F` (line 278)

Statements:
```
gamma_from_embed1_F : d5tildeGamma_F F m (starEmbed1_F F m x) =
    starEmbed1_F F m x + starEmbed2_F F m x
gamma_from_embed2_F : d5tildeGamma_F F m (starEmbed2_F F m y) =
    starEmbed1_F F m y + starEmbed2_F F m (nilpotentShiftLinGen F m y)
```

**Correct.** Spot-checked against the ℂ-source inline proofs
`gamma_from_embed1` (`InfiniteTypeConstructions.lean:1711-1729`) and
`gamma_from_embed2` (`InfiniteTypeConstructions.lean:1732-1757`): the
case-split structure (`i < m + 1` vs `i ≥ m + 1`, then secondary
`i - (m + 1) + 1 < m + 1` split) and the dif/by_cases bookkeeping is
identical. Coefficient signs and shift indices match the ℂ-source
character-for-character; the only F-generic edits are renaming
`nilpotentShiftLin` → `nilpotentShiftLinGen`, and substituting the
F-generic `d5tildeGamma_F` / `starEmbed1_F` / `starEmbed2_F` for their
ℂ counterparts.

### Q4 — API stubs `d5tildeRep_kQ_leaf_equalities` (line 528) and `d5tildeRep_kQ_isIndecomposable` (line 849)

The leaf-equality stub takes `[Field F]` only. The indecomposability
stub additionally takes `[IsAlgClosed F]`. **Correct asymmetry.**

The leaf-equality theorem ultimately reduces to `compl_le_forces_eq`,
which only needs `Module.Finite F V` (automatic for `Fin (m+1) → F`).
Adding `IsAlgClosed F` here would be over-restrictive.

The indecomposability theorem will need to invoke
`nilpotent_invariant_compl_trivial_gen` (the F-generic analogue of the
ℂ-source's `nilpotent_invariant_compl_trivial` at
`InfiniteTypeConstructions.lean:1847`) on `nilpotentShiftLinGen`. That
lemma needs `IsAlgClosed F` for polynomial-factorisation reasons. So
the stub correctly anticipates the requirement.

Both stubs take `(hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)`
positionally; #2853 and #2851 will both `rcases hOrient.2.1 ...` over
the five edges. The structural alignment with the ℂ-source
`d5tildeRep_isIndecomposable` (uniformly canonical-orientation only)
plus the wave-60 cycle-rep pattern (`FieldGenericCycle.lean:189-235`)
gives high confidence the signature is right.

No follow-up needed on the typeclass surface.

## 2. PR #2843 (γ⁻¹ closed forms) — PASS

### Q5 — `cumTailSumLin_apply` / `_last` / `_succ` / `_oneSubNilp` (lines 337–435)

**Correct.** The four `cumTailSumLin` lemmas implement the
`M = (I - N)⁻¹` recursion faithfully:

- `_apply` (337) gives the closed form
  `M v i = Σ_{j ∈ univ, i.val ≤ j.val} v j` — the right-tail sum, which
  is the standard closed form of `(I - N)⁻¹` for the nilpotent shift
  `N` (the geometric series `I + N + N² + …` collapses because `N^{m+1} = 0`).

- `_last` (346) is the base case: at index `m`, the tail sum collapses
  to the single term `v ⟨m, _⟩`. The proof via `Finset.sum_eq_single`
  is the natural argument.

- `_succ` (361) is the recursion step at index `i` with `i + 1 < m + 1`:
  `M v ⟨i⟩ = v ⟨i⟩ + M v ⟨i + 1⟩`. Direction is **correct** —
  index `i + 1` carries the `v` value at `⟨i, _⟩` summand peeled off,
  matching the standard right-tail recursion. Cross-checked: in
  `_oneSubNilp` the inductive step rewrites with `_succ` at index `i'`
  and then `ih (i' + 1)`, which is the correct application order for the
  reverse induction on `m - i'`.

- `_oneSubNilp` (395) is the telescoping identity `M (v - N v) = v`,
  proved by reverse induction on `k = m - i.val`. The base case
  (`k = 0`, i.e. `i = m`) uses `_last` and the fact that `N v` at
  index `m` is zero (since `m + 1 = m + 1` violates the `< m + 1`
  guard). The inductive step expands `M (v - N v) ⟨i'⟩` via `_succ`,
  applies `ih` at `i' + 1`, and closes with `ring`. **Direction
  verified correct.**

### Q6 — `gammaInv_embed1_plus_embed2_F` (458) and `gammaInv_embed1_plus_embedNshift_F` (477)

Statements:
```
gammaInv_embed1_plus_embed2_F :
    d5tildeGammaInv_F F m (starEmbed1_F F m x + starEmbed2_F F m x) = starEmbed1_F F m x

gammaInv_embed1_plus_embedNshift_F :
    d5tildeGammaInv_F F m (starEmbed1_F F m y + starEmbed2_F F m (nilpotentShiftLinGen F m y)) =
      starEmbed2_F F m y
```

**Correct.** These collapse `d5tildeGammaInv_F` applied to the two
patterns produced by `gamma_from_embed1_F` / `gamma_from_embed2_F` back
to a single `starEmbed_i_F` term. They are the inverse identities
specifically tuned to the reversed-{2,3} edge case in #2853 at
`FieldGenericD5Tilde.lean:806`: the case-split needs
`d5tildeGammaInv_F (W₁(2)) ⊆ W₁(3)` where W₁(2) contains
`starEmbed1_F x + starEmbed2_F x` or
`starEmbed1_F y + starEmbed2_F (N y)` (the canonical-direction γ
pushes from `gamma_containment_F`). The two identities are exactly the
γ-inverse "reverses the canonical containment" facts.

Proof technique: `simp only [d5tildeGammaInv_F, …, LinearMap.add_apply,
LinearMap.comp_apply, LinearMap.sub_apply]` reduces `γ⁻¹` to its
constituent `starFirst_F`/`starSecond_F`/`cumTailSumLin` chain; then
`hP1`, `hP2` (computed via `starFirst_F_starEmbed*_F`,
`starSecond_F_starEmbed*_F` from `FieldGenericStar.lean:406-432`) feed
the algebra. The second identity uses `cumTailSumLin_oneSubNilp` to
collapse `M (y - N y) = y`. Clean and direct.

Index-shift convention cross-check vs case-split sorries (lines 802–810):
the reversed-{2,3} branch (line 806) is the only one that uses these
γ⁻¹ identities. Lines 802/804/808/810 handle reversed leaf edges and
will use `starFirst_F` / `starSecond_F` projection identities instead.
The split of γ-inverse work (this PR) from projection work (#2853) is
clean.

### Q7 — Heartbeat audit on PR #2843

**No `set_option maxHeartbeats` bumps introduced by this PR.** Grep
returns zero hits in `FieldGenericD5Tilde.lean` for `maxHeartbeats` or
`set_option`. The only heartbeat bump in the surrounding cascade is at
`FieldGenericStar.lean:101` (a 1.6M bump on
`starRepGen_isIndecomposable`, predating this PR and inherited from the
ℂ-source `starRep_isIndecomposable`).

No over-provisioning. No follow-up.

## 3. PR #2854 (canonical-orientation case) — PASS-with-followups

### Q8 — Local `have core_F` / `core3_F` / `gamma_containment_F` (lines 628, 676, 724)

The three local `have`s parameterise over arbitrary
`(Wmain, Wother)` so they can be applied both to `(W₁, W₂)` and
`(W₂, W₁)`. That parameterisation is **correct and necessary** —
without it the leaf-equality assembly cannot symmetrise.

**Follow-up (recommended, files a separate issue).** `core_F` and
`core3_F` are tied to the canonical leaf-center directions
(0→2, 1→2, 4→3, 5→3) by their hypothesis structure
(`x ∈ Wmain ⟨0⟩ → starEmbed1_F F m x ∈ Wmain ⟨2⟩`, etc.). They will
be reusable in #2853 only for sub-cases where all four leaf-center
edges are canonical — i.e. the 2 sub-cases under the
reversed-only-at-e23 branch (line 806). That's 8 of 31 = ~26% reuse.

For the remaining 23 sub-cases (any leaf-center edge reversed), the
direction-reversed analogues take pushes from the centre to the
leaf via `starFirst_F` / `starSecond_F`. These analogues should be
filed as a separate cleanup task:

- Hoist `core_F`, `core3_F`, `gamma_containment_F` from local `have`s
  to top-level theorems under `Section 5`.
- File a sibling lemma family for the projection-direction
  (`core_F_reversed_e02`, etc., or a uniformly parameterised
  `core_F_dir : ... (d : Direction) ...`).

This is a structural concern (reuse efficiency for #2853) but **not a
correctness defect** with #2854.

### Q9 — Match against ℂ-source proof

The canonical-orientation proof body (lines 559–800) mirrors the
ℂ-source `d5tildeRep_isIndecomposable` (lines 1569–1834 of
`InfiniteTypeConstructions.lean`) **line-for-line on the canonical
branch**. The structural deviation is the outer five-fold case-split on
edge direction (`rcases hOrient_edge ... with Or.inl | Or.inr` ×5,
each with a deepest-canonical `obtain ⟨a##⟩` extraction of the concrete
quiver arrow). The ℂ-source has no orientation-direction case-split
because it uses the canonical `d5tildeQuiver` only.

Within the canonical branch, the proof goes through five stages, all
mirrored from the ℂ-source:

1. Concretise the rep-map invariance hypotheses (`hW₁_02 .. hW₁_53`,
   `hW₂_02 .. hW₂_53`) via `simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h`.
   The ℂ-source obtains these by hand-applying the rep-map definition
   via `show @Quiver.Hom _ d5tildeQuiver ⟨a, _⟩ ⟨b, _⟩ from ⟨...⟩`.
   The F-generic version uses the orientation arrow witnesses obtained
   from `rcases` — strictly more uniform than the ℂ-source.
2. Establish `core_F` (v=2 decomposition under canonical 0→2, 1→2 pushes)
   — mirror of ℂ-source `core`.
3. Establish `core3_F` (v=3 decomposition under canonical 4→3, 5→3
   pushes) — mirror of ℂ-source `core3`.
4. Establish `gamma_containment_F` (γ-coupled leaf containments) —
   mirror of ℂ-source `gamma_containment`.
5. Apply `compl_le_forces_eq` to derive
   `W₁(0) = W₁(4)`, `W₁(0) = W₁(5)`, `W₁(1) = W₁(4)`, then chain
   `W₁(0) = W₁(1)` via `W₁(4)`. Mirror of ℂ-source `compl_eq_of_le`
   chain.

The F-generic version uses `compl_le_forces_eq` (from
`FieldGenericInfiniteType.lean:296`) instead of the ℂ-source's local
`have compl_eq_of_le` — that's a project-wide cleanup landed earlier
in the per-(F, Q) refactor, not a deviation introduced by this PR.

**Deviation justified.** No correctness concerns.

### Q10 — Case-split sorry positions (802 / 804 / 806 / 808 / 810)

The case-split hierarchy is:

```
e02 ─ Or.inl (canonical 0→2)
       ├── e12 ─ Or.inl (canonical 1→2)
       │       ├── e23 ─ Or.inl (canonical 2→3)
       │       │       ├── e43 ─ Or.inl (canonical 4→3)
       │       │       │       ├── e53 ─ Or.inl  → canonical branch (proven)
       │       │       │       └── e53 ─ Or.inr  → line 802 (1 sub-case)
       │       │       └── e43 ─ Or.inr           → line 804 (2 sub-cases)
       │       └── e23 ─ Or.inr                    → line 806 (4 sub-cases)
       └── e12 ─ Or.inr                            → line 808 (8 sub-cases)
└── e02 ─ Or.inr                                   → line 810 (16 sub-cases)
```

Arithmetic: 1 + 2 + 4 + 8 + 16 = **31 sub-cases**. The docstring
annotation in the issue body is **correct**:
3→5 / 3→4 / 3→2 / 2→1 / 2→0 with 1 / 2 / 4 / 8 / 16 sub-cases per
position. The orientation-branch mapping per sorry is right.

The actual in-source comments at lines 801–810 each correctly identify
which edge is reversed at that level (`e53 reversed (3→5)`,
`e43 reversed (3→4)`, `e23 reversed (3→2): follow-up sub-issue (uses γ⁻¹)`,
`e12 reversed (2→1): follow-up sub-issue (uses starSecond_F projection)`,
`e02 reversed (2→0): follow-up sub-issue (uses starFirst_F projection)`).
The "uses γ⁻¹" / "uses projection" annotations correctly point #2853 at
the relevant section 5b/5c/5d / `FieldGenericStar.lean` infrastructure.

### Q11 — Sorries / decide / convert chains in the canonical branch

**No issues found.** The canonical-branch proof body uses only
`rcases`, `obtain`, `have`, `simp only`, `refine`, `intros`, `rw`,
`omega`, `abel`, `ring`, `ext`, `change`, `exact`, and `exfalso`. No
`decide`-style tactics. No `convert` or `cast`. Three uses of `change`
in the helper proofs at the `Q.Hom` direction-arrow witness extraction
points (line 258, 555–622 are `simp only [d5tildeRep_kQ,
d5tildeRepMap_kQ]` which unfolds the rep — not `change`); those are
needed for the `simp only` to find a match, not to paper over coercion
issues.

The `simp only [d5tildeRep_kQ, d5tildeRepMap_kQ]` pattern (lines 578,
584, 588, 593, 598, 603, 608, 613, 618, 623) unfolds the rep
construction to expose the underlying `starEmbed1_F` /
`starEmbed2_F` / `d5tildeGamma_F` maps. This is the right way to
reduce — no hidden coercion mismatches.

## 4. Recommended follow-ups (separate issues to file)

The two follow-ups below are **non-blocking** for this audit; they are
cleanup tasks that should land before #2853 starts to maximise reuse.

1. **Hoist + dedup leaf helpers**
   (PR #2835 cleanup, single feature-issue).
   - Hoist `embed_sum_zero_F` and `center_decomp_F` from
     `FieldGenericD5Tilde.lean` (lines 215, 240) into
     `FieldGenericStar.lean`.
   - Replace the local `have embed_sum_zero` (lines 114-135) and
     `have center_decomp` (lines 270-278) in `starRepGen_isIndecomposable`
     with applications of the public theorems.
   - Estimated ~25 lines diff, single-session.

2. **Hoist canonical-branch helpers + decompose for non-canonical reuse**
   (PR #2854 cleanup, single feature-issue, blocks #2853).
   - Hoist `core_F`, `core3_F`, `gamma_containment_F` from the local
     `have` inside the canonical-orientation branch
     (`FieldGenericD5Tilde.lean:628-775`) to top-level theorems under
     Section 5e (alongside the leaf-equality theorem statement).
   - File sibling projection-direction analogues (e.g.
     `core_F_proj1`, `core_F_proj2`) for the 23 sub-cases where any
     leaf-center edge is reversed — these will use
     `starFirst_F` / `starSecond_F` pushes from centre to leaf
     instead of `starEmbed1_F` / `starEmbed2_F` from leaf to centre.
   - Estimated ~80 lines diff for the hoists; the sibling-analogue
     decomposition is part of the #2853 scope and not in this
     cleanup.

Both follow-ups are intentionally scoped small. Neither is on the
critical path for closing #2804 — the canonical case is proven and
the 31 reversed cases can be filled before or after the cleanup.

## 5. Build / test verification

```
$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde
⚠ [8041/8041] Built EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde (14s)
warning: …:528:8: declaration uses `sorry`
warning: …:849:8: declaration uses `sorry`
Build completed successfully (8041 jobs).
```

Two declarations use `sorry` (= 6 raw `sorry` keywords: 5 inside the
31-branch case-split at 802/804/806/808/810 + 1 at the API stub at
line 856). Matches the sorry-landscape report.

No new lint warnings introduced by any of the three PRs in the audit
window. Pre-existing warnings on `FieldGenericStar.lean:101`
(unscoped `maxHeartbeats` bump on `starRepGen_isIndecomposable`) and
on `FieldGenericInfiniteType.lean:263` (flexible `simp`) are
unrelated.

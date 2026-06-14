# Audit — D̃₅ Sub B cleanup hoists (PRs #2862, #2863)

Issue: #2864 (review). Parent: #2804.
Auditor session: `6fc85452`. Date: 2026-05-18 (UTC).

Scope: pre-flight check that the wave-60 cleanup hoists land cleanly
before #2853 starts. Both PRs claimed "mechanical hoist, no proof
changes"; this audit confirms statement fidelity, proof preservation,
and downstream-readiness of the hoisted helpers.

Build status confirmed on current `main` after both PRs merged:
- `lake build EtingofRepresentationTheory.Chapter6` exits green
  (`✔ [8079/8079] Built EtingofRepresentationTheory.Chapter6 (8.8s)`).
- `FieldGenericStar.lean`: 0 raw `sorry`, 0 declarations using `sorry`.
- `FieldGenericD5Tilde.lean`: 6 raw `sorry` (lines 798/800/802/804/806
  inside the 31-branch case-split + 1 at the API stub line 853);
  2 declarations using `sorry` (lines 670 `d5tildeRep_kQ_leaf_equalities`
  and 846 `d5tildeRep_kQ_isIndecomposable`).
- Matches the wave-60 baseline (`progress/sorry-landscape.md`,
  `progress/reviews/2026-05-18-d5tilde-subB-cascade-helpers.md` §5).

Line numbers shifted relative to the issue body (which referenced
802/804/806/808/810): the hoist in PR #2862 added ~170 lines for the
three new top-level theorems at lines 482–648, pushing the case-split
sorries down by 4 lines. Sorry count and structural meaning are
unchanged.

## Verdicts

| PR    | Verdict |
|-------|---------|
| #2862 | PASS    |
| #2863 | PASS    |

Both PRs are clean refactors. No follow-ups filed; the
sibling-direction analogues for non-canonical sub-cases are already
part of #2853's scope (as noted in the wave-60 audit §4 item 2).

## 1. PR #2862 — `d5tilde_core_F` / `d5tilde_core3_F` / `d5tilde_gamma_containment_F` — PASS

### 1.1 Statement fidelity

The three local `have` lemmas that previously lived inside the
canonical-orientation branch of `d5tildeRep_kQ_leaf_equalities`
(pre-hoist `FieldGenericD5Tilde.lean:625–795`) were universally
quantified over `(Wmain, Wother)` and four-to-six push hypotheses. The
hoisted top-level theorems
(`FieldGenericD5Tilde.lean:482`, `:540`, `:598`) make those
universally-quantified arguments explicit parameters and add the outer
`(F, Q, [Subsingleton], hOrient, m)` parameter block. **Logically
equivalent** — currying the same set of arguments.

Spot-check against the old `have` blocks (read from
`git show 2332f15 -- EtingofRepresentationTheory/Chapter6/FieldGenericD5Tilde.lean`):

- `d5tilde_core_F` (FieldGenericD5Tilde.lean:482) — hypothesis list
  matches `have core_F` (pre-hoist 628–676): `Wmain Wother`,
  `hMain_02`, `hMain_12`, `hOther_02`, `hOther_12`, `hc`,
  `x z`, `hmem`. Conclusion `x ∈ Wmain ⟨0⟩ ∧ z ∈ Wmain ⟨1⟩` unchanged.
  Proof body (lines 501–532) is character-for-character identical to
  the old `have` body except for the binder style (top-level takes
  named params; old used `intros`).
- `d5tilde_core3_F` (FieldGenericD5Tilde.lean:540) — same shape, v=3
  instead of v=2. Hypothesis list matches `have core3_F` exactly. Body
  identical.
- `d5tilde_gamma_containment_F` (FieldGenericD5Tilde.lean:598) — six
  push hypotheses (`hMain_02`, `hMain_12`, `hMain_23`, `hMain_43`,
  `hMain_53`, `hOther_43`, `hOther_53`) match the old `have
  gamma_containment_F`. Conclusion `(W(0)→W(4)) ∧ (W(0)→W(5)) ∧
  (W(1)→W(4)) ∧ (W(1)→nshift→W(5))` unchanged. Body (lines 628–648)
  identical (four `· have he … rw [gamma_from_embed*_F] … exact
  (d5tilde_core3_F …).{1,2}`).

No hypothesis from the enclosing scope was silently dropped. The
canonical-branch proof body at `FieldGenericD5Tilde.lean:715–796` still
specialises `hW₁_inv` / `hW₂_inv` via
`simp only [d5tildeRep_kQ, d5tildeRepMap_kQ]` (lines 717–766), then
calls `d5tilde_gamma_containment_F` twice (lines 771, 774) with
correctly threaded hypotheses, then chains via three
`compl_le_forces_eq` applications (lines 780–795). Same overall
structure as the wave-60 audit confirmed for PR #2854.

### 1.2 `(Wmain, Wother)` symmetry

The hoisted theorems take `Wmain Wother` as a symmetric pair, and the
canonical-branch usage applies them both ways:

```lean
-- line 771: (Wmain, Wother) = (W₁, W₂); hcompl threaded directly
obtain ⟨h04, h05, h14, _⟩ :=
  d5tilde_gamma_containment_F F Q hOrient m W₁ W₂
    hW₁_02 hW₁_12 hW₁_23 hW₁_43 hW₁_53 hW₂_43 hW₂_53 hcompl
-- line 774: (Wmain, Wother) = (W₂, W₁); hcompl symmetrised
obtain ⟨h04', h05', h14', _⟩ :=
  d5tilde_gamma_containment_F F Q hOrient m W₂ W₁
    hW₂_02 hW₂_12 hW₂_23 hW₂_43 hW₂_53 hW₁_43 hW₁_53
    (fun v => (hcompl v).symm)
```

Both applications type-check (build green) and threading is mechanical
— this confirms the parameterisation is genuinely symmetric.

Note one mild asymmetry in `d5tilde_gamma_containment_F`'s signature:
it takes a γ-push hypothesis only on `Wmain` (`hMain_23`), not on
`Wother`. This is intentional and inherited from the old `have` —
the lemma's job is to feed `core3_F` after applying γ to one specific
side, and the other side's γ-invariance is not needed within the lemma
body. The asymmetric application above passes `hW₁_23` then `hW₂_23`
respectively, which is sound (both `W₁` and `W₂` are γ-invariant
subspaces).

### 1.3 Build/heartbeat

No `set_option maxHeartbeats` bump introduced by PR #2862. The
`FieldGenericD5Tilde.lean` file has no scoped heartbeat options
(verified by grep). Build time of the hoisted file: ~13s from cache.

## 2. PR #2863 — `embed_sum_zero_F` / `center_decomp_F` hoist + dedup — PASS

### 2.1 Statement fidelity

`embed_sum_zero_F` (FieldGenericStar.lean:86):
```lean
theorem embed_sum_zero_F (F : Type) [Field F] (m : ℕ) (x y : Fin (m + 1) → F)
    (h : starEmbed1_F F m x + starEmbed2_F F m y = 0) :
    x = 0 ∧ y = 0
```
Matches the disjointness-at-the-center fact #2853 needs:
`starEmbed1_F x + starEmbed2_F y = 0 → x = 0 ∧ y = 0`. Body (lines
89–107) is byte-equivalent to the old `have embed_sum_zero` block at
the pre-hoist `FieldGenericStar.lean:114–135`.

`center_decomp_F` (FieldGenericStar.lean:111):
```lean
theorem center_decomp_F (F : Type) [Field F] (m : ℕ) (w : Fin (2 * (m + 1)) → F) :
    w = starEmbed1_F F m (starFirst_F F m w) +
        starEmbed2_F F m (starSecond_F F m w)
```
Decomposes `w : Fin (2 * (m + 1)) → F` as the sum of its two half-block
embeddings via the half-block projections. This is a refinement on the
old `have center_decomp` statement (pre-hoist
`FieldGenericStar.lean:270–278`), which used inline lambdas
`fun i => w ⟨i.val, _⟩` and `fun i => w ⟨m + 1 + i.val, _⟩`. The
inline lambdas and the projections `starFirst_F` / `starSecond_F` are
definitionally equal (the projection `def`s have `toFun w i :=
w ⟨i.val, by omega⟩` and `toFun w i := w ⟨m + 1 + i.val, by omega⟩`).
Body is byte-equivalent except for an additional `starFirst_F,
starSecond_F` in the `simp only` list to unfold the projections.

### 2.2 Local `have` removal

The two local `have embed_sum_zero` and `have center_decomp` blocks
inside `starRepGen_isIndecomposable` are gone:
```
$ grep -n "have embed_sum_zero\|have center_decomp" \
    EtingofRepresentationTheory/Chapter6/FieldGenericStar.lean
(no matches in FieldGenericStar.lean — only ℂ-source
 InfiniteTypeConstructions.lean retains the old idiom)
```

The two former call sites now call the public theorems:
- `FieldGenericStar.lean:215`: `obtain ⟨hb0', hd0'⟩ :=
  embed_sum_zero_F F m b d hzero` (was `embed_sum_zero b d hzero`).
- `FieldGenericStar.lean:331`: `center_decomp_F F m w ▸ …` (was
  `center_decomp w ▸ …`). The rewrite still matches because both
  forms have `w` as their LHS.

### 2.3 Cross-file usage by PR #2862

The hoisted `embed_sum_zero_F` is also consumed by PR #2862's
canonical-branch proof body, at `FieldGenericD5Tilde.lean:530` (inside
`d5tilde_core_F`) and `:588` (inside `d5tilde_core3_F`). This
cross-file usage was the motivation for the hoist — it eliminates two
sources of duplication (one in `starRepGen_isIndecomposable`, one
local to each of `core_F` / `core3_F`).

### 2.4 `starFirst_F` / `starSecond_F` relocation

To allow `center_decomp_F` to be stated using the projection form, the
two half-block projections were moved upstream from the
"Direction-aware leaf maps" section
(`FieldGenericStar.lean:381+` pre-hoist) to right after the embeddings
(`:64–76` post-hoist). The "Direction-aware leaf maps" section header
was updated with a note pointing to the new home. The four
direction-projection lemmas
(`starFirst_F_starEmbed*`/`starSecond_F_starEmbed*` at lines 406–432)
that previously sat below the definitions are unchanged in placement
relative to the embeddings — they now appear after the projections in
the same logical order.

### 2.5 `starRepGen_isIndecomposable` preservation

Build of `FieldGenericStar.lean` green
(`⚠ [8075/8079] Built EtingofRepresentationTheory.Chapter6.FieldGenericStar (13s)`)
with the existing `set_option maxHeartbeats 1600000` bump at line 159
(unchanged from pre-hoist — this is the K_{1,4} indecomposability
heartbeat profile inherited from the ℂ-source). The two `have` →
public-call substitutions at lines 215 and 331 are entirely local; no
other structural changes inside `starRepGen_isIndecomposable`. The
overall proof structure (centre-extraction, leaf-by-leaf reasoning,
nilpotent-shift complement, final `propagate` lemma) is intact.

Pre-existing lint warnings on line 159 (unscoped `maxHeartbeats`
bump, requires explanatory comment) are unchanged — neither PR
introduces nor removes them.

## 3. Downstream-readiness for #2853

Sorry positions and helper applicability per branch:

| Line | Reversed edge       | Sub-cases | `d5tilde_core_F` | `d5tilde_core3_F` | `d5tilde_gamma_containment_F` |
|------|---------------------|-----------|------------------|-------------------|-------------------------------|
| 798  | e53 (3→5)           | 1         | ✓                | ✗                 | ✗                             |
| 800  | e43 (3→4)           | 2         | ✓                | ✗                 | ✗                             |
| 802  | e23 (3→2)           | 4         | ✓                | 1/4 ✓             | ✗                             |
| 804  | e12 (2→1)           | 8         | ✗                | 2/8 ✓             | ✗                             |
| 806  | e02 (2→0)           | 16        | ✗                | 4/16 ✓            | ✗                             |

Applicability rules:
- `d5tilde_core_F` requires `e02 = e12 = canonical` (canonical 0→2,
  1→2 pushes). Applicable in lines 798/800/802 (where both are
  pre-fixed canonical by the outer rcases) — 7 of 31 sub-cases.
- `d5tilde_core3_F` requires `e43 = e53 = canonical` (canonical 4→3,
  5→3 pushes). Applicable in: 0 at line 798 (e53 reversed); 0 at line
  800 (e43 reversed); 1 of 4 at line 802 (e43 = e53 = canonical inner
  split); 2 of 8 at line 804 (e23 ∈ {can, rev}, e43 = e53 = can); 4
  of 16 at line 806 (e12 ∈ {can, rev}, e23 ∈ {can, rev}, e43 = e53 =
  can). 7 of 31 sub-cases.
- `d5tilde_gamma_containment_F` requires all five edges canonical
  (full canonical orientation), which is already proven inline. 0 of
  31 reversed sub-cases.

The remaining 24 sub-cases needing `d5tilde_core_F` and 24 needing
`d5tilde_core3_F` will require **direction-reversed sibling lemmas**
(e.g. `d5tilde_core_F_proj1` using `starFirst_F : Wmain(2) → Wmain(0)`
in place of `starEmbed1_F : Wmain(0) → Wmain(2)`). These siblings are
part of #2853's scope (as anticipated by the wave-60 audit §4 item 2)
and don't need to be filed separately by this audit.

The 31 sub-cases will additionally need γ-reversed analogues at line
802 (where the γ direction is reversed, needing
`gammaInv_embed1_plus_embed2_F` / `gammaInv_embed1_plus_embedNshift_F`
from PR #2843 instead of `gamma_from_embed*_F`).

**Sanity-check passed:** the hoisted helpers are usable for at least
some sub-cases (14 of 31 applications: 7 for `core_F`, 7 for
`core3_F`). The parameterisation hasn't accidentally locked them to
`W₁`-only — confirmed by the symmetric `(W₁, W₂)` / `(W₂, W₁)` calls
in the canonical branch.

## 4. Recommended follow-ups

**None from this audit.** Both PRs are clean refactors with no
hidden defects. The sibling-direction analogues for the 24 sub-cases
that don't fit `d5tilde_core_F` / `d5tilde_core3_F` directly are part
of #2853's scope and were already called out by the wave-60 audit.

## 5. Build / test verification

```
$ lake build EtingofRepresentationTheory.Chapter6
[…]
⚠ [8075/8079] Built EtingofRepresentationTheory.Chapter6.FieldGenericStar (13s)
⚠ [8077/8079] Built EtingofRepresentationTheory.Chapter6.FieldGenericD5Tilde (13s)
warning: FieldGenericD5Tilde.lean:670:8: declaration uses `sorry`
warning: FieldGenericD5Tilde.lean:846:8: declaration uses `sorry`
✔ [8079/8079] Built EtingofRepresentationTheory.Chapter6 (8.8s)
Build completed successfully (8079 jobs).
```

Total wall-clock 8m08s (cached incremental). Two declarations use
`sorry` in `FieldGenericD5Tilde.lean` (the leaf-equality and
indecomposability stubs); 0 in `FieldGenericStar.lean`. Matches the
wave-60 sorry landscape.

No new lint warnings. Pre-existing warnings on
`FieldGenericCycle.lean:76/84` (show/exact style) and
`FieldGenericStar.lean:159` (unscoped maxHeartbeats) are unrelated to
either PR.

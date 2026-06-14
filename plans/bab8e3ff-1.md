## Current state

PR #2706 (Schur-Weyl L_i part C-4c, `schurModule_isSimple`) merged on
2026-05-04 as a `--partial` PR carrying one well-localised sorry at
`EtingofRepresentationTheory/Chapter5/SchurModuleSimple.lean:148`:

```lean
theorem schurModuleSubmodule_isSimple_centralizer
    (N : ℕ) (lam : Fin N → ℕ) (_hlam : Antitone lam) (_hN : (∑ i, lam i) ≤ N) :
    IsSimpleModule
      (↥(diagonalActionImage k (Fin N → k) (∑ i, lam i)))
      (SchurModuleSubmodule k N lam) := by
  sorry
```

This is the **C-4a aggregation** referenced in the worker progress note
`progress/20260504T082119Z_a1a48844.md`: the single discharge that
combines the now-landed/in-flight C-4a sub-pieces — `sub-α`, `sub-β`
(β.1 #2682 merged, β.2 #2683 merged via PR #2697, β.3 #2684 in flight),
`sub-γ` (γ.A #2694 PR in repair, γ.B #2693 blocked on β.3), and
`C-4a-ii` `image_of_primitive_idempotent_isSimple_centralizer`
(`PrimitiveIdempotentSimplicity.lean:220`, merged via PR #2698) — into
the single `IsSimpleModule` conclusion above.

Once γ.A + γ.B + β.3 all land, the discharge is mechanical glue: thread
the `Theorem5_18_4_bimodule_decomposition_explicit` decomposition
(sub-α, already merged) into the `e : E ≃ₗ[k] ⨁ᵢ ↥(S i) ⊗[k] L i`
hypothesis of `image_of_primitive_idempotent_isSimple_centralizer`, then
read off `f i = 0` for `i ≠ iLam` from β.3 and `f iLam = α • π` for a
rank-1 idempotent `π` from γ.A + γ.B.

## Deliverables

Replace the sorry at `SchurModuleSimple.lean:148` with the full proof of
`schurModuleSubmodule_isSimple_centralizer`. **Single deliverable, one
file touched.**

## Context

- **Parent**: closes the last sorry introduced by PR #2706 (#2612). With
  this sorry discharged, the C-4c critical-path entry of
  `Theorem 5.22.1` is fully proven.
- **Files**: `EtingofRepresentationTheory/Chapter5/SchurModuleSimple.lean`
  (the only file touched). Likely net ≤ 50 lines of glue code; if it
  grows past ~150 lines, decompose via `coordination skip`.
- **Helpers to use**:
  - `image_of_primitive_idempotent_isSimple_centralizer`
    (`PrimitiveIdempotentSimplicity.lean:220`) — the aggregation
    interface. Consumes a bimodule decomposition `e`, the simplicity of
    `S iLam`, and per-block action hypotheses `hf_block`, `hf_zero`,
    `hπ_idem`, `hπ_rank`, `hπ_special`. Outputs `IsSimpleModule
    centralizer ↥(imageSubmoduleB c)`.
  - `Theorem5_18_4_bimodule_decomposition_explicit`
    (`Theorem5_18_4.lean`) — supplies the `e` (bimodule
    decomposition of `V^⊗n` indexed by partitions of `n` ≤ N).
  - `Theorem5_18_4_centralizers` (`Theorem5_18_4.lean:268`) —
    identifies the centralizer of `symGroupImage` with
    `diagonalActionImage` (needed to match the conclusion's module
    structure). Requires `n ≤ N`.
  - **β.3 output** (from #2684, when it lands): `hf_zero` — the
    off-block vanishing `f i = 0` for `i ≠ iLam`.
  - **γ.A output** (from PR #2694, when it lands): the scaled-projection
    structure on the iLam block, giving the rank-1 idempotent `π` and
    scalar `α` such that `f iLam = α • π`.
  - **γ.B output** (from #2693, when it lands): rank-1 dim count
    `Module.finrank k (LinearMap.range π) = 1` (= `hπ_rank` in the
    aggregation interface).
  - **β.2 output** (PR #2697 merged): simplicity of the special Specht
    block, supplies `hSiLam_simple : IsSimpleModule A ↥(S iLam)`.

## Proof outline

```lean
theorem schurModuleSubmodule_isSimple_centralizer
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) (hN : (∑ i, lam i) ≤ N) :
    IsSimpleModule (↥(diagonalActionImage k (Fin N → k) (∑ i, lam i)))
      (SchurModuleSubmodule k N lam) := by
  -- 1. Identify diagonalActionImage with centralizer(symGroupImage)
  --    via Theorem5_18_4_centralizers (needs hN).
  -- 2. The Schur module submodule equals `range (c_λ : V^⊗n →ₗ V^⊗n)`
  --    where `c_λ` is the Young symmetrizer — i.e. it IS an
  --    `imageSubmoduleB c_λ` for `c = c_λ`.
  -- 3. Feed the per-block data from β.3 + γ.A + γ.B into
  --    `image_of_primitive_idempotent_isSimple_centralizer`:
  --    - `e` from `Theorem5_18_4_bimodule_decomposition_explicit`
  --    - `hSiLam_simple` from β.2 (merged)
  --    - `hf_zero` from β.3
  --    - `hπ_idem`, `hπ_rank` from γ.B
  --    - `hπ_special` (the rank-1 idempotent structure) from γ.A
  -- 4. Transport simplicity via the centralizer identification (step 1).
  sorry  -- ≤ 50 lines of glue
```

## Stalls and pivots

If the per-block data from γ.A + γ.B + β.3 doesn't match the
`image_of_primitive_idempotent_isSimple_centralizer` interface
verbatim (mismatched indexing, scalar bookkeeping, or DirectSum
mismatches), do NOT force-close with a new sorry. Instead, file a
follow-up issue identifying the specific interface mismatch and leave
the existing sorry in place. The discharge is purely mechanical glue —
any non-trivial obstacle is a sign that one of the upstream pieces
needs sharpening before aggregation.

## Verification

- `lake build EtingofRepresentationTheory.Chapter5.SchurModuleSimple` passes
- Zero sorries remain in `SchurModuleSimple.lean`
- `lake build EtingofRepresentationTheory.Chapter5` passes end-to-end
- Sorry-count delta: **−1 leaf in 1 file**

depends-on: #2684
depends-on: #2693
depends-on: #2694

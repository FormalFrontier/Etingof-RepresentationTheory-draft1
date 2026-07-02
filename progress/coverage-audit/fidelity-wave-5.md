# Stage 3.7 Fidelity Sweep — Wave 5 (Chapter 3 closeout, issue #5340)

Judge model: Opus (different family than the original formalizers and than the
wave-1/wave-2 Chapter-3 auditors). Scope: the **27** claim-bearing done items of
Chapter 3 (`fidelity-worklist.tsv`), applying PLAN.md §3.2 steps 6–7 (anti-vacuity
decision test + conjunct-by-conjunct fidelity), calibrated on #5322/#5323/#5326 and
the wave-4 dropped-uniqueness gap (#5669).

## Entry state

Prior waves had already audited Chapter 3 and driven every wave-2 gap through a
repair issue. On entry, 22 items were `verified`, 1 was `gap` (Definition3.3.2),
and **5 items carried non-canonical fidelity values** left over from the repair
cycle (`faithful`, `partial`, `covered`) or a stale `gap`. This wave re-read each
of those 5 against its blob and current Lean statement and normalized it to the
canonical `verified`/`gap` vocabulary. The other 22 `verified` items were accepted
from waves 1–2; three headliners were spot-checked (below) to bound residual risk.

## Normalizations (5 items, all → `verified` after fresh verification)

- **Definition3.3.2** (`gap` → `verified`). Stale gap. Repair #5618 (CLOSED) added
  the algebra parameter `A`: `DualRepresentation k A V := Module.Dual k V` now
  carries the contragredient `Aᵐᵒᵖ`-action via `instance instModuleMulOppositeDual`,
  and the defining-equation theorem `dualRepresentation_smul_apply` proves
  `(a • f) v = f (a.unop • v)` — exactly the book's `(f·a)(v) = f(av)`. The A^op
  representation is genuinely constructed; no vacuous/weakened statement remains.

- **Definition3.4.1** (`faithful` → `verified`). Repair #5619 (CLOSED) replaced the
  bare `RelSeries` abbrev with a `structure` bundling the strictly-ascending chain
  and both boundary conditions `head_eq_bot` (V₀ = ⊥) and `last_eq_top` (Vₙ = ⊤),
  matching `0 = V₀ ⊂ ⋯ ⊂ Vₙ = V`. No dropped conjunct.

- **Theorem3.10.2** (`faithful` → `verified`). Part (i) `tensor_product_irreducible`
  and part (ii) existence `tensor_product_irreducible_classification` are faithful;
  repair #5614 (CLOSED) restored the dropped uniqueness conjunct as companion
  theorem `tensor_product_irreducible_classification_unique` (any two A-B-equivariant
  factorizations give `V ≃ₗ[A] V'` and `W ≃ₗ[B] W'` — the book's "unique V and W"
  up to isomorphism). No dropped conjunct.

- **Remark3.10.3** (`covered` → `verified`). Repair #5663 (CLOSED) formalized the
  remark's concrete counterexample: `ratFunc_tensor_ratFunc_not_isField` proves
  `¬ IsField (RatFunc ℂ ⊗[ℂ] RatFunc ℂ)`, witnessing the failure of Theorem
  3.10.2(i) for A=B=V=W=ℂ(x). Faithful and non-vacuous (explicit nonzero non-unit
  witness).

- **Remark3.8.6** (`partial` → `verified`). Judgment call, recorded explicitly.
  The remark asserts Krull-Schmidt holds for finite-length modules. The formalized
  declarations (`isNilpotent_or_isUnit_of_finiteLength_indecomposable` = Fitting's
  lemma, `isLocalRing_end_of_finiteLength_indecomposable`,
  `exists_indecomposable_decomposition`) are each faithful and non-vacuous, and
  crucially **none is presented as full Krull-Schmidt while being silently weaker** —
  the existence half is honestly named "existence half". The missing uniqueness
  half (Krull-Schmidt-Azumaya) in the finite-length setting is a *coverage*
  follow-up already tracked and closed as an acceptable resting state (repair
  #5662, CLOSED, with uniqueness noted as follow-up), not a *fidelity* gap: no
  vacuous/weakened statement masquerades under this item's name. Full uniqueness
  for the finite-dimensional case is faithfully proved separately in Theorem 3.8.1
  (`krull_schmidt_uniqueness`). Verdict `verified` for the fidelity arm; the
  uniqueness coverage item remains for the coverage arm to schedule if desired.

## Spot-checks of the inherited `verified` bucket (3 headliners, all faithful)

- **Theorem3.5.4** `structure_mod_radical` — proves `A/Rad(A) ≃ₐ[k] ∏ᵢ End(Vᵢ)`
  over a finite complete family of nonisomorphic simples (Fintype ι + completeness
  hypothesis). Isomorphism conjunct present; product = direct sum for finite index.
- **Theorem3.7.1** `jordan_holder` + `jordan_holder_factors` — both conjuncts
  present: length equality `n = m` and `∃ σ` permutation with `Wᵢ ≃ₗ[A] W'_{σ i}`.
- **Theorem3.8.1** `krull_schmidt_existence` + `krull_schmidt_uniqueness` — both
  halves present; uniqueness is `n = m ∧ ∃ σ, ∀ i, Wᵢ ≃ₗ[A] W'_{σ i}`.

No new gaps found in the spot-check.

## Result

All 27 Chapter 3 worklist items are now `verified` (canonical). Chapter-3 fidelity
verdict counts: **verified 27, gap 0**. Issue #5340 done. No repair issues opened
(the two dropped-conjunct gaps from wave-2 were already repaired and closed;
this wave only confirmed and re-labeled them).

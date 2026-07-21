# Statement-fidelity & non-vacuity audit — Ch3 Theorem 3.7.1 (Jordan-Hölder theorem for modules)

**Date:** 2026-07-21
**Reviewer:** review session (issue #7166)
**Files audited:**
- `EtingofRepresentationTheory/Chapter3/Theorem3_7_1.lean` (79 lines, 0 sorry)
- Book source: `blobs/Chapter3/Theorem3.7.1.md`,
  `blobs/Chapter3/Discussion_after_Theorem3.7.1.md`
- Mathlib backing: `Mathlib/Order/JordanHolder.lean`
  (`CompositionSeries`, `Equivalent`, `CompositionSeries.jordan_holder`),
  `Mathlib/RingTheory/SimpleModule/Basic.lean`
  (`JordanHolderModule.instJordanHolderLattice`, `covBy_iff_quot_is_simple`)

## Verdict summary

| Declaration | Verdict |
|---|---|
| `Etingof.compositionFactor` (the factor abbrev) | **FAITHFUL** — the genuine successive quotient `sᵢ₊₁ / sᵢ` |
| `Etingof.jordan_holder_equivalent` | **FAITHFUL** |
| `Etingof.jordan_holder_factors` | **FAITHFUL** |
| `Etingof.jordan_holder` | **FAITHFUL** |
| Non-vacuity / axiom audit | **CLEAN** (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`); concrete length-2 witness constructed |

No defect found. This is a **report-only** deliverable; no `.lean` files were modified.

## Book statement

> **Theorem 3.7.1** (Jordan-Hölder theorem). *Let V be a finite dimensional
> representation of A, and let 0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ = V, 0 = V'₀ ⊂ ⋯ ⊂ V'ₘ = V be
> filtrations of V, such that the representations Wᵢ := Vᵢ/Vᵢ₋₁ and W'ᵢ := V'ᵢ/V'ᵢ₋₁
> are irreducible for all i. Then n = m, and there exists a permutation σ of 1, …, n
> such that W_{σ(i)} is isomorphic to W'ᵢ.*

The book statement bundles three claims: (a) the two series have the same number of
terms (`n = m`), (b) there is a permutation `σ` of the index set, and (c) matching up
factors under `σ` gives isomorphic irreducible successive quotients. The Lean encoding
provides one master theorem carrying all three (`jordan_holder_equivalent`) and two
convenience corollaries projecting out the length half (`jordan_holder`) and the
permutation-of-factors half (`jordan_holder_factors`).

## 0. The framework: `CompositionSeries` and `compositionFactor`

The book's "filtration `0 = V₀ ⊂ ⋯ ⊂ Vₙ = V` with irreducible successive quotients" is
rendered as `s : CompositionSeries (Submodule A V)` together with `s.head = ⊥` and
`s.last = ⊤`. Each piece checks out:

- **`CompositionSeries (Submodule A V)` is the honest Jordan-Hölder series notion, not a
  weaker chain.** In Mathlib
  `CompositionSeries X := RelSeries {(x, y) : X × X | IsMaximal x y}`, and the module
  lattice instance `JordanHolderModule.instJordanHolderLattice` sets
  `IsMaximal := (· ⋖ ·)` (the *covering* relation). So the `step` field of the series
  requires `s i.castSucc ⋖ s i.succ` for every `i`: each inclusion is **strict**
  (`⋖` implies `<`) and **covering** (nothing strictly between). Covering of submodules
  is exactly simplicity of the successive quotient:
  `covBy_iff_quot_is_simple (hAB : A ≤ B) : A ⋖ B ↔ IsSimpleModule R (B ⧸ A.comap B.subtype)`.
  Hence "successive quotients are irreducible" is faithfully captured, and the series is a
  genuine composition series (strict, simple quotients), not a mere ascending chain.
  Verified defeq: `s.step i : (s i.castSucc) ⋖ (s i.succ)`.

- **`s.head = ⊥ ∧ s.last = ⊤` pins the series to run from `0` to all of `V`.** A
  `RelSeries` always has `length + 1 ≥ 1` terms; `head = s 0` and `last = s (Fin.last _)`.
  Requiring `head = ⊥` fixes the bottom term to the zero submodule and `last = ⊤` fixes the
  top term to the whole module `V` (`⊤ : Submodule A V`), matching `0 = V₀` and `Vₙ = V`.
  This is not a series in some sub-quotient — `⊤` is genuinely `V`.

- **`Etingof.compositionFactor s i` is the genuine successive quotient `Wᵢ = Vᵢ/Vᵢ₋₁`.**
  Its definition is
  `s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype`,
  i.e. `sᵢ₊₁` modulo the image of `sᵢ` sitting inside `sᵢ₊₁` — the standard realization of
  the quotient of two consecutive submodules. Verified by `rfl`:
  `compositionFactor s i = s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype`.
  Crucially this is **exactly** the quotient the module lattice's `Iso` relation uses
  (`Iso X Y := Nonempty ((X.2 ⧸ X.1.comap X.2.subtype) ≃ₗ[R] Y.2 ⧸ Y.1.comap Y.2.subtype)`),
  so the abbrev is not a placeholder — it is the very object the Jordan-Hölder equivalence
  talks about. Confirmed non-vacuously simple in the witness below.

## 1. Master theorem — `Etingof.jordan_holder_equivalent`

```
theorem Etingof.jordan_holder_equivalent (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V))
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    s₁.Equivalent s₂
```

**FAITHFUL.**

- **`s₁.Equivalent s₂` is the correct "permutation + isomorphic factors" notion, not
  something vacuous.** Mathlib defines
  `Equivalent s₁ s₂ := ∃ f : Fin s₁.length ≃ Fin s₂.length, ∀ i, Iso (s₁ i.castSucc, s₁ i.succ) (s₂ (f i).castSucc, s₂ (f i).succ)`,
  and for the module lattice `Iso` is `Nonempty (successive-quotient ≃ₗ successive-quotient)`.
  So the conclusion literally asserts the existence of an index bijection under which
  matched composition factors are linearly isomorphic — the full content of the book's
  "n = m and ∃σ with W_{σ(i)} ≅ W'ᵢ". It is not `True` and not trivially inhabited (it fails
  for series of different lengths, which is precisely why the theorem has content).
- **The hypotheses feed Mathlib's `CompositionSeries.jordan_holder` correctly.** That theorem
  needs `s₁.head = s₂.head` and `s₁.last = s₂.last`; the proof supplies these by rewriting
  the four `⊥`/`⊤` hypotheses (`rw [hs₁_bot, hs₂_bot]`, `rw [hs₁_top, hs₂_top]`). So the two
  series are compared as composition series *of the same module from ⊥ to ⊤*, exactly the
  book's setup.

## 2. Factor half — `Etingof.jordan_holder_factors`

```
theorem Etingof.jordan_holder_factors (A V : Type*) [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V))
    (hs₁_bot : s₁.head = ⊥) (hs₁_top : s₁.last = ⊤)
    (hs₂_bot : s₂.head = ⊥) (hs₂_top : s₂.last = ⊤) :
    ∃ σ : Fin s₁.length ≃ Fin s₂.length, ∀ i : Fin s₁.length,
      Nonempty (Etingof.compositionFactor s₁ i ≃ₗ[A] Etingof.compositionFactor s₂ (σ i))
```

**FAITHFUL.** This is the literal transcription of "there exists a permutation `σ` such that
`W_{σ(i)}` is isomorphic to `W'ᵢ`" (up to which side carries `σ`, which is immaterial since
`σ` ranges over all bijections and can be inverted). The proof is *definitional*: the body is
just `Etingof.jordan_holder_equivalent …`, meaning the target existential is **defeq** to
`s₁.Equivalent s₂`. This defeq is not an accident — it holds precisely because
`Etingof.compositionFactor` was defined to be the same quotient the lattice `Iso` uses (see
§0). The `∃ σ … Nonempty (… ≃ₗ[A] …)` is honest: `σ` is a genuine `Equiv`, and each factor
comparison is an actual `LinearEquiv`, not a propositional stand-in. Non-vacuously realized in
the witness below (§4) with two simple factors.

## 3. Length half — `Etingof.jordan_holder`

```
theorem Etingof.jordan_holder (A V : Type*) [Ring A] [AddCommGroup V] [Module A V]
    (s₁ s₂ : CompositionSeries (Submodule A V)) …four ⊥/⊤ hyps… :
    s₁.length = s₂.length
```

**FAITHFUL.** This is the book's "n = m". The proof is
`(jordan_holder_equivalent …).length_eq`, using Mathlib's
`CompositionSeries.Equivalent.length_eq : Equivalent s₁ s₂ → s₁.length = s₂.length`. Note the
book's `n` is the number of *factors* (`= Vₙ` index), which in Lean is `s.length` (a
`RelSeries` of length `n` has `n + 1` terms `s 0 … s n` and `n` factors). So `s₁.length =
s₂.length` is exactly `n = m`. Honest consequence of the master theorem.

## 4. Non-vacuity — axioms and a concrete length-2 witness

**Axioms.** `#print axioms` for all three public theorems gives exactly
```
[propext, Classical.choice, Quot.sound]
```
No `sorryAx`, no project-specific custom axiom. The file is genuinely sorry-free and the
declarations rest only on Lean/Mathlib's standard classical foundation.

**Satisfiability of the hypotheses / non-triviality of the conclusion.** The concern flagged
in the issue — "if some module admits no composition series from ⊥ to ⊤ the theorem is
vacuously true for it" — is correct but is a *hypothesis*, not a defect: existence of the two
series `sᵢ` with `head = ⊥`, `last = ⊤` is what carries the finite-length content, exactly as
the book assumes finite-dimensionality to guarantee such filtrations exist (Lemma 3.4.2 in the
book). To confirm the hypotheses are satisfiable with a genuinely length-≥2 series and that the
conclusions come out with real content, I constructed and machine-checked a concrete witness
over `A = ℚ`, `V = ℚ² = (Fin 2 → ℚ)`:

```lean
-- The first-coordinate line L = {f | f 1 = 0} ⊂ ℚ².
noncomputable def L : Submodule ℚ (Fin 2 → ℚ) :=
  LinearMap.ker (LinearMap.proj 1 : (Fin 2 → ℚ) →ₗ[ℚ] ℚ)

-- L is 1-dimensional (rank-nullity, proj 1 surjective), hence simple;
-- and ℚ²/L is 1-dimensional, hence simple.
instance : IsSimpleModule ℚ L                      := isSimpleModule_iff_finrank_eq_one.mpr …
instance : IsSimpleModule ℚ ((Fin 2 → ℚ) ⧸ L)      := isSimpleModule_iff_finrank_eq_one.mpr …

-- A genuine length-2 composition series ⊥ ⋖ L ⋖ ⊤ from ⊥ to ⊤.
noncomputable def sJH : CompositionSeries (Submodule ℚ (Fin 2 → ℚ)) where
  length := 2
  toFun := ![⊥, L, ⊤]
  step := by
    intro i; fin_cases i
    · change (⊥ : Submodule ℚ (Fin 2 → ℚ)) ⋖ L
      exact bot_covBy_iff.mpr IsSimpleModule.isAtom
    · change L ⋖ (⊤ : Submodule ℚ (Fin 2 → ℚ))
      exact covBy_top_iff.mpr (isSimpleModule_iff_isCoatom.mp ‹_›)

example : sJH.head = ⊥ := rfl
example : sJH.last = ⊤ := rfl
example : sJH.length = 2 := rfl

-- Both hypotheses satisfiable; the theorem then yields real content:
example : sJH.length = sJH.length ∧ Nonempty (Fin sJH.length ≃ Fin sJH.length) :=
  ⟨Etingof.jordan_holder ℚ (Fin 2 → ℚ) sJH sJH rfl rfl rfl rfl,
   (Etingof.jordan_holder_factors ℚ (Fin 2 → ℚ) sJH sJH rfl rfl rfl rfl).elim
      fun σ _ => ⟨σ⟩⟩

-- Each of the two composition factors is genuinely a simple module (irreducible):
example (i : Fin sJH.length) : IsSimpleModule ℚ (Etingof.compositionFactor sJH i) := by
  have h : sJH i.castSucc ⋖ sJH i.succ := sJH.step i
  exact (covBy_iff_quot_is_simple h.le).mp h
```

This entire witness **compiles** (checked in a scratch file, since removed — the deliverable is
report-only). It establishes:
- the `head = ⊥ ∧ last = ⊤` hypotheses are jointly satisfiable by a `length = 2` series, so the
  theorems are *not* vacuously quantified over an empty hypothesis space;
- applying `jordan_holder` / `jordan_holder_factors` to it yields `2 = 2` and a genuine
  permutation `σ : Fin 2 ≃ Fin 2` of the factor indices (the permutation content is live, not
  a `Fin 0`/`Fin 1` triviality);
- both `compositionFactor sJH i` are genuinely `IsSimpleModule ℚ …`, confirming the factors
  compared are real irreducibles, matching the book's `Wᵢ`.

## 5. Generality vs the book

The Lean statement quantifies over an arbitrary `[Ring A]`-module `V` (any ring, no
finite-dimensionality or algebra/field structure required). This is **strictly more general**
than the book's "finite-dimensional representation of an algebra `A` over a field `k`":

- The book's `A` is a `k`-algebra and `V` finite-dimensional over `k`; the Lean `A` is any ring
  and `V` any module. Every book instance is a Lean instance (a finite-dimensional
  representation is in particular an `A`-module over the ring `A`).
- No finiteness hypothesis is missing in a way that makes the statement *false*: the entire
  finite-length content is delivered through the *existence of the two composition series*
  (`head = ⊥`, `last = ⊤` with simple covering steps). Modules with no such series simply do not
  satisfy the hypotheses and the theorem says nothing about them — sound, and matching the
  book's reliance on finite-dimensionality to produce the filtrations. The §4 witness shows the
  hypotheses are non-emptily inhabited.

The Lean generalization also transparently covers the book's footnote caveat: the book gives two
proofs, the first (characters) only in characteristic 0, the second (induction on `dim V`)
general. Mathlib's `CompositionSeries.jordan_holder` is the general (characteristic-free,
ring-level) statement, so the formalization faithfully captures the theorem in the generality of
its *second* proof, with no characteristic restriction — a correct and honest choice.

## Conclusion

All three public declarations of `Theorem3_7_1.lean`, and the underlying
`compositionFactor` abbrev, are **FAITHFUL** to Etingof Theorem 3.7.1. The successive-quotient
factors are genuine simple modules, `Equivalent` is the honest permutation-plus-isomorphism
notion, and the length/factor corollaries are sound projections of the master equivalence.
Axioms are clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`), and a concrete
length-2 witness confirms non-vacuity: the hypotheses are satisfiable and the conclusions carry
real content (length 2, a live index permutation, two genuinely simple factors). **No defect;
no follow-up feature issue required.**
</content>
</invoke>

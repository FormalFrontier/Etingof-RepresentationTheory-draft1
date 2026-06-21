import Mathlib
import EtingofRepresentationTheory.Chapter5.PolynomialGLRightAction
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# The kernel lemma (K′): no nonneg-weight submodule of `(A/det) ⊗ χ⁻ʳ`

This file states the genuine representation-theoretic core (K′) of the
det⁻¹-elimination kernel lemma (K) (issue #4694, route doc
`progress/kernel-lemma-K-route.md`), phrased over the right-translation
`GL_N`-action `polyRightRep` on `A = k[Xᵢⱼ]` constructed in
`PolynomialGLRightAction.lean`.

## The objects

* `quotDetRep` — the induced right-`GL_N`-representation on the quotient
  `A/det = k[Xᵢⱼ]/(det)`. The principal ideal `(det)` is right-`GL_N`-stable
  (`Etingof.PolynomialGLAction.rTransAlgHom_mem_detIdeal`), so the right
  translation descends to the quotient. **This is the genuine object** (a real
  `Representation`, not a `sorry`'d placeholder) that (K′) analyses.
* `charTwistRep c ρ` — the twist of a representation `ρ` by a character
  `c : G →* kˣ`: `g ↦ c(g) • ρ(g)`.
* `detChar` — the determinant character `g ↦ det g : GL_N(k) →* kˣ`. Its
  right-torus weight is `(1,…,1)` (`det (diagUnit i t) = t`), so `χ⁻ʳ = detChar⁻ʳ`
  shifts every weight by `(−r,…,−r)`.
* `quotDetTwistRep r := charTwistRep (detChar⁻ʳ) quotDetRep` — the rep
  `(A/det) ⊗ χ⁻ʳ` of the route doc.
* `glWeightSpaceℤ ρ μ` — the (integer) weight space for `μ : Fin N → ℤ`, the
  ℤ-graded analogue of `Etingof.glWeightSpace` (which is indexed by `ℕ`-weights).

## The statement

`kernelLemmaK'` : for `r ≥ 1` the supremum of all **nonnegative**-weight spaces
of `(A/det) ⊗ χ⁻ʳ` is `⊥`. Equivalently (`kernelLemmaK'_submodule`), every
right-`GL_N`-submodule all of whose torus weights lie in `ℕ^N` is `⊥`.

This is the form the #4694 det-power-filtration assembly consumes: the assembly
produces a *nonzero* nonneg-weight submodule `W̄ ⊆ (A/det) ⊗ χ⁻ʳ`, and (K′)
contradicts it.

## Status

The mathematics of `kernelLemmaK'` is the `GL×GL`-equivariant **Cauchy
decomposition** `k[Xᵢⱼ] = ⊕_{ν ∈ ℕ^N dom} V_ν^* ⊠ V_ν` together with the
highest-weight shift `det · A ≅ A ⊗ χ`: `A/det` keeps exactly the constituents
with last highest-weight coordinate `ν_N = 0`, so after the `χ⁻ʳ` twist every
weight has last coordinate `ν_N − r = −r < 0`, i.e. no weight is `≥ 0`. This core
is a research-level effort tracked as a residual `sorry` here and decomposed in a
follow-up sub-issue; the present file fixes the precise statement and constructs
every object it is phrased over.
-/

namespace Etingof.KernelLemmaKPrime

open MvPolynomial Etingof.PolynomialGLAction

/-! ### The quotient representation `A/det` -/

variable {k : Type*} [CommRing k] {N : ℕ}

/-- The determinant principal ideal `(det)` viewed as a `k`-submodule of
`A = k[Xᵢⱼ]`, so the right translation (a `k`-linear map) can be quotiented by it. -/
noncomputable def detSubmodule (k : Type*) [CommRing k] (N : ℕ) :
    Submodule k (MvPolynomial (Fin N × Fin N) k) :=
  (Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)}).restrictScalars k

/-- The right translation preserves the determinant submodule (`(det)` is
right-`GL_N`-stable), so it descends to the quotient `A/det`. -/
theorem polyRightRep_mem_detSubmodule (g : Matrix.GeneralLinearGroup (Fin N) k)
    {f : MvPolynomial (Fin N × Fin N) k} (hf : f ∈ detSubmodule k N) :
    polyRightRep k N g f ∈ detSubmodule k N := by
  rw [detSubmodule, Submodule.restrictScalars_mem] at hf ⊢
  exact rTransAlgHom_mem_detIdeal _ hf

/-- The **right-translation representation on the quotient `A/det = k[Xᵢⱼ]/(det)`**.
Since the ideal `(det)` is right-`GL_N`-stable, the right translation
`polyRightRep` descends through `Submodule.mapQ` to a genuine representation on
the quotient. This is the object the kernel lemma (K′) analyses (after twisting
by `χ⁻ʳ`). -/
noncomputable def quotDetRep (k : Type*) [CommRing k] (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) where
  toFun g := Submodule.mapQ _ _ (polyRightRep k N g)
    (fun _ hx => polyRightRep_mem_detSubmodule g hx)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, map_one]
    rfl
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, map_mul]
    simp only [Module.End.mul_apply, Submodule.mapQ_apply]

@[simp] theorem quotDetRep_mk (g : Matrix.GeneralLinearGroup (Fin N) k)
    (f : MvPolynomial (Fin N × Fin N) k) :
    quotDetRep k N g (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (polyRightRep k N g f) :=
  rfl

/-! ### Character twist of a representation -/

variable {G V : Type*} [Monoid G] [AddCommMonoid V] [Module k V]

/-- The **character twist** of a representation `ρ` by a character `c : G →* kˣ`:
`g ↦ c(g) • ρ(g)`. This is `ρ ⊗ c` as a representation (the one-dimensional rep
of a character tensored on). -/
noncomputable def charTwistRep (c : G →* kˣ) (ρ : Representation k G V) :
    Representation k G V where
  toFun g := (c g : k) • ρ g
  map_one' := by simp
  map_mul' g₁ g₂ := by
    simp only [map_mul, Units.val_mul, smul_mul_smul_comm]

@[simp] theorem charTwistRep_apply (c : G →* kˣ) (ρ : Representation k G V)
    (g : G) (v : V) : charTwistRep c ρ g v = (c g : k) • ρ g v :=
  rfl

/-! ### The determinant character and the twisted quotient `(A/det) ⊗ χ⁻ʳ` -/

/-- The determinant character `χ : GL_N(k) →* kˣ`, `g ↦ det g`. Its right-torus
weight is `(1,…,1)`: `det (diagUnit i t) = t`. -/
noncomputable def detChar (k : Type*) [CommRing k] (N : ℕ) :
    Matrix.GeneralLinearGroup (Fin N) k →* kˣ :=
  Matrix.GeneralLinearGroup.det

/-- The representation `(A/det) ⊗ χ⁻ʳ`: the quotient `A/det` twisted by the
`(−r)`-th power of the determinant character. This is the rep the kernel lemma
(K′) is about. -/
noncomputable def quotDetTwistRep (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) :=
  charTwistRep (detChar k N ^ (-(r : ℤ))) (quotDetRep k N)

/-! ### Integer weight spaces -/

/-- The **integer weight space** `M_μ` for a weight `μ : Fin N → ℤ` in a
`GL_N(k)`-representation `ρ`: the subspace where the diagonal torus element
`diagUnit i t` acts as the scalar `t ^ μ i`, for every `i` and every `t ∈ kˣ`.
This is the ℤ-graded analogue of `Etingof.glWeightSpace` (whose weights are `ℕ`),
needed because the twist by `χ⁻ʳ` produces negative weights. -/
noncomputable def glWeightSpaceℤ (k : Type*) [Field k] (N : ℕ) {V : Type*}
    [AddCommGroup V] [Module k V]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (μ : Fin N → ℤ) : Submodule k V :=
  ⨅ (i : Fin N) (t : kˣ),
    LinearMap.ker (ρ (diagUnit k N i t) - (((t ^ μ i : kˣ) : k)) • LinearMap.id)

/-! ### The kernel lemma (K′) -/

/-- **Kernel lemma (K′).** For `r ≥ 1`, the supremum of all *nonnegative*-weight
spaces of the twisted quotient representation `(A/det) ⊗ χ⁻ʳ` is `⊥`: it has no
nonzero vector whose right-torus weight lies in `ℕ^N`.

The mathematics: by the `GL×GL`-equivariant Cauchy decomposition every
irreducible constituent of `A/det = k[Xᵢⱼ]/(det)` has last highest-weight
coordinate `ν_N = 0`; twisting by `χ⁻ʳ` (weight `(−r,…,−r)`) makes the last
coordinate `ν_N − r = −r < 0`, so no weight is `≥ 0`. This Cauchy-decomposition
core is tracked as a research-level residual `sorry` (follow-up sub-issue of
#4826); the statement and all the objects it quantifies over are in place. -/
theorem kernelLemmaK' (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    (r : ℕ) (hr : 1 ≤ r) :
    (⨆ (μ : Fin N → ℕ), glWeightSpaceℤ k N (quotDetTwistRep k N r)
      (fun i => (μ i : ℤ))) = ⊥ := by
  sorry

/-- Consumable form of (K′): every submodule of `(A/det) ⊗ χ⁻ʳ` all of whose
torus weights lie in `ℕ^N` (i.e. contained in the supremum of nonneg-weight
spaces) is `⊥`. This is what the #4694 det-power-filtration assembly contradicts:
it produces a *nonzero* such submodule. -/
theorem kernelLemmaK'_submodule (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    (N : ℕ) (r : ℕ) (hr : 1 ≤ r)
    {W : Submodule k (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N)}
    (hW : W ≤ ⨆ (μ : Fin N → ℕ),
      glWeightSpaceℤ k N (quotDetTwistRep k N r) (fun i => (μ i : ℤ))) :
    W = ⊥ :=
  le_bot_iff.mp (le_of_le_of_eq hW (kernelLemmaK' k N r hr))

end Etingof.KernelLemmaKPrime

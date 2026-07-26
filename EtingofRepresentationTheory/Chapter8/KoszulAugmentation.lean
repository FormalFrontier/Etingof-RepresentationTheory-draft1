import EtingofRepresentationTheory.Chapter8.KoszulDifferential
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The augmentation, freeness and basis-independence of the Koszul complex

Problem 8.2.10(i) asks for `C_• = SV ⊗ ⋀^• V` to be a *free* resolution of `k`, where `k` carries
the trivial `V`-action. `Chapter8/KoszulDifferential.lean` builds the complex itself; this file
supplies the three remaining pieces of the "free resolution" data, leaving only exactness.

* **The augmentation.** `k` becomes an `SV`-module through the counit
  `SymmetricAlgebra.algebraMapInv : SV →ₐ[k] k`, which kills `V`. That module is
  `Etingof.KoszulAugModule k V`, and `Etingof.koszulAug` is the induced `SV`-linear map
  `C₀ = SV ⊗ ⋀⁰ V → k`. It annihilates the image of `d₀`
  (`Etingof.koszulAug_comp_koszulD`), so the augmented complex really is a complex.

* **Freeness.** A `k`-basis of `⋀ⁱ V` base-changes to an `SV`-basis of `Cᵢ = SV ⊗[k] ⋀ⁱ V`
  (`Etingof.koszulXBasis`), so each `Cᵢ` is free, hence projective — the parenthetical
  "(in fact, free)" of the problem statement.

* **Basis-independence.** `Etingof.koszulD` is stated in terms of a chosen basis, but the book's
  `dᵢ(f)(u) = ιᵤ (f u)` is manifestly basis-free. The reconciliation is
  `Etingof.koszulD_one_tmul_ιMulti`, which evaluates `d` on the generators `1 ⊗ v₁ ∧ ⋯ ∧ v_{i+1}`
  with no basis in sight; since `d` is `SV`-linear and those generators span, this pins `d` down
  and gives `Etingof.koszulD_eq_of_basis`.

## Main definitions

* `Etingof.KoszulAugModule k V` — `k` as an `SV`-module with `V` acting by zero.
* `Etingof.koszulAug` — the augmentation `C₀ → k`.
* `Etingof.koszulXBasis` — the `SV`-basis of `Cᵢ` coming from a `k`-basis of `V`.

## Main results

* `Etingof.koszulAug_comp_koszulD` — `ε ∘ d₀ = 0`.
* `Etingof.koszulAug_surjective` — `ε` is onto, so the augmented complex ends correctly.
* `Etingof.koszulX_free`, `Etingof.koszulX_projective` — each `Cᵢ` is a free, hence projective,
  `SV`-module.
* `Etingof.koszulD_one_tmul_ιMulti` — the basis-free formula for `d` on generators.
* `Etingof.koszulD_eq_of_basis`, `Etingof.koszulComplex_eq_of_basis` — `d` and the whole complex
  do not depend on the chosen basis.
-/

universe u v w w'

open scoped TensorProduct

namespace Etingof

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

/-! ### `k` as the trivial `SV`-module -/

/-- **`k` with the trivial action of `V`**, the module that the Koszul complex resolves. The
symmetric algebra acts through its counit `SymmetricAlgebra.algebraMapInv : SV →ₐ[k] k`, so `V`
acts by zero. It is a `ULift` of `k` purely so that it lives in the same universe
`max u v` as `Etingof.koszulX k V i`, and can therefore sit at the end of the same complex.

The arguments are spelled out rather than taken from `variable`s because `V` occurs only in the
`SV`-module structure below, not in the underlying type. -/
def KoszulAugModule (k : Type u) [CommRing k] (V : Type v) [AddCommGroup V] [Module k V] :
    Type max u v := ULift.{v} k

namespace KoszulAugModule

instance : AddCommGroup (KoszulAugModule k V) := inferInstanceAs (AddCommGroup (ULift.{v} k))

instance : Module k (KoszulAugModule k V) := inferInstanceAs (Module k (ULift.{v} k))

/-- The trivial `SV`-module structure on `k`: `s • c = ε(s) · c`, where `ε` kills `V`. -/
noncomputable instance : Module (SymmetricAlgebra k V) (KoszulAugModule k V) :=
  Module.compHom (KoszulAugModule k V)
    (SymmetricAlgebra.algebraMapInv (R := k) (M := V)).toRingHom

variable (k V) in
/-- `KoszulAugModule k V` is `k` itself, as a `k`-module. -/
def equiv : KoszulAugModule k V ≃ₗ[k] k := ULift.moduleEquiv

@[simp]
theorem equiv_smul (s : SymmetricAlgebra k V) (x : KoszulAugModule k V) :
    equiv k V (s • x) = SymmetricAlgebra.algebraMapInv s * equiv k V x :=
  rfl

end KoszulAugModule

/-! ### The augmentation `ε : C₀ → k` -/

variable (k V) in
/-- The counit `SV → k` of the symmetric algebra, as a map of `SV`-modules (`k` carrying the
trivial action). -/
noncomputable def koszulAugHom :
    SymmetricAlgebra k V →ₗ[SymmetricAlgebra k V] KoszulAugModule k V where
  toFun s := (KoszulAugModule.equiv k V).symm (SymmetricAlgebra.algebraMapInv s)
  map_add' s t := by simp
  map_smul' s t := by
    apply (KoszulAugModule.equiv k V).injective
    simp [smul_eq_mul]

@[simp]
theorem koszulAugHom_apply (s : SymmetricAlgebra k V) :
    KoszulAugModule.equiv k V (koszulAugHom k V s) = SymmetricAlgebra.algebraMapInv s :=
  (KoszulAugModule.equiv k V).apply_symm_apply _

variable (k V) in
/-- **The augmentation of the Koszul complex**, `ε : C₀ = SV ⊗ ⋀⁰ V → k`. It is the counit
`SV → k` under the identification `⋀⁰ V ≃ k`, and is a map of `SV`-modules for the trivial
`SV`-action on `k`. -/
noncomputable def koszulAug : koszulX k V 0 →ₗ[SymmetricAlgebra k V] KoszulAugModule k V :=
  (koszulAugHom k V).comp
    ((TensorProduct.AlgebraTensorModule.rid k (SymmetricAlgebra k V)
        (SymmetricAlgebra k V)).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := SymmetricAlgebra k V))
        (exteriorPower.zeroEquiv k V).toLinearMap))

@[simp]
theorem koszulAug_tmul (s : SymmetricAlgebra k V) (w : ⋀[k]^0 V) :
    KoszulAugModule.equiv k V (koszulAug k V (s ⊗ₜ[k] w)) =
      exteriorPower.zeroEquiv k V w • SymmetricAlgebra.algebraMapInv s := by
  simp [koszulAug, map_smul]

/-- The augmentation is surjective: `ε (1 ⊗ 1) = 1`. -/
theorem koszulAug_surjective : Function.Surjective (koszulAug k V) := by
  intro y
  refine ⟨(algebraMap k (SymmetricAlgebra k V) (KoszulAugModule.equiv k V y)) ⊗ₜ[k]
    (exteriorPower.zeroEquiv k V).symm 1, ?_⟩
  apply (KoszulAugModule.equiv k V).injective
  simp

/-- **The augmented Koszul complex is a complex**: the augmentation kills the image of `d₀`.
Every term of `d₀` is multiplied by some `ι xₐ ∈ SV`, and the counit kills `V`. -/
theorem koszulAug_comp_koszulD {κ : Type w} [Fintype κ] (b : Module.Basis κ k V) :
    (koszulAug k V).comp (koszulD b 0) = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s w =>
      apply (KoszulAugModule.equiv k V).injective
      rw [koszulD_tmul]
      simp [SymmetricAlgebra.algebraMapInv_ι]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-! ### Freeness of the terms -/

variable (k V) in
/-- **The `SV`-basis of `Cᵢ = SV ⊗ ⋀ⁱ V`** obtained by base change from the standard `k`-basis
`{x_{j₁} ∧ ⋯ ∧ x_{jᵢ} : j₁ < ⋯ < jᵢ}` of `⋀ⁱ V`. This is the "(in fact, free)" of
Problem 8.2.10(i). -/
noncomputable def koszulXBasis {I : Type w} [LinearOrder I] (b : Module.Basis I k V) (i : ℕ) :
    Module.Basis (Set.powersetCard I i) (SymmetricAlgebra k V) (koszulX k V i) :=
  (b.exteriorPower i).baseChange (SymmetricAlgebra k V)

@[simp]
theorem koszulXBasis_apply {I : Type w} [LinearOrder I] (b : Module.Basis I k V) (i : ℕ)
    (s : Set.powersetCard I i) :
    koszulXBasis k V b i s = 1 ⊗ₜ[k] (b.exteriorPower i) s :=
  Module.Basis.baseChange_apply _ _ _

/-- Each term of the Koszul complex is a free `SV`-module. -/
instance koszulX_free [Module.Free k V] (i : ℕ) :
    Module.Free (SymmetricAlgebra k V) (koszulX k V i) := by
  obtain ⟨⟨I, c⟩⟩ := Module.Free.exists_basis (R := k) (M := ⋀[k]^i V)
  exact Module.Free.of_basis (c.baseChange (SymmetricAlgebra k V))

/-- Each term of the Koszul complex is a projective `SV`-module — the property
Problem 8.2.10(i) actually asserts. -/
instance koszulX_projective [Module.Free k V] (i : ℕ) :
    Module.Projective (SymmetricAlgebra k V) (koszulX k V i) :=
  Module.Projective.of_free

/-! ### Basis-independence of the differential -/

/-- An `SV`-linear map out of `Cᵢ = SV ⊗ ⋀ⁱ V` is determined by its values on the generators
`1 ⊗ v₁ ∧ ⋯ ∧ vᵢ`. -/
theorem koszulX_hom_ext {N : Type*} [AddCommGroup N] [Module (SymmetricAlgebra k V) N] {n : ℕ}
    {f g : koszulX k V n →ₗ[SymmetricAlgebra k V] N}
    (h : ∀ v : Fin n → V,
      f (1 ⊗ₜ[k] exteriorPower.ιMulti k n v) = g (1 ⊗ₜ[k] exteriorPower.ιMulti k n v)) :
    f = g := by
  have key : ∀ w : ⋀[k]^n V, f (1 ⊗ₜ[k] w) = g (1 ⊗ₜ[k] w) := by
    intro w
    have hw : w ∈ (⊤ : Submodule k (⋀[k]^n V)) := trivial
    rw [← exteriorPower.ιMulti_span k n] at hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨v, rfl⟩ := hx; exact h v
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    | smul c x _ hx =>
        have hc : (1 : SymmetricAlgebra k V) ⊗ₜ[k] (c • x)
            = (algebraMap k (SymmetricAlgebra k V) c) • ((1 : SymmetricAlgebra k V) ⊗ₜ[k] x) := by
          rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
          simp [Algebra.algebraMap_eq_smul_one]
        rw [hc, map_smul, map_smul, hx]
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s w =>
      have hs : s ⊗ₜ[k] w = s • ((1 : SymmetricAlgebra k V) ⊗ₜ[k] w) := by
        rw [TensorProduct.smul_tmul']; simp
      rw [hs, map_smul, map_smul, key]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {κ : Type w} [Fintype κ]

/-- **The book's basis-free formula for the Koszul differential.** On the generators
`1 ⊗ v₁ ∧ ⋯ ∧ v_{i+1}` of `Cᵢ₊₁`,

`d (1 ⊗ v₁ ∧ ⋯ ∧ v_{i+1}) = ∑ⱼ (-1)ʲ vⱼ ⊗ v₁ ∧ ⋯ v̂ⱼ ⋯ ∧ v_{i+1}`,

with no basis appearing. This is what makes `d` the book's `dᵢ(f)(u) = ιᵤ (f u)`: the
contraction's alternating sum is reassembled by `∑ₐ b.coord a (vⱼ) • b a = vⱼ`.

As in `Etingof.exteriorContraction_ιMulti`, `Fin (i + 1)` is 0-indexed, so the book's `(-1)ʲ`
for `j = 1, …, i + 1` appears below as `(-1) ^ (j + 1)`. -/
theorem koszulD_one_tmul_ιMulti (b : Module.Basis κ k V) (i : ℕ) (v : Fin (i + 1) → V) :
    koszulD b i (1 ⊗ₜ[k] exteriorPower.ιMulti k (i + 1) v) =
      ∑ j : Fin (i + 1), ((-1 : k) ^ ((j : ℕ) + 1)) •
        (SymmetricAlgebra.ι k V (v j) ⊗ₜ[k] exteriorPower.ιMulti k i (v ∘ j.succAbove)) := by
  rw [koszulD_tmul]
  simp only [mul_one, exteriorContraction_ιMulti, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- The basis is eliminated here: `v j` is reassembled from its coordinates,
  -- `∑ₐ b.coord a (v j) • b a = v j`.
  have hb : ∑ a : κ, (b.coord a) (v j) • SymmetricAlgebra.ι k V (b a)
      = SymmetricAlgebra.ι k V (v j) := by
    simp only [← map_smul, ← map_sum]
    congr 1
    simp [b.sum_repr (v j)]
  simp only [mul_smul, ← Finset.smul_sum]
  congr 1
  rw [← hb, TensorProduct.sum_tmul]
  exact Finset.sum_congr rfl fun a _ => (TensorProduct.smul_tmul' _ _ _).symm

/-- **The Koszul differential does not depend on the chosen basis.** Both sides satisfy the
basis-free formula `koszulD_one_tmul_ιMulti` on generators, and an `SV`-linear map out of `Cᵢ₊₁`
is determined by those values. -/
theorem koszulD_eq_of_basis {κ' : Type w'} [Fintype κ'] (b : Module.Basis κ k V)
    (b' : Module.Basis κ' k V) (i : ℕ) : koszulD b i = koszulD b' i :=
  koszulX_hom_ext fun v => by
    rw [koszulD_one_tmul_ιMulti, koszulD_one_tmul_ιMulti]

/-- The Koszul complex itself does not depend on the chosen basis. -/
theorem koszulComplex_eq_of_basis {κ' : Type w'} [Fintype κ'] (b : Module.Basis κ k V)
    (b' : Module.Basis κ' k V) : koszulComplex b = koszulComplex b' := by
  refine HomologicalComplex.ext rfl ?_
  rintro i j (rfl : j + 1 = i)
  simp only [koszulComplex_d, koszulD_eq_of_basis b b' j]
  simp

end Etingof

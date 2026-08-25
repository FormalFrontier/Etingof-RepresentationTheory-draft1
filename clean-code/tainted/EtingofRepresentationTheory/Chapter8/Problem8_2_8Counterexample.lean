import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.LinearMap.FiniteRange
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Problem 8.2.8: why the `Ext` Künneth formula needs finite dimensionality

The book's Problem 8.2.8 states the `Ext` Künneth formula
`Extⁱ_{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Extʲ_{A₁}(M₁, N₁) ⊗ₖ Extᵐ_{A₂}(M₂, N₂)`
assuming only that the target modules `Nᵢ` are finite dimensional. **That literal statement is
false.** Already in degree zero, over `A₁ = A₂ = k` and `N₁ = N₂ = k`, it reduces to the claim that
the canonical map

`M₁* ⊗ₖ M₂* → (M₁ ⊗ₖ M₂)*`

(`TensorProduct.dualDistrib`) is an isomorphism, and this fails as soon as the `Mᵢ` are infinite
dimensional: the map is injective but **not surjective**. This is exactly why the formalized theorem
`Etingof.Problem_8_2_8_ext` (in `Problem8_2_8.lean`) adds finite dimensionality of the `Mᵢ` (which
lets the resolving projectives be finitely generated). See also `skipped-exercises.md`.

## Main result

`TensorProduct.dualDistrib_not_surjective`: for the countably-infinite-dimensional space
`V = ℕ →₀ k` over a field `k`, the canonical map `dualDistrib k V V : V* ⊗ₖ V* → (V ⊗ₖ V)*` is not
surjective.

## Proof idea

The "diagonal" functional `Ψ : (V ⊗ V)*` with `Ψ (eᵢ ⊗ eⱼ) = δᵢⱼ` is not in the image. Any
element `t : V* ⊗ V*` is a finite sum `∑ fₐ ⊗ gₐ`, so the associated slot map
`x ↦ (y ↦ dualDistrib t (x ⊗ y))` has range inside the finite-dimensional span of the `gₐ`
(`LinearMap.HasNoetherianRange`). If `dualDistrib t = Ψ`, then this range would contain every
coordinate functional `eᵢ*` (because `y ↦ Ψ (eᵢ ⊗ y) = eᵢ*`), and the `eᵢ*` form an infinite
linearly independent family — impossible inside a Noetherian (here finite-dimensional) submodule.
-/

open TensorProduct LinearMap

namespace Etingof.Problem_8_2_8

universe u

variable (k : Type u) [Field k]

/-- The canonical "slot" map: `diagCurry k t` sends `x` to the functional `y ↦ dualDistrib t
(x ⊗ y)`. On a simple tensor `f ⊗ g` it is `x ↦ f x • g`, a rank-`≤ 1` operator; the point is that
`diagCurry k t` always has finitely generated (indeed finite-dimensional) range. -/
noncomputable def diagCurry :
    Module.Dual k (ℕ →₀ k) ⊗[k] Module.Dual k (ℕ →₀ k) →ₗ[k]
      ((ℕ →₀ k) →ₗ[k] Module.Dual k (ℕ →₀ k)) :=
  TensorProduct.lift LinearMap.smulRightₗ

variable {k}

@[simp]
theorem diagCurry_tmul (f g : Module.Dual k (ℕ →₀ k)) :
    diagCurry k (f ⊗ₜ[k] g) = f.smulRight g :=
  TensorProduct.lift.tmul f g

/-- `diagCurry` computes the same pairing as `dualDistrib`: `diagCurry k t x y = dualDistrib t
(x ⊗ y)`. -/
theorem diagCurry_apply_apply (t : Module.Dual k (ℕ →₀ k) ⊗[k] Module.Dual k (ℕ →₀ k))
    (x y : ℕ →₀ k) :
    diagCurry k t x y = TensorProduct.dualDistrib k (ℕ →₀ k) (ℕ →₀ k) t (x ⊗ₜ[k] y) := by
  induction t with
  | zero => simp
  | tmul f g => simp [smul_eq_mul]
  | add a b ha hb => simp [ha, hb]

/-- The slot map of any `t` has Noetherian (finitely generated) range: it is a finite sum of
rank-`≤ 1` operators. -/
theorem hasNoetherianRange_diagCurry
    (t : Module.Dual k (ℕ →₀ k) ⊗[k] Module.Dual k (ℕ →₀ k)) :
    (diagCurry k t).HasNoetherianRange := by
  induction t with
  | zero =>
      rw [map_zero]
      change IsNoetherian k ↥(LinearMap.range (0 : (ℕ →₀ k) →ₗ[k] Module.Dual k (ℕ →₀ k)))
      rw [LinearMap.range_zero]
      infer_instance
  | tmul f g =>
      have hle : LinearMap.range (diagCurry k (f ⊗ₜ[k] g)) ≤ Submodule.span k {g} := by
        rw [diagCurry_tmul]
        rintro _ ⟨v, rfl⟩
        simpa [LinearMap.smulRight_apply] using
          Submodule.smul_mem _ (f v) (Submodule.mem_span_singleton_self g)
      haveI : IsNoetherian k ↥(Submodule.span k {g}) :=
        isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_singleton g))
      exact isNoetherian_of_le hle
  | add a b ha hb =>
      rw [map_add]
      exact ha.add hb

end Etingof.Problem_8_2_8

open Etingof.Problem_8_2_8 in
/-- **Non-surjectivity witnessing the false scope of Problem 8.2.8.**
For the countably-infinite-dimensional space `V = ℕ →₀ k` over a field, the canonical map
`V* ⊗ₖ V* → (V ⊗ₖ V)*` is not surjective. This is the degree-zero heart of why the book's `Ext`
Künneth formula (which assumes only the `Nᵢ` finite dimensional) fails without finite dimensionality
of the source modules. -/
theorem TensorProduct.dualDistrib_not_surjective (k : Type u) [Field k] :
    ¬ Function.Surjective
      (TensorProduct.dualDistrib k (ℕ →₀ k) (ℕ →₀ k)) := by
  intro hsurj
  -- The diagonal functional `Ψ (eᵢ ⊗ eⱼ) = δᵢⱼ`, built from the coordinate functionals.
  set D : (ℕ →₀ k) →ₗ[k] Module.Dual k (ℕ →₀ k) :=
    Finsupp.linearCombination k (fun i => Finsupp.lapply i) with hD
  set Ψ : Module.Dual k ((ℕ →₀ k) ⊗[k] (ℕ →₀ k)) := TensorProduct.lift D with hΨ
  obtain ⟨t, ht⟩ := hsurj Ψ
  -- The slot map of `t` has Noetherian range.
  haveI : IsNoetherian k ↥(LinearMap.range (diagCurry k t)) := hasNoetherianRange_diagCurry t
  -- Every coordinate functional lies in that range: `diagCurry k t (eᵢ) = eᵢ*`.
  have hmem : ∀ i, (Finsupp.lapply i : Module.Dual k (ℕ →₀ k)) ∈
      LinearMap.range (diagCurry k t) := by
    intro i
    refine ⟨Finsupp.single i 1, ?_⟩
    refine LinearMap.ext fun y => ?_
    rw [diagCurry_apply_apply, ht, hΨ, TensorProduct.lift.tmul, hD,
      Finsupp.linearCombination_single, one_smul]
  -- The coordinate functionals are linearly independent.
  have hli : LinearIndependent k (fun i : ℕ => (Finsupp.lapply i : Module.Dual k (ℕ →₀ k))) := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have h0 : (∑ j ∈ s, c j • Finsupp.lapply (R := k) (M := k) j) (Finsupp.single i 1) = 0 := by
      rw [hsum]; simp
    simpa [Finsupp.single_apply, Finset.sum_ite_eq, hi] using h0
  -- Transport them into the (Noetherian) range submodule, where an infinite independent family
  -- cannot exist.
  set W := LinearMap.range (diagCurry k t)
  set w : ℕ → W := fun i => ⟨Finsupp.lapply i, hmem i⟩ with hw
  have hwli : LinearIndependent k w := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent k (fun i : ℕ => (Finsupp.lapply i : Module.Dual k (ℕ →₀ k)))
    exact hli
  haveI : Finite ℕ := hwli.finite_of_isNoetherian
  exact not_finite ℕ

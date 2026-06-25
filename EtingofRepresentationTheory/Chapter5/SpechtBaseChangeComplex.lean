import Mathlib
import EtingofRepresentationTheory.Chapter5.SpechtCharacterGeneral

/-!
# Scalar extension of Specht modules: `ℂ ⊗_ℚ V_λ(ℚ) ≅ V_λ(ℂ)`

The Specht module `SpechtModuleK k n la = k[S_n]·c_λ` is defined uniformly over any
commutative ring `k` from the **integer** Young symmetrizer `c_ℤ` (`YoungSymmetrizerZ`).
This file proves the **base-change compatibility** asked for by the "uniform real type"
route: the complex Specht module has a *rational form*, namely there is a
`ℂ`-linear `S_n`-equivariant isomorphism

```
ℂ ⊗_ℚ SpechtModuleK ℚ n la  ≃  SpechtModuleK ℂ n la.
```

Combined with the classification "every `ℂ`-irrep of `S_n` is a Specht module"
(Theorem 5.12.2 area) and the L1 rational-form linchpin
(`Etingof.isRealType_of_rational_form`, from the Frobenius-Schur package), this gives
"every irreducible representation of `S_n` is of real type" for all `n` at once,
without analysing each partition separately.

## Construction

Write `Aℚ = ℚ[S_n]`, `Aℂ = ℂ[S_n]`, and `j : Aℚ →+* Aℂ` for the coefficient base change
`mapRingHom (algebraMap ℚ ℂ)`. The map

```
Ψ : ℂ ⊗_ℚ ↥(SpechtModuleK ℚ n la) →ₗ[ℂ] Aℂ,   Ψ (z ⊗ v) = z • j v
```

is `LinearMap.liftBaseChange ℂ` of the `ℚ`-linear `g : ↥V_λ(ℚ) →ₗ[ℚ] Aℂ`, `v ↦ j v`.

* **Range** `= V_λ(ℂ)`: by `LinearMap.range_liftBaseChange` the range is the `ℂ`-span of
  `j '' V_λ(ℚ)`; the span argument (`j (c_ℚ) = c_ℂ`, `j` multiplicative) identifies it with
  the left ideal `Aℂ·c_ℂ = SpechtModuleK ℂ n la`.
* **Injective**: `Ψ` factors as `finsuppScalarRight ∘ lTensor ℂ (incl)`, and `lTensor ℂ` of
  the injective inclusion `V_λ(ℚ) ↪ Aℚ` is injective because `ℂ` is **flat** (free) over `ℚ`
  (`Module.Flat.lTensor_preserves_injective_linearMap`); `finsuppScalarRight` is an equiv.
* **Equivariance**: `j (of σ * x) = of σ * j x` makes `Ψ` intertwine the base-changed
  `ℚ`-action `1 ⊗ ρ_ℚ(σ)` with the `ℂ`-action `ρ_ℂ(σ)` (both the `spechtModuleActionK`
  left-multiplications by `of σ`).
-/

noncomputable section

namespace Etingof

open scoped TensorProduct
open MonoidAlgebra

variable (n : ℕ) (la : Nat.Partition n)

/-- The coefficient base-change ring hom `ℚ[S_n] →+* ℂ[S_n]`. -/
private abbrev jHom : MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →+*
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ ℂ)

/-- `j (of σ) = of σ`. -/
private lemma jHom_of (σ : Equiv.Perm (Fin n)) :
    jHom n (MonoidAlgebra.of ℚ _ σ) = MonoidAlgebra.of ℂ _ σ := by
  change MonoidAlgebra.mapRingHom _ _ (Finsupp.single σ 1) = Finsupp.single σ 1
  rw [MonoidAlgebra.mapRingHom_single, map_one]

/-- `j (c_λ over ℚ) = c_λ over ℂ`. -/
private lemma jHom_youngSymmetrizer :
    jHom n (YoungSymmetrizerK ℚ n la) = YoungSymmetrizerK ℂ n la := by
  rw [YoungSymmetrizerK_eq_mapRange ℚ n la, YoungSymmetrizerK_eq_mapRange ℂ n la]
  ext g
  simp only [jHom, MonoidAlgebra.mapRingHom_apply]
  norm_cast

/-- `j` as a `ℚ`-linear map (every additive map between `ℚ`-vector spaces is `ℚ`-linear). -/
private def jLin : MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →ₗ[ℚ]
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (jHom n).toAddMonoidHom.toRatLinearMap

private lemma jLin_apply (x : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) :
    jLin n x = jHom n x := rfl

/-- The `ℚ`-linear map `g : ↥V_λ(ℚ) →ₗ[ℚ] ℂ[S_n]`, `v ↦ j v`. -/
private def gMap : ↥(SpechtModuleK ℚ n la) →ₗ[ℚ] MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (jLin n).comp ((SpechtModuleK ℚ n la).subtype.restrictScalars ℚ)

private lemma gMap_apply (v : ↥(SpechtModuleK ℚ n la)) :
    gMap n la v = jHom n (v : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) := rfl

/-- The scalar-extension map `Ψ : ℂ ⊗_ℚ ↥V_λ(ℚ) →ₗ[ℂ] ℂ[S_n]`, `z ⊗ v ↦ z • j v`. -/
private def psiMap :
    ℂ ⊗[ℚ] ↥(SpechtModuleK ℚ n la) →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (gMap n la).liftBaseChange ℂ

private lemma psiMap_tmul (z : ℂ) (v : ↥(SpechtModuleK ℚ n la)) :
    psiMap n la (z ⊗ₜ[ℚ] v) = z • jHom n (v : MonoidAlgebra ℚ (Equiv.Perm (Fin n))) := by
  rw [psiMap, LinearMap.liftBaseChange_tmul, gMap_apply]

/-! ### Injectivity via flatness -/

private lemma psiMap_injective : Function.Injective (psiMap n la) := by
  classical
  -- `Ψ = finsuppScalarRight ∘ lTensor ℂ (incl)`, both injective.
  have hincl_inj : Function.Injective
      ((SpechtModuleK ℚ n la).subtype.restrictScalars ℚ) := by
    intro a b hab
    exact Subtype.ext hab
  have hlT : Function.Injective
      (LinearMap.lTensor ℂ ((SpechtModuleK ℚ n la).subtype.restrictScalars ℚ)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hincl_inj
  set F := TensorProduct.finsuppScalarRight ℚ ℂ ℂ (Equiv.Perm (Fin n)) with hF
  have hcomp : ∀ t, psiMap n la t =
      F (LinearMap.lTensor ℂ ((SpechtModuleK ℚ n la).subtype.restrictScalars ℚ) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z v =>
      rw [psiMap_tmul, LinearMap.lTensor_tmul]
      ext g
      rw [TensorProduct.finsuppScalarRight_apply_tmul_apply, Finsupp.smul_apply, smul_eq_mul,
        jHom, MonoidAlgebra.mapRingHom_apply]
      simp only [LinearMap.coe_restrictScalars, Submodule.coe_subtype]
      rw [Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hcompose : Function.Injective
      (fun t => F (LinearMap.lTensor ℂ
        ((SpechtModuleK ℚ n la).subtype.restrictScalars ℚ) t)) :=
    F.injective.comp hlT
  rw [show (psiMap n la : _ → _) = fun t => F (LinearMap.lTensor ℂ
      ((SpechtModuleK ℚ n la).subtype.restrictScalars ℚ) t) from funext hcomp]
  exact hcompose

/-! ### Range equals the complex Specht module -/

private lemma psiMap_range :
    LinearMap.range (psiMap n la) = (SpechtModuleK ℂ n la).restrictScalars ℂ := by
  classical
  rw [psiMap, LinearMap.range_liftBaseChange]
  -- `T := span ℂ (range g)` — show `T = V_λ(ℂ)` as `ℂ`-submodules of `ℂ[S_n]`.
  apply le_antisymm
  · -- `span ℂ (range g) ≤ V_λ(ℂ)`
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp v.2
    rw [gMap_apply, ← ha, smul_eq_mul, map_mul, jHom_youngSymmetrizer]
    exact Submodule.mem_span_singleton.mpr ⟨jHom n a, rfl⟩
  · -- `V_λ(ℂ) ≤ span ℂ (range g)`
    set T := Submodule.span ℂ (↑(LinearMap.range (gMap n la)) :
      Set (MonoidAlgebra ℂ (Equiv.Perm (Fin n)))) with hT
    -- every `b * c_ℂ` lies in `T`
    have hmul : ∀ b : MonoidAlgebra ℂ (Equiv.Perm (Fin n)),
        b * YoungSymmetrizerK ℂ n la ∈ T := by
      intro b
      induction b using Finsupp.induction_linear with
      | zero => rw [zero_mul]; exact T.zero_mem
      | add x y hx hy => rw [add_mul]; exact T.add_mem hx hy
      | single σ r =>
        have hsingle : (Finsupp.single σ r : MonoidAlgebra ℂ _)
            = r • MonoidAlgebra.of ℂ _ σ := by
          simp [MonoidAlgebra.of_apply, mul_one]
        rw [hsingle, smul_mul_assoc]
        refine T.smul_mem r ?_
        -- `of σ * c_ℂ = g ⟨of σ * c_ℚ, _⟩ ∈ range g ⊆ T`
        have hmem : MonoidAlgebra.of ℚ _ σ * YoungSymmetrizerK ℚ n la ∈ SpechtModuleK ℚ n la :=
          Submodule.smul_mem _ (MonoidAlgebra.of ℚ _ σ) (Submodule.subset_span rfl)
        have hval : MonoidAlgebra.of ℂ _ σ * YoungSymmetrizerK ℂ n la
            = gMap n la ⟨MonoidAlgebra.of ℚ _ σ * YoungSymmetrizerK ℚ n la, hmem⟩ := by
          rw [gMap_apply, map_mul, jHom_of, jHom_youngSymmetrizer]
        rw [hval]
        exact Submodule.subset_span (LinearMap.mem_range_self _ _)
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [smul_eq_mul]
    exact hmul b

/-! ### The base-change isomorphism and its `S_n`-equivariance -/

/-- **Scalar extension of the Specht module.** The `ℂ`-linear isomorphism

```
ℂ ⊗_ℚ SpechtModuleK ℚ n la  ≃  SpechtModuleK ℂ n la,
```

obtained by corestricting the injective scalar-extension map `Ψ` to its range
`SpechtModuleK ℂ n la`. This exhibits the complex Specht module as the complexification
of its rational form. -/
def spechtComplexRatBaseChangeEquiv :
    ℂ ⊗[ℚ] ↥(SpechtModuleK ℚ n la) ≃ₗ[ℂ] ↥(SpechtModuleK ℂ n la) :=
  (LinearEquiv.ofInjective (psiMap n la) (psiMap_injective n la)).trans
    (LinearEquiv.ofEq _ _ (psiMap_range n la))

@[simp]
private lemma spechtComplexRatBaseChangeEquiv_coe (t : ℂ ⊗[ℚ] ↥(SpechtModuleK ℚ n la)) :
    ((spechtComplexRatBaseChangeEquiv n la t : ↥(SpechtModuleK ℂ n la)) :
      MonoidAlgebra ℂ (Equiv.Perm (Fin n))) = psiMap n la t := rfl

/-- **`S_n`-equivariance of the base-change isomorphism.** The isomorphism intertwines the
base-changed `ℚ`-action `1 ⊗ ρ_ℚ(σ)` (left multiplication by `of σ` on the rational Specht
module, tensored up) with the `ℂ`-action `ρ_ℂ(σ)` (left multiplication by `of σ` on the
complex Specht module). Hence it is an isomorphism of `S_n`-representations. -/
theorem spechtComplexRatBaseChangeEquiv_equivariant (σ : Equiv.Perm (Fin n)) :
    (spechtComplexRatBaseChangeEquiv n la).toLinearMap ∘ₗ
        LinearMap.baseChange ℂ (spechtModuleActionK ℚ n la σ)
      = (spechtModuleActionK ℂ n la σ) ∘ₗ
        (spechtComplexRatBaseChangeEquiv n la).toLinearMap := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z v =>
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      spechtComplexRatBaseChangeEquiv_coe, psiMap_tmul]
    -- both sides equal `of σ * (z • j v)` in `ℂ[S_n]`
    change z • jHom n (MonoidAlgebra.of ℚ _ σ * (v : MonoidAlgebra ℚ (Equiv.Perm (Fin n))))
      = MonoidAlgebra.of ℂ _ σ * (z • jHom n (v : MonoidAlgebra ℚ (Equiv.Perm (Fin n))))
    rw [map_mul, jHom_of, mul_smul_comm]
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

end Etingof

end

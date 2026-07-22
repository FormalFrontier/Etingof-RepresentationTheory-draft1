import Mathlib
import EtingofRepresentationTheory.Infrastructure.SpechtModuleSimple
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Classification

/-!
# Corollary 5.12.4: Rational Representation Matrices

All irreducible representations of `S_n` over `ℂ` can be given by matrices with rational
entries. Following Etingof, the proof rests on the integrality of the Young symmetrizer
`c_λ ∈ ℤ[S_n]`: the rational Specht module `V_λ^ℚ = ℚ[S_n]·c_λ` is a genuine `ℚ`-form of
the complex Specht module `V_λ = ℂ[S_n]·c_λ`.

## Main results

* `Etingof.SpechtModule_complexification` — for each partition `λ`, the complexification
  `ℂ ⊗_ℚ V_λ^ℚ` is isomorphic to `V_λ` via a `ℂ`-linear `S_n`-equivariant isomorphism.
* `Etingof.Corollary5_12_4` — every simple `ℂ[S_n]`-module `M` is the Specht module `V_λ`
  for some `λ` (classification), `V_λ^ℚ` is a simple `ℚ[S_n]`-module (an irreducible
  representation defined over `ℚ`), and `V_λ` is the complexification of `V_λ^ℚ`.

## Proof strategy

The key map is `T : ℂ ⊗_ℚ (ℚ[S_n]·c_λ) → ℂ[S_n]`, built as the base change of the
inclusion `ℚ[S_n]·c_λ ↪ ℚ[S_n]` along `ℚ → ℂ` followed by the module-level base-change
isomorphism `ℂ ⊗_ℚ ℚ[S_n] ≃ ℂ[S_n]` (`TensorProduct.finsuppScalarRight`). It is injective
because `ℂ` is flat (free) over `ℚ`, and its image is exactly `V_λ`, so it corestricts to
an isomorphism. Because `T(z ⊗ w) = z · (cast w)`, the isomorphism intertwines the
`S_n`-action, which is precisely what "given by rational matrices" means.

## Mathlib correspondence

Built on the Specht-module construction over a general field (`SpechtModuleK`), the
classification of complex irreducibles (`Theorem5_12_2_classification`), and the
simplicity of the rational Specht module (`SpechtModuleK_isSimpleModule`).
-/

open scoped TensorProduct

namespace Etingof

noncomputable section

variable (n : ℕ) (la : Nat.Partition n)

/-- Coefficient cast `ℚ[Sₙ] → ℂ[Sₙ]`. -/
private abbrev castQC (n : ℕ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) →+* MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (algebraMap ℚ ℂ)

/-- The cast of the rational Young symmetrizer is the complex one. -/
private theorem castQC_young (n : ℕ) (la : Nat.Partition n) :
    castQC n (YoungSymmetrizerK ℚ n la) = YoungSymmetrizer n la := by
  rw [YoungSymmetrizerK_eq_mapRange, YoungSymmetrizer_eq_mapRange]
  ext x
  simp only [castQC, MonoidAlgebra.mapRingHom_apply, eq_intCast]
  norm_cast

/-- The complexification map `T : ℂ ⊗_ℚ (ℚ[Sₙ]·c) → ℂ[Sₙ]`. -/
private def Tmap (n : ℕ) (la : Nat.Partition n) :
    (ℂ ⊗[ℚ] (SpechtModuleK ℚ n la)) →ₗ[ℂ] (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :=
  (TensorProduct.finsuppScalarRight ℚ ℂ ℂ (Equiv.Perm (Fin n))).toLinearMap ∘ₗ
    LinearMap.baseChange ℂ (((SpechtModuleK ℚ n la).subtype).restrictScalars ℚ)

private theorem Tmap_tmul (z : ℂ) (w : SpechtModuleK ℚ n la) :
    Tmap n la (z ⊗ₜ[ℚ] w) = z • (castQC n (w : MonoidAlgebra ℚ (Equiv.Perm (Fin n)))) := by
  ext g
  change (TensorProduct.finsuppScalarRight ℚ ℂ ℂ (Equiv.Perm (Fin n)))
      (LinearMap.baseChange ℂ (((SpechtModuleK ℚ n la).subtype).restrictScalars ℚ)
        (z ⊗ₜ[ℚ] w)) g = _
  rw [LinearMap.baseChange_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply,
    Finsupp.smul_apply, MonoidAlgebra.mapRingHom_apply, smul_eq_mul, Algebra.smul_def, mul_comm]
  rfl

private theorem Tmap_injective : Function.Injective (Tmap n la) := by
  have h : Function.Injective
      (((SpechtModuleK ℚ n la).subtype).restrictScalars ℚ) := Subtype.coe_injective
  have hbc : Function.Injective
      ⇑(LinearMap.baseChange ℂ (((SpechtModuleK ℚ n la).subtype).restrictScalars ℚ)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ h
  exact (TensorProduct.finsuppScalarRight ℚ ℂ ℂ (Equiv.Perm (Fin n))).injective.comp hbc

/-- The cast maps the rational Specht module into the complex one. -/
private theorem castQC_mem_spechtModule (y : MonoidAlgebra ℚ (Equiv.Perm (Fin n)))
    (hy : y ∈ SpechtModuleK ℚ n la) :
    castQC n y ∈ SpechtModule n la := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [castQC_young]
    exact Submodule.subset_span rfl
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact (SpechtModule n la).add_mem ha hb
  | smul a b _ hb =>
    rw [smul_eq_mul, map_mul]
    exact (SpechtModule n la).smul_mem (castQC n a) hb

/-- `T` lands in the complex Specht module. -/
private theorem Tmap_mem (x : ℂ ⊗[ℚ] (SpechtModuleK ℚ n la)) :
    Tmap n la x ∈ SpechtModule n la := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z w =>
    rw [Tmap_tmul]
    exact (SpechtModule n la).smul_of_tower_mem z (castQC_mem_spechtModule n la _ w.2)
  | add a b ha hb => rw [map_add]; exact (SpechtModule n la).add_mem ha hb

/-- The cast of `of g` is `of g`. -/
private theorem castQC_of (g : Equiv.Perm (Fin n)) :
    castQC n (MonoidAlgebra.of ℚ (Equiv.Perm (Fin n)) g)
      = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g := by
  change MonoidAlgebra.mapRingHom _ _ (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1
  rw [MonoidAlgebra.mapRingHom_single, map_one]

/-- Pointwise `Sₙ`-equivariance of `T` on simple tensors. -/
private theorem Tmap_smul_of (g : Equiv.Perm (Fin n)) (z : ℂ) (w : SpechtModuleK ℚ n la) :
    MonoidAlgebra.of ℂ _ g • (Tmap n la (z ⊗ₜ[ℚ] w))
      = Tmap n la (z ⊗ₜ[ℚ] (MonoidAlgebra.of ℚ _ g • w)) := by
  rw [Tmap_tmul, Tmap_tmul, Submodule.coe_smul]
  conv_rhs => rw [show (MonoidAlgebra.of ℚ (Equiv.Perm (Fin n)) g • (↑w : MonoidAlgebra ℚ _))
      = MonoidAlgebra.of ℚ _ g * ↑w from rfl, map_mul, castQC_of]
  rw [smul_comm (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g) z, smul_eq_mul]

/-- The `ℚ`-linear endomorphism of `V_λ^ℚ` given by left multiplication by `of g`. -/
private def lgMap (g : Equiv.Perm (Fin n)) :
    (SpechtModuleK ℚ n la) →ₗ[ℚ] (SpechtModuleK ℚ n la) :=
  DistribSMul.toLinearMap ℚ (SpechtModuleK ℚ n la) (MonoidAlgebra.of ℚ _ g)

/-- `Sₙ`-equivariance of `T` for all elements, not just simple tensors. -/
private theorem Tmap_smul_of_all (g : Equiv.Perm (Fin n)) (x : ℂ ⊗[ℚ] (SpechtModuleK ℚ n la)) :
    MonoidAlgebra.of ℂ _ g • (Tmap n la x)
      = Tmap n la (LinearMap.baseChange ℂ (lgMap n la g) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z w =>
    rw [LinearMap.baseChange_tmul, Tmap_smul_of]
    rfl
  | add a b ha hb => rw [map_add, map_add, smul_add, ha, hb, map_add]

/-- The range of `T` is closed under the `ℂ[Sₙ]`-action. -/
private theorem Tmap_range_smul_mem (a : MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
    (y : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (hy : y ∈ LinearMap.range (Tmap n la)) :
    a • y ∈ LinearMap.range (Tmap n la) := by
  obtain ⟨x, rfl⟩ := hy
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
    rw [Tmap_smul_of_all]
    exact LinearMap.mem_range_self _ _
  | hadd a b ha hb => rw [add_smul]; exact (LinearMap.range _).add_mem ha hb
  | hsmul r a ha =>
    rw [smul_assoc]
    exact (LinearMap.range _).smul_mem r ha

/-- The complex Specht module is contained in the range of `T` (surjectivity). -/
private theorem spechtModule_le_range :
    (SpechtModule n la).restrictScalars ℂ ≤ LinearMap.range (Tmap n la) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rw [Set.mem_singleton_iff] at hv
    subst hv
    refine ⟨1 ⊗ₜ[ℚ] ⟨YoungSymmetrizerK ℚ n la, Submodule.subset_span rfl⟩, ?_⟩
    rw [Tmap_tmul, one_smul, castQC_young]
  | zero => exact (LinearMap.range _).zero_mem
  | add a b _ _ ha hb => exact (LinearMap.range _).add_mem ha hb
  | smul a b _ hb => exact Tmap_range_smul_mem n la a b hb

/-- The complexification isomorphism `ℂ ⊗_ℚ V_λ^ℚ ≃ V_λ`, as a `ℂ`-linear equivalence. -/
private def complexificationEquiv :
    (ℂ ⊗[ℚ] (SpechtModuleK ℚ n la)) ≃ₗ[ℂ] (SpechtModule n la) :=
  LinearEquiv.ofBijective
    ((Tmap n la).codRestrict ((SpechtModule n la).restrictScalars ℂ) (Tmap_mem n la))
    ⟨fun a b h => Tmap_injective n la (Subtype.ext_iff.mp h),
     fun v => by
       obtain ⟨x, hx⟩ := spechtModule_le_range n la v.2
       exact ⟨x, Subtype.ext hx⟩⟩

private theorem complexificationEquiv_apply (x : ℂ ⊗[ℚ] (SpechtModuleK ℚ n la)) :
    (complexificationEquiv n la x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) = Tmap n la x := rfl

/-- **The rational form of the Specht module.** The complexification of the rational Specht
module `V_λ^ℚ = ℚ[Sₙ]·c_λ` is the complex Specht module `V_λ = ℂ[Sₙ]·c_λ`, via a `ℂ`-linear
isomorphism intertwining the `Sₙ`-action. Since `V_λ^ℚ` is a representation over `ℚ`, this
exhibits `V_λ` as realizable by rational matrices. -/
theorem SpechtModule_complexification (n : ℕ) (la : Nat.Partition n) :
    ∃ e : (ℂ ⊗[ℚ] (SpechtModuleK ℚ n la)) ≃ₗ[ℂ] (SpechtModule n la),
      ∀ (g : Equiv.Perm (Fin n)) (z : ℂ) (w : SpechtModuleK ℚ n la),
        (e (z ⊗ₜ[ℚ] (MonoidAlgebra.of ℚ _ g • w))
            : MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
          = MonoidAlgebra.of ℂ _ g •
              (e (z ⊗ₜ[ℚ] w) : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) := by
  refine ⟨complexificationEquiv n la, fun g z w => ?_⟩
  rw [complexificationEquiv_apply, complexificationEquiv_apply, ← Tmap_smul_of]

/-- **Corollary 5.12.4.** Every irreducible representation of `Sₙ` over `ℂ` can be given by
matrices with rational entries.

Concretely, for every simple `ℂ[Sₙ]`-module `M` there is a partition `λ` such that:
* `M ≅ V_λ`, the Specht module (classification, Theorem 5.12.2);
* the rational Specht module `V_λ^ℚ = ℚ[Sₙ]·c_λ` is a simple `ℚ[Sₙ]`-module — an
  irreducible representation defined over `ℚ`; and
* `V_λ` is the complexification of `V_λ^ℚ`, via a `ℂ`-linear `Sₙ`-equivariant isomorphism.

Thus `M` is realized over `ℚ`: in a `ℚ`-basis of `V_λ^ℚ` every `g ∈ Sₙ` acts by a matrix
with rational entries. The integrality of the Young symmetrizer `c_λ ∈ ℤ[Sₙ]` is what makes
`V_λ^ℚ` a genuine `ℚ`-form. -/
theorem Corollary5_12_4 (n : ℕ) (M : Type)
    [AddCommGroup M] [Module (SymGroupAlgebra n) M] [IsSimpleModule (SymGroupAlgebra n) M] :
    ∃ la : Nat.Partition n,
      Nonempty (M ≃ₗ[SymGroupAlgebra n] SpechtModule n la) ∧
      IsSimpleModule (MonoidAlgebra ℚ (Equiv.Perm (Fin n))) (SpechtModuleK ℚ n la) ∧
      ∃ e : (ℂ ⊗[ℚ] (SpechtModuleK ℚ n la)) ≃ₗ[ℂ] (SpechtModule n la),
        ∀ (g : Equiv.Perm (Fin n)) (z : ℂ) (w : SpechtModuleK ℚ n la),
          (e (z ⊗ₜ[ℚ] (MonoidAlgebra.of ℚ _ g • w))
              : MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
            = MonoidAlgebra.of ℂ _ g •
                (e (z ⊗ₜ[ℚ] w) : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) := by
  obtain ⟨la, hM⟩ := Theorem5_12_2_classification n M
  exact ⟨la, hM, SpechtModuleK_isSimpleModule n la, SpechtModule_complexification n la⟩

end

end Etingof

import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter5.Definition5_12_1

/-!
# Introduction 5.14: `U_λ = Ind_{P_λ}^{S_n} ℂ ≅ ℂ[S_n] · a_λ`

Etingof (Section 5.14) defines the permutation module `U_λ = Ind_{P_λ}^{S_n} ℂ` and remarks that
it can be alternatively described as the left ideal `ℂ[S_n] · a_λ`, where `P_λ` is the Young (row)
subgroup and `a_λ = ∑_{p ∈ P_λ} p` is the row symmetrizer.

This file proves that isomorphism as a `Representation.Equiv` between

* the induced representation `Etingof.Definition5_8_1 (RowSubgroup n la) (trivial)`, i.e. Mathlib's
  `Representation.ind (RowSubgroup n la).subtype (trivial)` on the coinvariants
  `(ℂ[S_n] ⊗ ℂ)_{P_λ}`, and
* the left ideal `ℂ[S_n] · a_λ = LinearMap.range (LinearMap.mulRight ℂ a_λ)`, with `S_n` acting by
  left multiplication (a sub-representation of the left regular representation).

## The isomorphism

The well-defined `S_n`-equivariant map is `⟦δ_g ⊗ 1⟧ ↦ g⁻¹ · a_λ` (the informal `g ⊗ 1 ↦ g · a_λ`
of the book made precise: left cosets `P_λ g` of the coinvariants must map to left ideal elements,
which forces the inverse). Well-definedness uses left-invariance `p · a_λ = a_λ` for `p ∈ P_λ`,
and the inverse `g · a_λ ↦ ⟦δ_{g⁻¹} ⊗ 1⟧` carries the normalisation `1/|P_λ|`.
-/

open Representation TensorProduct

open scoped Classical

namespace Etingof.Introduction5_14

variable (n : ℕ) (la : Nat.Partition n)

/-- The identity bridge between the group-algebra instances and the `Finsupp` instances on the
same carrier. -/
noncomputable def toFinsuppLE :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) ≃ₗ[ℂ] (Equiv.Perm (Fin n) →₀ ℂ) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma toFinsuppLE_apply (z : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    toFinsuppLE n z = z := rfl

/-- The trivial 1-dimensional representation of the row subgroup `P_λ`. -/
noncomputable abbrev trivRep : Representation ℂ (↥(RowSubgroup n la)) ℂ :=
  Representation.trivial ℂ (↥(RowSubgroup n la)) ℂ

/-- The representation of `P_λ` on `ℂ[S_n] ⊗ ℂ` whose coinvariants give the underlying module of
`Ind_{P_λ}^{S_n} ℂ`. -/
noncomputable abbrev tensRep :
    Representation ℂ (↥(RowSubgroup n la))
      (TensorProduct ℂ (Equiv.Perm (Fin n) →₀ ℂ) ℂ) :=
  Representation.tprod ((leftRegular ℂ (Equiv.Perm (Fin n))).comp (RowSubgroup n la).subtype)
    (trivRep n la)

/-- The underlying module of `Ind_{P_λ}^{S_n} ℂ`. -/
noncomputable abbrev srcMod :=
  Representation.IndV (RowSubgroup n la).subtype (trivRep n la)

/-- The left ideal `ℂ[S_n] · a_λ`, as the range of right multiplication by `a_λ`. -/
noncomputable abbrev rowIdeal : Submodule ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :=
  LinearMap.range (LinearMap.mulRight ℂ (RowSymmetrizer n la))

/-! ## Left invariance of the row symmetrizer -/

/-- Left multiplication by an element of the row subgroup fixes the row symmetrizer:
`p · a_λ = a_λ` for `p ∈ P_λ`. -/
theorem of_mul_rowSymmetrizer {q : Equiv.Perm (Fin n)} (hq : q ∈ RowSubgroup n la) :
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) q * RowSymmetrizer n la = RowSymmetrizer n la := by
  simp only [RowSymmetrizer, Finset.mul_sum]
  refine Fintype.sum_bijective (Equiv.mulLeft (⟨q, hq⟩ : ↥(RowSubgroup n la)))
    (Equiv.mulLeft _).bijective _ _ (fun g => ?_)
  change MonoidAlgebra.of ℂ _ q * MonoidAlgebra.of ℂ _ (g : Equiv.Perm (Fin n))
      = MonoidAlgebra.of ℂ _ ((⟨q, hq⟩ * g : ↥(RowSubgroup n la)) : Equiv.Perm (Fin n))
  rw [← map_mul, Subgroup.coe_mul]

/-! ## The left regular representation is left multiplication -/

theorem leftRegular_eq_mul (g : Equiv.Perm (Fin n))
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    leftRegular ℂ (Equiv.Perm (Fin n)) g x = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g * x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, mul_add, hu, hv]
  | single y r =>
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul]
      simp [leftRegular, Representation.ofMulAction_single, smul_eq_mul]

/-! ## The forward map `Ffull` -/

/-- Inversion `δ_h ↦ δ_{h⁻¹}` as a linear map into the group algebra. -/
noncomputable def invMap :
    (Equiv.Perm (Fin n) →₀ ℂ) →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  Finsupp.lsum ℂ fun h =>
    LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) h⁻¹)

@[simp] lemma invMap_single (h : Equiv.Perm (Fin n)) (r : ℂ) :
    invMap n (Finsupp.single h r) = Finsupp.single h⁻¹ r := by
  rw [invMap, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply,
    MonoidAlgebra.of_apply, Finsupp.smul_single_one]

/-- The linear map `δ_h ↦ δ_{h⁻¹} · a_λ`. -/
noncomputable def g0 :
    (Equiv.Perm (Fin n) →₀ ℂ) →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  LinearMap.mulRight ℂ (RowSymmetrizer n la) ∘ₗ invMap n

@[simp] lemma g0_single (h : Equiv.Perm (Fin n)) (r : ℂ) :
    g0 n la (Finsupp.single h r) = MonoidAlgebra.single h⁻¹ r * RowSymmetrizer n la := by
  rw [g0, LinearMap.comp_apply, invMap_single, LinearMap.mulRight_apply]

/-- Left-multiplying by a row-subgroup element before applying `g0` does nothing. -/
lemma g0_of_mul (p : ↥(RowSubgroup n la)) (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    g0 n la (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (p : Equiv.Perm (Fin n)) * x) = g0 n la x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv => rw [mul_add, map_add, map_add, hu, hv]
  | single y r =>
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul, g0_single, g0_single,
        mul_inv_rev]
      rw [show MonoidAlgebra.single (y⁻¹ * (p : Equiv.Perm (Fin n))⁻¹) r
            = MonoidAlgebra.single y⁻¹ r
              * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) ((p : Equiv.Perm (Fin n))⁻¹) by
            rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]]
      rw [mul_assoc, of_mul_rowSymmetrizer n la (inv_mem p.2)]

lemma g0_mem (y : Equiv.Perm (Fin n) →₀ ℂ) : g0 n la y ∈ rowIdeal n la := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add]; exact add_mem hu hv
  | single h r =>
      rw [g0_single]
      exact ⟨Finsupp.single h⁻¹ r, by rw [LinearMap.mulRight_apply]⟩

/-- The forward map on the tensor module `ℂ[S_n] ⊗ ℂ`, `x ⊗ c ↦ c • (g0 x)`. -/
noncomputable def f0 :
    TensorProduct ℂ (Equiv.Perm (Fin n) →₀ ℂ) ℂ →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  TensorProduct.lift ((LinearMap.lsmul ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n)))).flip ∘ₗ g0 n la)

@[simp] lemma f0_tmul (x : Equiv.Perm (Fin n) →₀ ℂ) (c : ℂ) :
    f0 n la (x ⊗ₜ[ℂ] c) = c • g0 n la x := by
  simp [f0, TensorProduct.lift.tmul]

lemma f0_mem (t : TensorProduct ℂ (Equiv.Perm (Fin n) →₀ ℂ) ℂ) : f0 n la t ∈ rowIdeal n la := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x c => rw [f0_tmul]; exact Submodule.smul_mem _ _ (g0_mem n la x)
  | add u v hu hv => rw [map_add]; exact add_mem hu hv

/-- `f0` is invariant under the `P_λ`-action, hence descends to the coinvariants. -/
lemma f0_invariant (p : ↥(RowSubgroup n la)) :
    f0 n la ∘ₗ (tensRep n la) p = f0 n la := by
  apply TensorProduct.ext'
  intro x c
  simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    MonoidHom.comp_apply, Subgroup.coe_subtype, Representation.trivial_apply, f0_tmul]
  rw [leftRegular_eq_mul, g0_of_mul]

/-- The forward map `Ind_{P_λ}^{S_n} ℂ →ₗ ℂ[S_n]`, descended from `f0`. -/
noncomputable def Ffull : srcMod n la →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  Coinvariants.lift (tensRep n la) (f0 n la) (f0_invariant n la)

@[simp] lemma Ffull_mk (t : TensorProduct ℂ (Equiv.Perm (Fin n) →₀ ℂ) ℂ) :
    Ffull n la (Coinvariants.mk (tensRep n la) t) = f0 n la t :=
  Coinvariants.lift_mk _ _ _ t

lemma IndVmk_apply (h : Equiv.Perm (Fin n)) (c : ℂ) :
    Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) h c
      = Coinvariants.mk (tensRep n la) (Finsupp.single h 1 ⊗ₜ[ℂ] c) := rfl

lemma Ffull_IndVmk (h : Equiv.Perm (Fin n)) (c : ℂ) :
    Ffull n la (Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) h c)
      = c • (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) h⁻¹ * RowSymmetrizer n la) := by
  rw [IndVmk_apply, Ffull_mk, f0_tmul, g0_single, MonoidAlgebra.of_apply]

lemma Ffull_mem (y : srcMod n la) : Ffull n la y ∈ rowIdeal n la := by
  induction y using Coinvariants.induction_on with
  | h t => rw [Ffull_mk]; exact f0_mem n la t

/-- The forward map, corestricted to the left ideal `ℂ[S_n] · a_λ`. -/
noncomputable def F : srcMod n la →ₗ[ℂ] ↥(rowIdeal n la) :=
  (Ffull n la).codRestrict _ (Ffull_mem n la)

@[simp] lemma F_coe (y : srcMod n la) :
    (F n la y : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) = Ffull n la y := rfl

/-! ## Inverse and auxiliary maps -/

/-- The (unnormalised) section `δ_x ↦ ⟦δ_{x⁻¹} ⊗ 1⟧`, used to prove surjectivity onto the ideal. -/
noncomputable def sMap : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] srcMod n la :=
  (Finsupp.linearCombination ℂ
    (fun x => Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) x⁻¹ 1))
    ∘ₗ (toFinsuppLE n).toLinearMap

@[simp] lemma sMap_single (x : Equiv.Perm (Fin n)) (r : ℂ) :
    sMap n la (Finsupp.single x r)
      = r • Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) x⁻¹ 1 := by
  rw [sMap, LinearMap.comp_apply, LinearEquiv.coe_coe, toFinsuppLE_apply,
    Finsupp.linearCombination_single]

/-- The normalised inverse `δ_x ↦ (1/|P_λ|) • ⟦δ_{x⁻¹} ⊗ 1⟧`, a left inverse to `Ffull`. -/
noncomputable def Gfull : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] srcMod n la :=
  (Finsupp.linearCombination ℂ
    (fun x => (Fintype.card (↥(RowSubgroup n la)) : ℂ)⁻¹ •
      Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) x⁻¹ 1))
    ∘ₗ (toFinsuppLE n).toLinearMap

@[simp] lemma Gfull_single (x : Equiv.Perm (Fin n)) (r : ℂ) :
    Gfull n la (Finsupp.single x r)
      = r • ((Fintype.card (↥(RowSubgroup n la)) : ℂ)⁻¹ •
          Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) x⁻¹ 1) := by
  rw [Gfull, LinearMap.comp_apply, LinearEquiv.coe_coe, toFinsuppLE_apply,
    Finsupp.linearCombination_single]

/-- Left multiplication by a row-subgroup element does not change a coinvariant generator. -/
lemma IndVmk_rowSubgroup_smul (p : ↥(RowSubgroup n la)) (h : Equiv.Perm (Fin n)) (c : ℂ) :
    Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la)
        ((p : Equiv.Perm (Fin n)) * h) c
      = Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) h c := by
  have hkey : (tensRep n la) p (Finsupp.single h 1 ⊗ₜ[ℂ] c)
      = Finsupp.single ((p : Equiv.Perm (Fin n)) * h) 1 ⊗ₜ[ℂ] c := by
    simp only [Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply,
      Subgroup.coe_subtype, Representation.trivial_apply]
    rw [leftRegular_eq_mul, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul]
  rw [IndVmk_apply, IndVmk_apply, ← hkey, Coinvariants.mk_self_apply]

/-! ## `Ffull` is a bijection onto the ideal -/

/-- `Ffull (sMap z) = z · a_λ`, so `Ffull` hits every element of the left ideal. -/
lemma Ffull_sMap (z : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    Ffull n la (sMap n la z) = z * RowSymmetrizer n la := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, add_mul, hu, hv]
  | single x r =>
      rw [sMap_single, map_smul, Ffull_IndVmk, one_smul, inv_inv, MonoidAlgebra.of_apply,
        ← smul_mul_assoc, Finsupp.smul_single_one]

/-- `Gfull ∘ Ffull = id`, so `Ffull` is injective. -/
lemma Gfull_comp_Ffull : (Gfull n la) ∘ₗ (Ffull n la) = LinearMap.id := by
  haveI : Nonempty (↥(RowSubgroup n la)) := ⟨1⟩
  have hcard : (Fintype.card (↥(RowSubgroup n la)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply Representation.IndV.hom_ext
  intro h
  apply LinearMap.ext_ring
  change Gfull n la (Ffull n la
      (Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) h 1))
    = Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) h 1
  rw [Ffull_IndVmk, one_smul,
    show MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) h⁻¹ * RowSymmetrizer n la
        = ∑ g : ↥(RowSubgroup n la), Finsupp.single (h⁻¹ * (g : Equiv.Perm (Fin n))) 1 by
      simp only [RowSymmetrizer, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [← map_mul, MonoidAlgebra.of_apply]]
  rw [map_sum, Finset.sum_congr rfl (fun g (_ : g ∈ Finset.univ) => by
    rw [Gfull_single, one_smul, mul_inv_rev, inv_inv, ← Subgroup.coe_inv,
      IndVmk_rowSubgroup_smul])]
  rw [Finset.sum_const, Finset.card_univ, smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

lemma Ffull_injective : Function.Injective (Ffull n la) := by
  have hL : Function.LeftInverse (Gfull n la) (Ffull n la) := fun x => by
    have := LinearMap.congr_fun (Gfull_comp_Ffull n la) x
    simpa using this
  exact hL.injective

lemma F_injective : Function.Injective (F n la) := by
  intro a b hab
  apply Ffull_injective n la
  have : (F n la a : MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
      = (F n la b : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) := congrArg _ hab
  simpa only [F_coe] using this

lemma F_surjective : Function.Surjective (F n la) := by
  intro y
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp y.2
  refine ⟨sMap n la z, ?_⟩
  apply Subtype.ext
  rw [F_coe, Ffull_sMap]
  simpa [LinearMap.mulRight_apply] using hz

/-! ## The target representation and the isomorphism -/

/-- The left-multiplication representation of `S_n` on its group algebra. -/
noncomputable def leftMulRep :
    Representation ℂ (Equiv.Perm (Fin n)) (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) where
  toFun g := LinearMap.mulLeft ℂ (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul, mul_assoc]

@[simp] lemma leftMulRep_apply (g : Equiv.Perm (Fin n))
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    leftMulRep n g x = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g * x := rfl

/-- The left ideal `ℂ[S_n] · a_λ` is invariant under left multiplication. -/
lemma le_comap (g : Equiv.Perm (Fin n)) :
    rowIdeal n la ≤ (rowIdeal n la).comap (leftMulRep n g) := by
  rintro _ ⟨z, rfl⟩
  refine Submodule.mem_comap.2 ⟨MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g * z, ?_⟩
  rw [leftMulRep_apply, LinearMap.mulRight_apply, LinearMap.mulRight_apply, mul_assoc]

/-- The representation of `S_n` on the left ideal `ℂ[S_n] · a_λ` by left multiplication. -/
noncomputable def targetRep : Representation ℂ (Equiv.Perm (Fin n)) ↥(rowIdeal n la) :=
  Representation.subrepresentation (leftMulRep n) (rowIdeal n la) (le_comap n la)

/-- `Ffull` intertwines the induced action with left multiplication. -/
lemma equivar_full (g : Equiv.Perm (Fin n)) :
    (Ffull n la) ∘ₗ (Etingof.Definition5_8_1 (RowSubgroup n la) (trivRep n la) g)
      = (leftMulRep n g) ∘ₗ (Ffull n la) := by
  apply Representation.IndV.hom_ext
  intro h
  apply LinearMap.ext_ring
  change Ffull n la (Representation.ind (RowSubgroup n la).subtype (trivRep n la) g
      (Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) h 1))
    = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g
      * Ffull n la (Representation.IndV.mk (RowSubgroup n la).subtype (trivRep n la) h 1)
  rw [Representation.ind_mk, Ffull_IndVmk, Ffull_IndVmk, one_smul, one_smul, mul_inv_rev, inv_inv,
    map_mul, mul_assoc]

lemma equivar_full_apply (g : Equiv.Perm (Fin n)) (y : srcMod n la) :
    Ffull n la (Etingof.Definition5_8_1 (RowSubgroup n la) (trivRep n la) g y)
      = leftMulRep n g (Ffull n la y) :=
  LinearMap.congr_fun (equivar_full n la g) y

/-- The `ℂ`-linear isomorphism `Ind_{P_λ}^{S_n} ℂ ≃ₗ ℂ[S_n] · a_λ`. -/
noncomputable def linEquiv : srcMod n la ≃ₗ[ℂ] ↥(rowIdeal n la) :=
  LinearEquiv.ofBijective (F n la) ⟨F_injective n la, F_surjective n la⟩

lemma linEquiv_intertwine (g : Equiv.Perm (Fin n)) :
    (linEquiv n la : srcMod n la →ₗ[ℂ] ↥(rowIdeal n la))
        ∘ₗ (Etingof.Definition5_8_1 (RowSubgroup n la) (trivRep n la) g)
      = (targetRep n la g) ∘ₗ (linEquiv n la) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, linEquiv, LinearEquiv.ofBijective_apply]
  apply Subtype.ext
  change Ffull n la (Etingof.Definition5_8_1 (RowSubgroup n la) (trivRep n la) g x)
      = leftMulRep n g (Ffull n la x)
  exact equivar_full_apply n la g x

/-- **Etingof, Section 5.14.** The induced representation `U_λ = Ind_{P_λ}^{S_n} ℂ` is isomorphic,
as a representation of `S_n`, to the left ideal `ℂ[S_n] · a_λ` generated by the row symmetrizer. -/
noncomputable def equiv :
    (Etingof.Definition5_8_1 (RowSubgroup n la)
        (Representation.trivial ℂ (↥(RowSubgroup n la)) ℂ)).Equiv (targetRep n la) :=
  Representation.Equiv.mk (linEquiv n la) (linEquiv_intertwine n la)

end Etingof.Introduction5_14

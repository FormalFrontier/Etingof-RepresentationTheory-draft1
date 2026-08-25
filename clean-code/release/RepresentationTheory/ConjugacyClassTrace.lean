/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib

/-!
# Conjugacy-class trace maps
-/

open MonoidAlgebra

namespace RepresentationTheory.ConjugacyClassTrace

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq G]

variable (k G) in
/-- An auxiliary scalar submodule of the group monoid algebra. -/
noncomputable def auxiliaryRelationSubmodule : Submodule k (MonoidAlgebra k G) :=
  Submodule.span k (Set.range (fun p : MonoidAlgebra k G × MonoidAlgebra k G =>
    p.1 * p.2 - p.2 * p.1))

variable (k G) in
/-- An auxiliary type associated with a field and a group. -/
noncomputable abbrev AuxiliaryClassQuotient : Type _ :=
  MonoidAlgebra k G ⧸ auxiliaryRelationSubmodule k G

variable (k G) in
/-- A linear map from the group monoid algebra to scalar-valued functions on conjugacy classes. -/
noncomputable def monoidAlgebraToClassFunctions :
    MonoidAlgebra k G →ₗ[k] (ConjClasses G → k) where
  toFun a := fun C' => ∑ g : G, if ConjClasses.mk g = C' then a.coeff g else 0
  map_add' a b := by
    funext C'
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by
      rw [show (a + b).coeff g = a.coeff g + b.coeff g from rfl]; split <;> simp
  map_smul' r a := by
    funext C'
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by
      rw [show (r • a).coeff g = r • a.coeff g from rfl, smul_eq_mul]; split <;> simp

/-- A singleton monoid-algebra term maps to the function supported on its conjugacy class with the given coefficient. -/
lemma monoidAlgebraToClassFunctions_single (g : G) (c : k) :
    monoidAlgebraToClassFunctions k G (single g c) =
      fun C' => if ConjClasses.mk g = C' then c else 0 := by
  funext C'
  simp only [monoidAlgebraToClassFunctions, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single g]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos rfl]
  · intro b _ hbg
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hbg), ite_self]
  · intro hg; exact absurd (Finset.mem_univ g) hg

/-- The class-function image of a product is unchanged when its two factors are reversed. -/
lemma monoidAlgebraToClassFunctions_mul_comm (x y : MonoidAlgebra k G) :
    monoidAlgebraToClassFunctions k G (x * y) = monoidAlgebraToClassFunctions k G (y * x) := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
    induction y using MonoidAlgebra.induction_on with
    | hM h =>
      rw [of_apply, of_apply, single_mul_single, single_mul_single,
        monoidAlgebraToClassFunctions_single, monoidAlgebraToClassFunctions_single,
        show ConjClasses.mk (g * h) = ConjClasses.mk (h * g) from
          ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by group⟩)]
    | hadd y₁ y₂ h₁ h₂ => rw [mul_add, add_mul, map_add, map_add, h₁, h₂]
    | hsmul r y h => rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, map_smul, map_smul, h]
  | hadd x₁ x₂ h₁ h₂ => rw [add_mul, mul_add, map_add, map_add, h₁, h₂]
  | hsmul r x h => rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smul, map_smul, h]

/-- The auxiliary relation submodule lies in the kernel of the map to conjugacy-class functions. -/
lemma auxiliaryRelationSubmodule_le_ker_monoidAlgebraToClassFunctions :
    auxiliaryRelationSubmodule k G ≤ LinearMap.ker (monoidAlgebraToClassFunctions k G) := by
  rw [auxiliaryRelationSubmodule, Submodule.span_le]
  rintro _ ⟨⟨x, y⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub,
    monoidAlgebraToClassFunctions_mul_comm x y, sub_self]

/-- The linear map from the monoid algebra to functions on conjugacy classes is surjective. -/
lemma monoidAlgebraToClassFunctions_surjective :
    Function.Surjective (monoidAlgebraToClassFunctions k G) := by
  have hmk : ∀ C' : ConjClasses G, ConjClasses.mk (Quotient.out C') = C' := fun C' => by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  intro f
  refine ⟨∑ C' : ConjClasses G, f C' • single (Quotient.out C') 1, ?_⟩
  funext D
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, monoidAlgebraToClassFunctions_single, hmk, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ D f]
  simp

variable (k G) in
/-- A linear map from the auxiliary class quotient to scalar-valued functions on conjugacy classes. -/
noncomputable def auxiliaryToClassFunctions :
    AuxiliaryClassQuotient k G →ₗ[k] (ConjClasses G → k) :=
  Submodule.liftQ (auxiliaryRelationSubmodule k G) (monoidAlgebraToClassFunctions k G)
    auxiliaryRelationSubmodule_le_ker_monoidAlgebraToClassFunctions

/-- The auxiliary linear map to functions on conjugacy classes is surjective. -/
lemma auxiliaryToClassFunctions_surjective : Function.Surjective (auxiliaryToClassFunctions k G) := by
  intro f
  obtain ⟨a, ha⟩ := monoidAlgebraToClassFunctions_surjective f
  exact ⟨Submodule.Quotient.mk a, by rw [auxiliaryToClassFunctions, Submodule.liftQ_apply, ha]⟩

variable (k G) in
/-- An auxiliary map from conjugacy classes into the auxiliary class quotient. -/
noncomputable def conjugacyClassToAuxiliary : ConjClasses G → AuxiliaryClassQuotient k G :=
  fun C' => Submodule.mkQ (auxiliaryRelationSubmodule k G) (single (Quotient.out C') 1)

omit [Fintype G] [DecidableEq G] in
/-- The difference of unit singleton terms at conjugate group elements belongs to the auxiliary relation submodule. -/
lemma single_sub_single_mem_auxiliaryRelationSubmodule_of_isConj {a b : G} (h : IsConj a b) :
    single a (1 : k) - single b 1 ∈ auxiliaryRelationSubmodule k G := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hrw : single (c⁻¹) (1 : k) * single (c * a) 1 - single (c * a) 1 * single (c⁻¹) 1
      = single a 1 - single b 1 := by
    rw [single_mul_single, single_mul_single, one_mul,
      show c⁻¹ * (c * a) = a by group, show c * a * c⁻¹ = b from hc]
  rw [← hrw]
  exact Submodule.subset_span ⟨(single (c⁻¹) 1, single (c * a) 1), rfl⟩

omit [Fintype G] [DecidableEq G] in
/-- The quotient image of a unit singleton equals the auxiliary element indexed by its conjugacy class. -/
lemma mkQ_single_one_eq_conjugacyClassToAuxiliary (g : G) :
    Submodule.mkQ (auxiliaryRelationSubmodule k G) (single g 1) =
      conjugacyClassToAuxiliary k G (ConjClasses.mk g) := by
  have hmk : ConjClasses.mk (Quotient.out (ConjClasses.mk g)) = ConjClasses.mk g := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  rw [conjugacyClassToAuxiliary, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact single_sub_single_mem_auxiliaryRelationSubmodule_of_isConj
    (ConjClasses.mk_eq_mk_iff_isConj.mp hmk.symm)

omit [Fintype G] [DecidableEq G] in
/-- The unit singleton terms indexed by the group span the entire monoid algebra. -/
lemma span_range_single_one :
    Submodule.span k (Set.range (fun g : G => (single g 1 : MonoidAlgebra k G))) = ⊤ := by
  rw [eq_top_iff]
  rintro a -
  induction a using MonoidAlgebra.induction_on with
  | hM g => exact Submodule.subset_span ⟨g, rfl⟩
  | hadd x y hx hy => exact Submodule.add_mem _ hx hy
  | hsmul r x hx => exact Submodule.smul_mem _ r hx

omit [Fintype G] [DecidableEq G] in
/-- The range of the auxiliary conjugacy-class map spans the whole auxiliary quotient. -/
lemma span_range_conjugacyClassToAuxiliary :
    Submodule.span k (Set.range (conjugacyClassToAuxiliary k G)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← Submodule.range_mkQ (auxiliaryRelationSubmodule k G), LinearMap.range_eq_map,
    ← span_range_single_one, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mkQ_single_one_eq_conjugacyClassToAuxiliary g]
  exact Submodule.subset_span ⟨ConjClasses.mk g, rfl⟩

/-- The monoid algebra of a finite type is finite-dimensional over the field. -/
noncomputable instance finite_monoidAlgebra : Module.Finite k (MonoidAlgebra k G) :=
  Module.Finite.of_basis (MonoidAlgebra.basis G k)

/-- The auxiliary class quotient is finite-dimensional over the field for a finite group. -/
noncomputable instance finite_auxiliaryClassQuotient : Module.Finite k (AuxiliaryClassQuotient k G) :=
  Module.Finite.of_surjective (Submodule.mkQ (auxiliaryRelationSubmodule k G))
    (Submodule.mkQ_surjective _)

/-- The auxiliary class quotient has dimension equal to the number of conjugacy classes. -/
theorem finrank_auxiliaryClassQuotient :
    Module.finrank k (AuxiliaryClassQuotient k G) = Nat.card (ConjClasses G) := by
  have hle1 : Fintype.card (ConjClasses G) ≤ Module.finrank k (AuxiliaryClassQuotient k G) := by
    have h := LinearMap.finrank_le_finrank_of_surjective
      (auxiliaryToClassFunctions_surjective (k := k) (G := G))
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have hle2 : Module.finrank k (AuxiliaryClassQuotient k G) ≤ Fintype.card (ConjClasses G) := by
    have hv := finrank_range_le_card (R := k) (conjugacyClassToAuxiliary k G)
    have heq : (Set.range (conjugacyClassToAuxiliary k G)).finrank k =
        Module.finrank k (AuxiliaryClassQuotient k G) := by
      change Module.finrank k (Submodule.span k (Set.range (conjugacyClassToAuxiliary k G))) = _
      rw [span_range_conjugacyClassToAuxiliary, finrank_top]
    rwa [heq] at hv
  rw [le_antisymm hle2 hle1, Nat.card_eq_fintype_card]

section TraceForm

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M] [Module.Finite k M]

omit [Fintype G] [DecidableEq G]

variable (k) in
/-- An algebra homomorphism from the group monoid algebra to the endomorphisms of a compatible module. -/
noncomputable def monoidAlgebraActionHom : MonoidAlgebra k G →ₐ[k] Module.End k M :=
  Algebra.lsmul k k M

omit [Module.Finite k M] in
/-- Evaluating the monoid-algebra action homomorphism agrees with scalar multiplication on the module. -/
@[simp] lemma monoidAlgebraActionHom_apply (x : MonoidAlgebra k G) (m : M) :
    monoidAlgebraActionHom k M x m = x • m := rfl

variable (k) in
/-- A linear functional from the group monoid algebra to the base field for a compatible module. -/
noncomputable def moduleTrace : MonoidAlgebra k G →ₗ[k] k :=
  (LinearMap.trace k M).comp (monoidAlgebraActionHom k M).toLinearMap

omit [Module.Finite k M] in
/-- The module trace functional evaluates an algebra element as the trace of its action endomorphism. -/
lemma moduleTrace_eq_trace_action (x : MonoidAlgebra k G) :
    moduleTrace k M x = LinearMap.trace k M (monoidAlgebraActionHom k M x) := rfl

omit [Module.Finite k M] in
/-- The module trace of a product is unchanged when the factors are reversed. -/
lemma moduleTrace_mul_comm (x y : MonoidAlgebra k G) :
    moduleTrace k M (x * y) = moduleTrace k M (y * x) := by
  simp only [moduleTrace_eq_trace_action, map_mul]
  exact LinearMap.trace_mul_comm k _ _

omit [Module.Finite k M] in
/-- The auxiliary relation submodule lies in the kernel of the module trace map. -/
lemma auxiliaryRelationSubmodule_le_ker_moduleTrace :
    auxiliaryRelationSubmodule k G ≤ LinearMap.ker (moduleTrace k M) := by
  rw [auxiliaryRelationSubmodule, Submodule.span_le]
  rintro _ ⟨⟨x, y⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, moduleTrace_mul_comm M x y, sub_self]

variable (k) in
/-- A linear functional from the auxiliary class quotient to the base field for a compatible module. -/
noncomputable def auxiliaryModuleTrace : AuxiliaryClassQuotient k G →ₗ[k] k :=
  Submodule.liftQ (auxiliaryRelationSubmodule k G) (moduleTrace k M)
    (auxiliaryRelationSubmodule_le_ker_moduleTrace M)

omit [Module.Finite k M] in
/-- The auxiliary module trace of a quotient image agrees with the module trace of its representative. -/
@[simp] lemma auxiliaryModuleTrace_mkQ (x : MonoidAlgebra k G) :
    auxiliaryModuleTrace k M (Submodule.mkQ (auxiliaryRelationSubmodule k G) x) =
      moduleTrace k M x :=
  Submodule.liftQ_apply _ _ _

omit [Module.Finite k M] in
/-- The auxiliary module trace of a quotient unit singleton equals the trace of its action. -/
lemma auxiliaryModuleTrace_mkQ_single_one (g : G) :
    auxiliaryModuleTrace k M
        (Submodule.mkQ (auxiliaryRelationSubmodule k G) (single g 1)) =
      LinearMap.trace k M (monoidAlgebraActionHom k M (single g (1 : k))) := by
  rw [auxiliaryModuleTrace_mkQ, moduleTrace_eq_trace_action]

omit [Module.Finite k M] in
/-- The auxiliary module trace at a conjugacy class is the trace of the corresponding unit singleton action. -/
lemma auxiliaryModuleTrace_conjugacyClass (g : G) :
    auxiliaryModuleTrace k M (conjugacyClassToAuxiliary k G (ConjClasses.mk g)) =
      LinearMap.trace k M (monoidAlgebraActionHom k M (single g (1 : k))) := by
  rw [← mkQ_single_one_eq_conjugacyClassToAuxiliary, auxiliaryModuleTrace_mkQ_single_one]

end TraceForm

end RepresentationTheory.ConjugacyClassTrace

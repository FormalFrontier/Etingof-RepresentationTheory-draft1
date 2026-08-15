/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.DualNumber
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.LinearAlgebra.ModuleDecompositions
import RepresentationTheory.Module.SimpleSubmodule

/-! # Actions of algebra centers -/

namespace RepresentationTheory.Algebra.CenterAction

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The endomorphism of a module induced by an element of the algebra center. -/
def centerActionEnd (z : Subalgebra.center k A) : Module.End A V where
  toFun v := (z : A) • v
  map_add' := smul_add _
  map_smul' a v := by
    change (z : A) • (a • v) = a • ((z : A) • v)
    rw [smul_smul, smul_smul, Subalgebra.mem_center_iff.mp z.2 a]

omit [Module k V] [IsScalarTower k A V] in
/-- Applying the central-action endomorphism agrees with the given module action. -/
@[simp]
theorem centerActionEnd_apply (z : Subalgebra.center k A) (v : V) :
    centerActionEnd z v = (z : A) • v := rfl

/-- The algebra homomorphism sending each central element to its action on the module. -/
def centerActionAlgHom : Subalgebra.center k A →ₐ[k] Module.End A V where
  toFun := centerActionEnd
  map_one' := by ext v; simp
  map_mul' z w := by
    ext v
    simp only [centerActionEnd_apply, Module.End.mul_apply, Subalgebra.coe_mul, mul_smul]
  map_zero' := by ext v; simp
  map_add' z w := by ext v; simp [add_smul]
  commutes' r := by
    ext v
    simp only [centerActionEnd_apply, Module.algebraMap_end_apply]
    exact algebraMap_smul A r v

variable [IsAlgClosed k] [IsSimpleModule A V] [FiniteDimensional k V]

/-- An algebra equivalence from the base field to the endomorphisms of a finite simple module. -/
noncomputable def endomorphismAlgebraEquiv : k ≃ₐ[k] Module.End A V :=
  AlgEquiv.ofBijective (Algebra.ofId k (Module.End A V))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)

/-- The endomorphism algebra equivalence sends a scalar to its standard scalar action. -/
@[simp]
theorem endomorphismAlgebraEquiv_apply (c : k) :
    endomorphismAlgebraEquiv (A := A) (V := V) c = algebraMap k (Module.End A V) c := rfl

/-- The scalar-valued algebra homomorphism describing central actions on a finite simple module. -/
noncomputable def centerCharacter : Subalgebra.center k A →ₐ[k] k :=
  (endomorphismAlgebraEquiv (k := k) (A := A) (V := V)).symm.toAlgHom.comp centerActionAlgHom

/-- A central element acts by multiplication by its associated scalar on every vector. -/
theorem centerAction_eq_character_smul (z : Subalgebra.center k A) (v : V) :
    (z : A) • v = centerCharacter (k := k) (V := V) z • v := by
  have h : endomorphismAlgebraEquiv (A := A) (V := V)
      (centerCharacter (k := k) (V := V) z) = centerActionAlgHom (k := k) z :=
    endomorphismAlgebraEquiv.apply_symm_apply _
  rw [endomorphismAlgebraEquiv_apply] at h
  have hv := congrArg (fun f : Module.End A V => f v) h
  simp only [Module.algebraMap_end_apply] at hv
  exact hv.symm

/-- Every central element acts as multiplication by some scalar on the indicated module. -/
theorem centerElement_smul_eq_scalar_smul (z : Subalgebra.center k A) :
    ∃ c : k, ∀ v : V, (z : A) • v = c • v :=
  ⟨centerCharacter (k := k) (V := V) z, fun v => centerAction_eq_character_smul z v⟩

section Indecomposable

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
variable [FiniteDimensional k V]

/-- A central action with a nonzero scalar eigenvector differs from that scalar action by a
nilpotent endomorphism, under the displayed hypothesis. -/
theorem centerAction_sub_scalar_isNilpotent
    (hV : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate
      A V)
    (z : Subalgebra.center k A) {χ : k} {v₀ : V} (hv₀ : v₀ ≠ 0)
    (heig : (z : A) • v₀ = χ • v₀) :
    IsNilpotent (centerActionEnd (V := V) z - χ • (1 : Module.End A V)) := by
  haveI : IsArtinian A V := isArtinian_of_tower k inferInstance
  haveI : IsNoetherian A V := isNoetherian_of_tower k inferInstance
  set g : Module.End A V := centerActionEnd (V := V) z - χ • (1 : Module.End A V) with hg
  have hgv₀ : g v₀ = 0 := by
    simp only [hg, LinearMap.sub_apply, centerActionEnd_apply, LinearMap.smul_apply,
      Module.End.one_apply, heig, sub_self]
  have hkerne : LinearMap.ker g ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨v₀, hgv₀, hv₀⟩
  have hcompl : IsCompl (⨆ n, LinearMap.ker (g ^ n)) (⨅ n, LinearMap.range (g ^ n)) :=
    LinearMap.isCompl_iSup_ker_pow_iInf_range_pow g
  have hker_le : LinearMap.ker g ≤ ⨆ n, LinearMap.ker (g ^ n) := by
    conv_lhs => rw [← pow_one g]
    exact le_iSup (fun n => LinearMap.ker (g ^ n)) 1
  have hsupne : (⨆ n, LinearMap.ker (g ^ n)) ≠ ⊥ := fun hbot =>
    hkerne (le_bot_iff.mp (hbot ▸ hker_le))
  rcases hV.2 _ _ hcompl with hP | hQ
  · exact absurd hP hsupne
  · have htop : (⨆ n, LinearMap.ker (g ^ n)) = ⊤ := by
      rw [hQ] at hcompl
      exact eq_top_of_isCompl_bot hcompl
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp g.eventually_iSup_ker_pow_eq
    have hkerN : LinearMap.ker (g ^ N) = ⊤ := by rw [← hN N le_rfl]; exact htop
    exact ⟨N, LinearMap.ker_eq_top.mp hkerN⟩

omit [FiniteDimensional k V] in
/-- A nilpotent scalar endomorphism of a nontrivial module has zero scalar. -/
theorem scalarEndomorphism_isNilpotent_imp [Nontrivial V] {c : k}
    (h : IsNilpotent (c • (1 : Module.End A V))) : c = 0 := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hcmv : c ^ m • v = 0 := by
    have happ := LinearMap.congr_fun hm v
    rw [← Algebra.algebraMap_eq_smul_one, ← map_pow, Module.algebraMap_end_apply,
      LinearMap.zero_apply] at happ
    exact happ
  have hcm : c ^ m = 0 := (smul_eq_zero.mp hcmv).resolve_right hv
  have hm0 : m ≠ 0 := by rintro rfl; rw [pow_zero] at hcm; exact one_ne_zero hcm
  exact (pow_eq_zero_iff hm0).mp hcm

omit [FiniteDimensional k V] in
/-- Two scalars producing nilpotent deviations from the same central action are equal. -/
theorem centerCharacter_value_unique
    (hV : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate
      A V)
    (z : Subalgebra.center k A) {χ χ' : k}
    (h : IsNilpotent (centerActionEnd (V := V) z - χ • (1 : Module.End A V)))
    (h' : IsNilpotent (centerActionEnd (V := V) z - χ' • (1 : Module.End A V))) : χ = χ' := by
  haveI : Nontrivial V := hV.1
  set a : Module.End A V := centerActionEnd (V := V) z with ha
  have hcomm : Commute (a - χ • (1 : Module.End A V)) (a - χ' • (1 : Module.End A V)) := by
    have hrw : a - χ' • (1 : Module.End A V) =
        (a - χ • (1 : Module.End A V)) + (χ - χ') • (1 : Module.End A V) := by
      rw [sub_smul]; abel
    rw [hrw]
    refine (Commute.refl _).add_right ?_
    rw [show ((χ - χ') • (1 : Module.End A V)) = algebraMap k (Module.End A V) (χ - χ') from
      (Algebra.algebraMap_eq_smul_one _).symm]
    exact Algebra.commute_algebraMap_right _ _
  have hdiff : (a - χ • (1 : Module.End A V)) - (a - χ' • (1 : Module.End A V)) =
      (χ' - χ) • (1 : Module.End A V) := by rw [sub_smul]; abel
  have hnil : IsNilpotent ((χ' - χ) • (1 : Module.End A V)) := by
    rw [← hdiff]; exact hcomm.isNilpotent_sub h h'
  have : χ' - χ = 0 := scalarEndomorphism_isNilpotent_imp hnil
  exact (sub_eq_zero.mp this).symm

variable [IsAlgClosed k]

/-- Under the displayed condition, there is a central character whose scalar actions differ from
central actions by nilpotents. -/
theorem exists_centerCharacter_sub_action_isNilpotent
    (hV : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate
      A V) :
    ∃ χ_V : Subalgebra.center k A →ₐ[k] k, ∀ z : Subalgebra.center k A,
      IsNilpotent (centerActionEnd (V := V) z - (χ_V z) • (1 : Module.End A V)) := by
  haveI : Nontrivial V := hV.1
  obtain ⟨S, hS⟩ := RepresentationTheory.Module.SimpleSubmodule.exists_isSimpleModule_subtype
    (k := k) (A := A) (V := V)
  haveI : IsSimpleModule A S := hS
  haveI : Nontrivial S := IsSimpleModule.nontrivial A S
  haveI : FiniteDimensional k S := (inferInstance : FiniteDimensional k (S.restrictScalars k))
  refine ⟨centerCharacter (k := k) (V := S), fun z => ?_⟩
  set χ : k := centerCharacter (k := k) (V := S) z with hχ
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  have hv₀ : (s₀ : V) ≠ 0 := by simpa using hs₀
  have heig : (z : A) • (s₀ : V) = χ • (s₀ : V) := by
    have := centerAction_eq_character_smul (k := k) (V := S) z s₀
    have h2 := congrArg (fun s : S => (s : V)) this
    simpa [hχ] using h2
  exact centerAction_sub_scalar_isNilpotent hV z hv₀ heig

/-- Under the given condition, a simple submodule admits compatible scalar descriptions of all
central actions. -/
theorem exists_simpleSubmodule_centerCharacter
    (hV : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate
      A V) :
    ∃ S : Submodule A V, IsSimpleModule A S ∧
      ∃ χ_V : Subalgebra.center k A →ₐ[k] k,
        (∀ z : Subalgebra.center k A,
          IsNilpotent (centerActionEnd (V := V) z - (χ_V z) • (1 : Module.End A V))) ∧
        ∀ (z : Subalgebra.center k A) (s : S),
          (z : A) • (s : V) = (χ_V z) • (s : V) := by
  haveI : Nontrivial V := hV.1
  obtain ⟨S, hS⟩ := RepresentationTheory.Module.SimpleSubmodule.exists_isSimpleModule_subtype
    (k := k) (A := A) (V := V)
  haveI : IsSimpleModule A S := hS
  haveI : Nontrivial S := IsSimpleModule.nontrivial A S
  haveI : FiniteDimensional k S :=
    (inferInstance : FiniteDimensional k (S.restrictScalars k))
  let χ_V := centerCharacter (k := k) (A := A) (V := S)
  refine ⟨S, hS, χ_V, ?_, ?_⟩
  · intro z
    obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
    have hv₀ : (s₀ : V) ≠ 0 := by simpa using hs₀
    have heig : (z : A) • (s₀ : V) = (χ_V z) • (s₀ : V) := by
      have h := centerAction_eq_character_smul (k := k) (A := A) (V := S) z s₀
      exact congrArg (fun s : S => (s : V)) h
    exact centerAction_sub_scalar_isNilpotent hV z hv₀ heig
  · intro z s
    have h := centerAction_eq_character_smul (k := k) (A := A) (V := S) z s
    exact congrArg (fun t : S => (t : V)) h

end Indecomposable

section DualNumberCounterexample

open DualNumber TrivSqZeroExt

variable {k : Type*} [Field k]

/-- The distinguished nilpotent element of the dual numbers, regarded as a central element. -/
def dualNumberEpsilonInCenter : Subalgebra.center k (DualNumber k) :=
  ⟨ε, Subalgebra.mem_center_iff.mpr fun b => commute_eps_right b⟩

/-- The underlying value of the selected central dual-number element is epsilon. -/
@[simp]
theorem dualNumberEpsilonInCenter_val :
    (dualNumberEpsilonInCenter (k := k) : DualNumber k) = ε := rfl

/-- Multiplication by epsilon on the dual numbers is not scalar multiplication by any field
element. -/
theorem dualNumberEpsilon_not_scalarAction :
    ¬ ∃ c : k, ∀ v : DualNumber k, (ε : DualNumber k) * v = c • v := by
  rintro ⟨c, hc⟩
  have h1 := hc 1
  rw [mul_one, Algebra.smul_def, mul_one] at h1
  have h2 := congrArg TrivSqZeroExt.snd h1
  rw [snd_eps, algebraMap_eq_inl, snd_inl] at h2
  exact one_ne_zero h2

end DualNumberCounterexample

end RepresentationTheory.Algebra.CenterAction

attribute [source_ref "Chapter2/Problem2.3.16" (role := primary)]
  RepresentationTheory.Algebra.CenterAction.centerAction_eq_character_smul
  RepresentationTheory.Algebra.CenterAction.centerCharacter
  RepresentationTheory.Algebra.CenterAction.centerElement_smul_eq_scalar_smul

attribute [source_ref "Chapter2/Problem2.3.16" (role := supporting)]
  RepresentationTheory.Algebra.CenterAction.centerAction_sub_scalar_isNilpotent
  RepresentationTheory.Algebra.CenterAction.centerCharacter_value_unique
  RepresentationTheory.Algebra.CenterAction.dualNumberEpsilon_not_scalarAction
  RepresentationTheory.Algebra.CenterAction.exists_simpleSubmodule_centerCharacter

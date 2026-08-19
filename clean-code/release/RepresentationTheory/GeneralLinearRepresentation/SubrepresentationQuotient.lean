/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearRepresentation.WeightSpaceMorphisms
import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

noncomputable section

set_option linter.dupNamespace false
set_option linter.style.longLine false

open MvPolynomial
open scoped MonoidAlgebra

namespace RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

/-- An auxiliary result about the quotient action associated with an invariant submodule. -/
theorem auxiliaryQuotient {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N ρ)
    (K : Submodule k Y) (hK : ∀ g, K ≤ K.comap (ρ g)) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N
      (fun g => Submodule.mapQ K K (ρ g) (hK g)) := by
  classical
  haveI : Module.Finite k (Y ⧸ K) := Module.Finite.of_surjective K.mkQ K.mkQ_surjective
  obtain ⟨M, B, P, hP⟩ := h
  let b' : Module.Basis (Fin (Module.finrank k (Y ⧸ K))) k (Y ⧸ K) := Module.finBasis k (Y ⧸ K)
  obtain ⟨K', hK'⟩ := K.exists_isCompl
  let e := Submodule.quotientEquivOfIsCompl K K' hK'
  let s : (Y ⧸ K) →ₗ[k] Y := K'.subtype ∘ₗ (e : (Y ⧸ K) →ₗ[k] K')
  have hsec : ∀ x : Y ⧸ K, K.mkQ (s x) = x := by
    intro x
    rw [Submodule.mkQ_apply]
    exact Submodule.mk_quotientEquivOfIsCompl_apply hK' x
  refine ⟨Module.finrank k (Y ⧸ K), b',
    fun a c => ∑ d, ∑ e,
      MvPolynomial.C (B.repr (s (b' c)) d) * P e d
        * MvPolynomial.C (b'.repr (K.mkQ (B e)) a), fun g a c => ?_⟩
  let φ : Y →ₗ[k] k := (Finsupp.lapply a).comp (b'.repr.toLinearMap.comp K.mkQ)
  have hφ_apply : ∀ y, φ y = b'.repr (K.mkQ y) a := fun _ => rfl
  have h1 : Submodule.mapQ K K (ρ g) (hK g) (b' c) = K.mkQ (ρ g (s (b' c))) := by
    conv_lhs => rw [← hsec (b' c)]
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.mkQ_apply]
  have hlhs : b'.repr (Submodule.mapQ K K (ρ g) (hK g) (b' c)) a
      = ∑ d, ∑ e, B.repr (s (b' c)) d
          * (RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (P e d) * b'.repr (K.mkQ (B e)) a) := by
    rw [show b'.repr (Submodule.mapQ K K (ρ g) (hK g) (b' c)) a = φ (ρ g (s (b' c))) from by
      rw [hφ_apply, h1]]
    rw [show ρ g (s (b' c))
        = ∑ d, B.repr (s (b' c)) d • ρ g (B d) from by
      conv_lhs => rw [show s (b' c) = ∑ d, B.repr (s (b' c)) d • B d from
        (B.sum_repr (s (b' c))).symm]
      rw [map_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [map_smul]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, smul_eq_mul]
    have hd : φ (ρ g (B d))
        = ∑ e, RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (P e d) * b'.repr (K.mkQ (B e)) a := by
      conv_lhs => rw [show ρ g (B d) = ∑ e, B.repr (ρ g (B d)) e • B e from
        (B.sum_repr (ρ g (B d))).symm]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, smul_eq_mul, hP g e d, hφ_apply]
    rw [hd, Finset.mul_sum]
  rw [hlhs, RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_mul,
    RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_mul,
    RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_C,
    RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_C]
  ring

end RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

namespace RepresentationTheory.GeneralLinearRepresentation.SubrepresentationQuotient

namespace GeneralLinearRepresentation

variable {k : Type*} [Field k] {N : ℕ}

/-- The finite-dimensional representation carried by a subrepresentation. -/
noncomputable def ofSubrepresentation (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) : FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : Module.Finite k σ.toSubmodule := inferInstance
  FDRep.of σ.toRepresentation

/-- The finite-dimensional representation on the quotient by a subrepresentation. -/
noncomputable def quotientBySubrepresentation
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) : FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : Module.Finite k (M ⧸ σ.toSubmodule) :=
    Module.Finite.of_surjective σ.toSubmodule.mkQ σ.toSubmodule.mkQ_surjective
  FDRep.of (Representation.quotient M.ρ σ.toSubmodule (fun g => σ.apply_mem_toSubmodule g))

/-- The canonical inclusion of a subrepresentation intertwines its action with the ambient action. -/
theorem subrepresentationSubtype_equivariant
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) (g : Matrix.GeneralLinearGroup (Fin N) k)
    (v : ofSubrepresentation M σ) :
    σ.toSubmodule.subtype ((ofSubrepresentation M σ).ρ g v) =
      M.ρ g (σ.toSubmodule.subtype v) := rfl

/-- The canonical linear inclusion of a subrepresentation is injective. -/
theorem subrepresentationSubtype_injective
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) :
    Function.Injective (σ.toSubmodule.subtype : ofSubrepresentation M σ →ₗ[k] M) :=
  Subtype.val_injective

/-- The canonical quotient map intertwines the original action with the quotient representation action. -/
theorem quotientMap_equivariant (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) (g : Matrix.GeneralLinearGroup (Fin N) k) (v : M) :
    σ.toSubmodule.mkQ (M.ρ g v) =
      (quotientBySubrepresentation M σ).ρ g (σ.toSubmodule.mkQ v) := rfl

/-- The canonical linear map to the quotient by a subrepresentation is surjective. -/
theorem quotientMap_surjective (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ) :
    Function.Surjective
      (σ.toSubmodule.mkQ : M →ₗ[k] quotientBySubrepresentation M σ) :=
  σ.toSubmodule.mkQ_surjective

/-- The range of the subrepresentation inclusion equals the kernel of the canonical quotient map. -/
theorem range_subtype_eq_ker_quotientMap
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ) :
    LinearMap.range (σ.toSubmodule.subtype : ofSubrepresentation M σ →ₗ[k] M) =
      LinearMap.ker
        (σ.toSubmodule.mkQ : M →ₗ[k] quotientBySubrepresentation M σ) := by
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

/-- The stated auxiliary condition on a general linear group action passes to the quotient representation. -/
theorem auxiliaryCondition_quotient
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (σ : Subrepresentation M.ρ)
    (hM : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N M.ρ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N
      (quotientBySubrepresentation M σ).ρ :=
  hM.auxiliaryQuotient σ.toSubmodule (fun g => σ.apply_mem_toSubmodule g)

/-- Weight spaces span the quotient representation whenever they span the original representation. -/
theorem iSup_weightSpaces_quotient_eq_top [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ)
    (hM : ⨆ μ : Fin N →₀ ℕ,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M
        (fun i => μ i) = ⊤) :
    ⨆ μ : Fin N →₀ ℕ,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N
        (quotientBySubrepresentation M σ) (fun i => μ i) = ⊤ :=
  RepresentationTheory.GeneralLinearRepresentation.WeightSpaceMorphisms.GeneralLinearRepresentation.iSup_weightSpaces_eq_top_of_surjective_equivariant N M
    (quotientBySubrepresentation M σ) σ.toSubmodule.mkQ
    (quotientMap_equivariant M σ) (quotientMap_surjective M σ) hM

/-- When the relevant weight spaces span, the ambient polynomial invariant is the sum of the invariants of a subrepresentation and its quotient. -/
theorem weightPolynomial_eq_subrepresentation_add_quotient [IsAlgClosed k] [CharZero k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (σ : Subrepresentation M.ρ)
    (hsub : ⨆ μ : Fin N →₀ ℕ,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N
        (ofSubrepresentation M σ) (fun i => μ i) = ⊤)
    (hM : ⨆ μ : Fin N →₀ ℕ,
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M
        (fun i => μ i) = ⊤) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N M =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N
          (ofSubrepresentation M σ) +
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N
          (quotientBySubrepresentation M σ) :=
  RepresentationTheory.GeneralLinearRepresentation.WeightSpaceMorphisms.GeneralLinearRepresentation.weightPolynomial_eq_add_of_equivariant_exact N (ofSubrepresentation M σ) M
    (quotientBySubrepresentation M σ) σ.toSubmodule.subtype σ.toSubmodule.mkQ
    (subrepresentationSubtype_equivariant M σ) (quotientMap_equivariant M σ)
    (subrepresentationSubtype_injective M σ) (quotientMap_surjective M σ)
    (range_subtype_eq_ker_quotientMap M σ) hsub hM

end GeneralLinearRepresentation

end RepresentationTheory.GeneralLinearRepresentation.SubrepresentationQuotient

end

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty.auxiliaryElidedStatement005115 := _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty.auxiliaryQuotient

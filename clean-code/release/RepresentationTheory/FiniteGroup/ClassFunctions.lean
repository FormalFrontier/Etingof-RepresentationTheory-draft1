/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.ConjugationInvariantCharacters
import RepresentationTheory.Representation.IsIrreducible
import RepresentationTheory.FDRep.RegularRepresentationCharacter
import RepresentationTheory.FDRep.Character

set_option linter.dupNamespace false

open FDRep CategoryTheory Finset

universe u

namespace RepresentationTheory.FiniteGroup.ClassFunctions

namespace FiniteGroup

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]
  [Invertible (Fintype.card G : k)]

/-- An auxiliary construction sending a field-valued function on a finite group to an element of its group algebra. -/
noncomputable def auxiliaryFunctionToMonoidAlgebra (f : G → k) : MonoidAlgebra k G :=
  ∑ g : G, MonoidAlgebra.single g⁻¹ (f g)

omit [IsAlgClosed k] [DecidableEq G] [Invertible (Fintype.card G : k)] in

private lemma trace_toGroupAlgebra_action (f : G → k) (V : FDRep k G) :
    LinearMap.trace k V (Representation.asAlgebraHom V.ρ (auxiliaryFunctionToMonoidAlgebra f)) =
      ∑ g : G, f g * V.character g⁻¹ := by
  simp only [auxiliaryFunctionToMonoidAlgebra, map_sum, Representation.asAlgebraHom_single]
  congr 1; ext g
  rw [LinearMap.map_smul, smul_eq_mul, FDRep.character]

omit [IsAlgClosed k] [DecidableEq G] [Invertible (Fintype.card G : k)] in

private lemma toGroupAlgebra_injective (f : G → k) (h : auxiliaryFunctionToMonoidAlgebra f = 0) : f = 0 := by
  classical
  ext g
  simp only [Pi.zero_apply]
  have heval : (auxiliaryFunctionToMonoidAlgebra f).coeff g⁻¹ = 0 := by rw [h]; rfl
  simp only [auxiliaryFunctionToMonoidAlgebra] at heval
  rw [MonoidAlgebra.coeff_sum] at heval
  change Finsupp.applyAddHom g⁻¹
      (∑ x : G, (MonoidAlgebra.single x⁻¹ (f x)).coeff) = 0 at heval
  rw [map_sum] at heval
  rw [Finset.sum_eq_single g] at heval
  · simpa [Finsupp.single_apply] using heval
  · intro b _ hb
    simp only [Finsupp.applyAddHom_apply, MonoidAlgebra.coeff_single]
    rw [Finsupp.single_apply, if_neg (show b⁻¹ ≠ g⁻¹ from fun h => hb (inv_injective h))]
  · intro h; exact absurd (Finset.mem_univ g) h

omit [IsAlgClosed k] [DecidableEq G] [Invertible (Fintype.card G : k)] in

private lemma toGroupAlgebra_comm_of (f : G → k)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) (h : G) :
    MonoidAlgebra.single h (1 : k) * auxiliaryFunctionToMonoidAlgebra f =
    auxiliaryFunctionToMonoidAlgebra f * MonoidAlgebra.single h (1 : k) := by
  simp only [auxiliaryFunctionToMonoidAlgebra, Finset.mul_sum, Finset.sum_mul,
    MonoidAlgebra.single_mul_single, one_mul, mul_one]
  refine Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ (fun g => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply]
  rw [show (h * g * h⁻¹)⁻¹ * h = h * g⁻¹ from by group, hf g h]

omit [IsAlgClosed k] [DecidableEq G] [Invertible (Fintype.card G : k)] in

private lemma toGroupAlgebra_central (f : G → k)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    ∀ β : MonoidAlgebra k G, β * auxiliaryFunctionToMonoidAlgebra f = auxiliaryFunctionToMonoidAlgebra f * β := by
  intro β
  induction β using MonoidAlgebra.induction_on with
  | hM g => exact toGroupAlgebra_comm_of f hf g
  | hadd a b ha hb => rw [add_mul, mul_add, ha, hb]
  | hsmul r a ha => rw [smul_mul_assoc, mul_smul_comm, ha]

omit [IsAlgClosed k] in

private lemma matrix_central_eq_scalar {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) k)
    (hM : ∀ N : Matrix (Fin n) (Fin n) k, N * M = M * N) :
    ∃ c : k, M = c • (1 : Matrix (Fin n) (Fin n) k) := by
  have hoff : ∀ r c : Fin n, r ≠ c → M r c = 0 := by
    intro r c hrc
    have h := congr_fun₂ (hM (Matrix.single c r 1)) c c
    simp only [Matrix.mul_apply, Matrix.single_apply, ite_and] at h
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero] at h
    simpa [hrc, Ne.symm hrc] using h
  have hdiag : ∀ i : Fin n, M i i = M 0 0 := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    · have h := congr_fun₂ (hM (Matrix.single (0 : Fin n) i 1)) 0 i
      simp only [Matrix.mul_apply, Matrix.single_apply, ite_and] at h
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_mul, one_mul, zero_mul,
        mul_ite, mul_one, mul_zero] at h
      simpa [Ne.symm hi] using h
  use M 0 0
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp [hdiag]
  · simp [hij, hoff i j hij]

omit [DecidableEq G] [Invertible (Fintype.card G : k)] in

private lemma projRingHom_smul' [NeZero (Nat.card G : k)] (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G) (i : Fin D.count)
    (r : k) (α : MonoidAlgebra k G) :
    D.matrixBlockHom i (r • α) = r • D.matrixBlockHom i α := by
  change (Pi.evalRingHom _ i) (D.groupAlgebraEquivMatrix (r • α)) = r • (Pi.evalRingHom _ i) (D.groupAlgebraEquivMatrix α)
  rw [show D.groupAlgebraEquivMatrix (r • α) = r • D.groupAlgebraEquivMatrix α from map_smul D.groupAlgebraEquivMatrix r α]
  simp [Pi.evalRingHom_apply, Pi.smul_apply]

omit [DecidableEq G] in

private lemma classFunction_eq_zero_of_orthogonal_simples
    (f : G → k) (hf_class : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hf_orth : ∀ (V : FDRep k G) [Simple V], ∑ g : G, f g * V.character g⁻¹ = 0) :
    f = 0 := by
  classical
  apply toGroupAlgebra_injective
  set α := auxiliaryFunctionToMonoidAlgebra f
  haveI : NeZero (Nat.card G : k) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact Invertible.ne_zero _⟩
  let D := RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default (k := k) (G := G)
  suffices h : D.groupAlgebraEquivMatrix α = 0 by exact D.groupAlgebraEquivMatrix.injective (h ▸ (map_zero D.groupAlgebraEquivMatrix).symm ▸ rfl)
  funext i
  change D.matrixBlockHom i α = 0
  haveI := D.dimension_neZero i
  have hcentral : ∀ N, N * D.matrixBlockHom i α = D.matrixBlockHom i α * N := by
    intro N
    obtain ⟨β, rfl⟩ := D.matrixBlockHom_surjective i N
    rw [← map_mul, ← map_mul, toGroupAlgebra_central f hf_class]
  obtain ⟨c, hc⟩ := matrix_central_eq_scalar (D.matrixBlockHom i α) hcentral

  have htrace : Matrix.trace (D.matrixBlockHom i α) = 0 := by
    have hrepr : Representation.asAlgebraHom (D.coordinateRepresentation i) α =
        Matrix.mulVecLin (D.matrixBlockHom i α) := by
      induction α using MonoidAlgebra.induction_on with
      | hM g =>
        simp only [Representation.asAlgebraHom, MonoidAlgebra.lift_of]; rfl
      | hadd a b ha hb => simp only [map_add, ha, hb]
      | hsmul r a ha => simp only [map_smul, projRingHom_smul', ha]
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_apply', ← hrepr]

    have key := trace_toGroupAlgebra_action f (D.representation i)
    simp only [show (D.representation i).ρ = D.coordinateRepresentation i from rfl] at key

    exact key.trans (hf_orth (D.representation i))

  rw [hc] at htrace
  simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htrace

  have hd_ne : (D.dimension i : k) ≠ 0 := D.cast_indexedNat_ne_zero i
  have hc_zero : c = 0 := (mul_eq_zero.mp htrace).resolve_right hd_ne
  rw [hc, hc_zero, zero_smul]

end FiniteGroup

open FiniteGroup in

/-- A conjugation-invariant function is zero if its sum against the inverse character of every simple finite-dimensional representation vanishes. -/
theorem FiniteGroup.ClassFunction.eq_zero_of_characterPairing_eq_zero
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (f : G → k) (hf_class : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hf_orth : ∀ (V : FDRep k G) [Simple V], ∑ g : G, f g * V.character g⁻¹ = 0) :
    f = 0 := by
  classical
  exact FiniteGroup.classFunction_eq_zero_of_orthogonal_simples f hf_class hf_orth

open FiniteGroup in

/-- A conjugation-invariant function on a finite group lies in the span of the characters of simple finite-dimensional representations. -/
@[source_ref "Chapter4/Theorem4.2.1" (role := supporting)]
theorem FiniteGroup.ClassFunction.mem_span_simple_characters
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (f : G → k) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    f ∈ Submodule.span k (FDRep.character '' { V : FDRep k G | Simple V }) := by
  classical
  haveI : NeZero (Nat.card G : k) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact Invertible.ne_zero _⟩
  let D := RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default (k := k) (G := G)

  let c : Fin D.count → k := fun i =>
    ⅟(Fintype.card G : k) * ∑ g : G, f g * (D.representation i).character g⁻¹

  set f' : G → k := ∑ i : Fin D.count, c i • (D.representation i).character with hf'_def

  have hf'_span : f' ∈ Submodule.span k (FDRep.character '' { V : FDRep k G | Simple V }) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, D.simple_representation i, rfl⟩)

  suffices h : f - f' = 0 by
    have := sub_eq_zero.mp h; rwa [this]
  apply classFunction_eq_zero_of_orthogonal_simples
  ·
    intro g h
    simp only [Pi.sub_apply, hf'_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    · exact hf g h
    · congr 1; ext i; congr 1
      exact FDRep.char_conj (D.representation i) g h
  ·
    intro V _
    obtain ⟨j, ⟨iso_j⟩⟩ := D.exists_iso_representation_of_simple V ‹Simple V›

    rw [FDRep.char_iso iso_j]

    have : ∀ g : G, (f - f') g * (D.representation j).character g⁻¹ =
        f g * (D.representation j).character g⁻¹ -
        (∑ i : Fin D.count, c i * (D.representation i).character g) *
          (D.representation j).character g⁻¹ := by
      intro g; simp [Pi.sub_apply, hf'_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul]
    simp_rw [this]
    rw [Finset.sum_sub_distrib, sub_eq_zero]

    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]

    have hinv : ∀ (x y : k), ⅟(Fintype.card G : k) * x = y → x = (Fintype.card G : k) * y := by
      intro x y h
      calc x = (Fintype.card G : k) * ⅟(Fintype.card G : k) * x := by rw [mul_invOf_self, one_mul]
        _ = (Fintype.card G : k) * (⅟(Fintype.card G : k) * x) := by rw [mul_assoc]
        _ = (Fintype.card G : k) * y := by rw [h]
    have horth : ∀ i : Fin D.count,
        ∑ g : G, (D.representation i).character g * (D.representation j).character g⁻¹ =
          if i = j then (Fintype.card G : k) else 0 := by
      intro i
      have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple (D.representation i) (D.representation j)
      rw [smul_eq_mul] at h
      by_cases hij : i = j
      · subst hij
        rw [if_pos ⟨Iso.refl _⟩] at h
        rw [if_pos rfl]; exact (hinv _ _ h).trans (mul_one _)
      · have hne : ¬ Nonempty (D.representation i ≅ D.representation j) :=
          fun ⟨iso⟩ => hij (D.representation_index_eq_of_iso i j ⟨iso⟩)
        rw [if_neg hne] at h
        rw [if_neg hij]; exact (hinv _ _ h).trans (mul_zero _)
    simp_rw [horth]

    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

    set S := ∑ g, f g * (D.representation j).character g⁻¹
    change S = (⅟(Fintype.card G : k) * S) * (Fintype.card G : k)
    rw [mul_comm (⅟_ * S) _, ← mul_assoc, mul_invOf_self, one_mul]

open FiniteGroup in

/-- An auxiliary linear-independence result for the displayed subtype inclusion over the coefficient field. -/
@[source_ref "Chapter4/Theorem4.2.1" (role := supporting)]
theorem FiniteGroup.auxiliarySubtypeValLinearIndependent
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)] :
    LinearIndependent k
      (Subtype.val : ↥(FDRep.character '' { V : FDRep k G | Simple V }) → (G → k)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i₀ hi₀

  choose V hVmem hVchar using fun i : ↥(FDRep.character '' { V : FDRep k G | Simple V }) => i.2

  have hinv : ∀ (x y : k), ⅟(Fintype.card G : k) * x = y → x = (Fintype.card G : k) * y := by
    intro x y h
    rw [← h, ← mul_assoc, mul_invOf_self, one_mul]

  have happly : ∑ x : G,
      (∑ i ∈ s, g i • (i : G → k)) x * (V i₀).character x⁻¹ = 0 := by
    rw [hsum]; simp

  have hexpand : ∑ x : G, (∑ i ∈ s, g i • (i : G → k)) x * (V i₀).character x⁻¹
      = ∑ i ∈ s, g i * (∑ x : G, (i : G → k) x * (V i₀).character x⁻¹) := by
    simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]

  have hdiag : ∑ i ∈ s, g i * (∑ x : G, (i : G → k) x * (V i₀).character x⁻¹)
      = g i₀ * (Fintype.card G : k) := by
    rw [Finset.sum_eq_single i₀]
    · congr 1
      rw [← hVchar i₀]
      haveI : Simple (V i₀) := hVmem i₀
      have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple (V i₀) (V i₀)
      rw [smul_eq_mul, if_pos ⟨Iso.refl _⟩] at h
      exact (hinv _ _ h).trans (mul_one _)
    · intro i _ hne
      have hval_ne : (i : G → k) ≠ (i₀ : G → k) := Subtype.coe_injective.ne hne
      have hchar_ne : (V i).character ≠ (V i₀).character := by
        rw [hVchar i, hVchar i₀]; exact hval_ne
      have hno_iso : ¬ Nonempty (V i ≅ V i₀) := fun ⟨e⟩ => hchar_ne (FDRep.char_iso e)
      have hzero : (∑ x : G, (i : G → k) x * (V i₀).character x⁻¹) = 0 := by
        rw [← hVchar i]
        haveI : Simple (V i) := hVmem i
        haveI : Simple (V i₀) := hVmem i₀
        have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple (V i) (V i₀)
        rw [smul_eq_mul, if_neg hno_iso] at h
        exact (hinv _ _ h).trans (mul_zero _)
      rw [hzero, mul_zero]
    · intro h; exact absurd hi₀ h

  have hfin : g i₀ * (Fintype.card G : k) = 0 := by
    rw [← hdiag, ← hexpand]; exact happly
  exact (mul_eq_zero.mp hfin).resolve_right (Invertible.ne_zero _)

/-- The span of the characters of simple finite-dimensional representations equals the displayed auxiliary submodule of functions on the group. -/
@[source_ref "Chapter4/Theorem4.2.1" (role := supporting),
  source_ref "Chapter4/Introduction_4.5/Derived2" (role := supporting)]
theorem FiniteGroup.span_simple_characters_eq_auxiliarySubmodule
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)] :
    Submodule.span k (FDRep.character '' {V : FDRep k G | Simple V}) =
      RepresentationTheory.ConjugationInvariantCharacters.conjugationInvariantSubmodule k G := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨V, _, rfl⟩
    exact RepresentationTheory.ConjugationInvariantCharacters.character_mem_conjugationInvariantSubmodule k G V
  · intro f hf
    exact FiniteGroup.ClassFunction.mem_span_simple_characters f hf

end RepresentationTheory.FiniteGroup.ClassFunctions

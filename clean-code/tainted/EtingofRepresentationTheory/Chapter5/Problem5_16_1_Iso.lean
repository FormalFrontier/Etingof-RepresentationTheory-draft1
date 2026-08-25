import EtingofRepresentationTheory.Chapter5.Problem5_16_1
import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Chapter5.CleanCharacterExtractionBase
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Infrastructure.FDRepDirectSum
import EtingofRepresentationTheory.Infrastructure.FDRepIsotypic

/-!
# Problem 5.16.1: representation-level branching isomorphisms

The character and multiplicity formulas in `Problem5_16_1` are useful computational
forms of the branching rule.  This file exposes the source's actual direct-sum
isomorphisms.
-/

noncomputable section

open CategoryTheory Module

namespace Etingof

private theorem spechtModule_asModule_smul (n : ℕ) (la : Nat.Partition n)
    (a : SymGroupAlgebra n) (v : (spechtModuleRep n la).asModule) :
    a • v = (show ↥(SpechtModule n la) from a •
      (show ↥(SpechtModule n la) from v)) := by
  classical
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
      change MonoidAlgebra.single g 1 • v = _
      rw [Representation.single_smul]
      simp only [one_smul, Representation.asModuleEquiv]
      simp [spechtModuleRep, spechtModuleAction]
      rfl
  | hadd x y hx hy =>
      rw [add_smul, hx, hy, add_smul]
  | hsmul r x hx =>
      rw [smul_assoc, hx, smul_assoc]

/-- The group-algebra module attached to the Specht representation is the book's
`SpechtModule`, with its original group-algebra action. -/
noncomputable def spechtModuleAsModuleEquiv (n : ℕ) (la : Nat.Partition n) :
    (spechtModuleRep n la).asModule ≃ₗ[SymGroupAlgebra n] SpechtModule n la :=
  { (spechtModuleRep n la).asModuleEquiv with
    map_smul' := fun a v => spechtModule_asModule_smul n la a v }

/-- The Specht representations exhaust the simple objects of `FDRep ℂ Sₙ`. -/
theorem simple_iso_spechtModuleFDRep (n : ℕ)
    (S : FDRep ℂ (Equiv.Perm (Fin n))) [Simple S] :
    ∃ la : Nat.Partition n, Nonempty (S ≅ spechtModuleFDRep n la) := by
  haveI : IsSimpleModule (SymGroupAlgebra n) (Representation.asModule S.ρ) :=
    isSimpleModule_asModule_of_simple S
  obtain ⟨la, ⟨f⟩⟩ :=
    Theorem5_12_2_classification n (Representation.asModule S.ρ)
  let φ : Representation.asModule S.ρ ≃ₗ[SymGroupAlgebra n]
      (spechtModuleRep n la).asModule :=
    f ≪≫ₗ (spechtModuleAsModuleEquiv n la).symm
  exact ⟨la, ⟨Action.mkIso (Representation.kEquivOfAsModuleEquiv φ).toFGModuleCatIso
    (fun g => by
      ext x
      exact Representation.kEquivOfAsModuleEquiv_intertwines φ g x)⟩⟩

/-- Restriction of the Specht representation `V_μ` along `Sₙ ↪ Sₙ₊₁`. -/
noncomputable def restrictionSpechtFDRep (n : ℕ) (μ : Nat.Partition (n + 1)) :
    FDRep ℂ (Equiv.Perm (Fin n)) :=
  FDRep.of ((spechtModuleFDRep (n + 1) μ).ρ.comp (permEmb n))

/-- The direct sum of the Specht modules obtained by removing one square from `μ`. -/
noncomputable def removeSquareSumFDRep (n : ℕ) (μ : Nat.Partition (n + 1)) :
    FDRep ℂ (Equiv.Perm (Fin n)) :=
  FDRep.pi (fun (p : ↥(removeSquare μ)) => spechtModuleFDRep n p.1)

/-- **Problem 5.16.1(a), representation-level form.** Restriction of `V_μ` from
`Sₙ₊₁` to `Sₙ` is isomorphic to the direct sum of the `V_λ` obtained by removing
one square. -/
theorem restriction_spechtModule_iso_removeSquareSum (n : ℕ)
    (μ : Nat.Partition (n + 1)) :
    Nonempty (restrictionSpechtFDRep n μ ≅ removeSquareSumFDRep n μ) := by
  apply charEq_iso
  funext σ
  unfold restrictionSpechtFDRep removeSquareSumFDRep
  rw [FDRep.character_pi]
  change spechtModuleCharacter (n + 1) μ (permEmb n σ) =
    ∑ p : ↥(removeSquare μ), spechtModuleCharacter n p.1 σ
  rw [res_spechtModule_character]
  exact (Finset.sum_attach (removeSquare μ)
    (fun p => spechtModuleCharacter n p σ)).symm

/-- Induction of `V_μ` along `Sₙ ↪ Sₙ₊₁`. -/
noncomputable def inductionSpechtFDRep (n : ℕ) (μ : Nat.Partition n) :
    FDRep ℂ (Equiv.Perm (Fin (n + 1))) :=
  FDRep.of (Representation.ind (permEmb n) (spechtModuleRep n μ))

/-- The direct sum of the Specht modules obtained by adding one square to `μ`. -/
noncomputable def addSquareSumFDRep (n : ℕ) (μ : Nat.Partition n) :
    FDRep ℂ (Equiv.Perm (Fin (n + 1))) :=
  FDRep.pi (fun (p : ↥(addSquare μ)) => spechtModuleFDRep (n + 1) p.1)

/-- Restriction along the standard embedding `Sₙ ↪ Sₙ₊₁`. -/
noncomputable abbrev restrictFDRep (n : ℕ)
    (S : FDRep ℂ (Equiv.Perm (Fin (n + 1)))) :
    FDRep ℂ (Equiv.Perm (Fin n)) :=
  (Action.res (FGModuleCat ℂ) (permEmb n)).obj S

private theorem frobenius_finrank_permEmb (n : ℕ) (μ : Nat.Partition n)
    (S : FDRep ℂ (Equiv.Perm (Fin (n + 1)))) :
    finrank ℂ (inductionSpechtFDRep n μ ⟶ S) =
      finrank ℂ (spechtModuleFDRep n μ ⟶ restrictFDRep n S) := by
  rw [← (FDRep.forget₂HomLinearEquiv (inductionSpechtFDRep n μ) S).finrank_eq]
  have hG :
      (forget₂ (FDRep ℂ (Equiv.Perm (Fin (n + 1))))
        (Rep ℂ (Equiv.Perm (Fin (n + 1))))).obj (inductionSpechtFDRep n μ) =
        Rep.ind (permEmb n) (Rep.of (spechtModuleRep n μ)) := rfl
  rw [hG, (Rep.indResHomEquiv (permEmb n) (Rep.of (spechtModuleRep n μ))
    ((forget₂ (FDRep ℂ (Equiv.Perm (Fin (n + 1))))
      (Rep ℂ (Equiv.Perm (Fin (n + 1))))).obj S)).finrank_eq]
  have hW : Rep.of (spechtModuleRep n μ) =
      (forget₂ (FDRep ℂ (Equiv.Perm (Fin n)))
        (Rep ℂ (Equiv.Perm (Fin n)))).obj (spechtModuleFDRep n μ) := rfl
  have hRes :
      (Rep.resFunctor (permEmb n)).obj
          ((forget₂ (FDRep ℂ (Equiv.Perm (Fin (n + 1))))
            (Rep ℂ (Equiv.Perm (Fin (n + 1))))).obj S) =
        (forget₂ (FDRep ℂ (Equiv.Perm (Fin n)))
          (Rep ℂ (Equiv.Perm (Fin n)))).obj (restrictFDRep n S) := rfl
  rw [← (FDRep.forget₂HomLinearEquiv
    (spechtModuleFDRep n μ) (restrictFDRep n S)).finrank_eq, ← hW, ← hRes]

private theorem finrank_hom_symm' {G : Type} [Group G] [Finite G]
    (V W : FDRep ℂ G) : finrank ℂ (V ⟶ W) = finrank ℂ (W ⟶ V) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hVW := FDRep.scalar_product_char_eq_finrank_equivariant V W
  have hWV := FDRep.scalar_product_char_eq_finrank_equivariant W V
  have hcast : (finrank ℂ (V ⟶ W) : ℂ) = (finrank ℂ (W ⟶ V) : ℂ) := by
    rw [← hVW, ← hWV]
    congr 1
    rw [← Equiv.sum_comp (Equiv.inv G) (fun g => V.character g * W.character g⁻¹)]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    change W.character g * V.character g⁻¹ = V.character g⁻¹ * W.character g⁻¹⁻¹
    rw [inv_inv, mul_comm]
  exact_mod_cast hcast

open Classical in
private theorem specht_restriction_finrank (n : ℕ) (μ : Nat.Partition n)
    (la : Nat.Partition (n + 1)) :
    finrank ℂ (spechtModuleFDRep n μ ⟶
        restrictFDRep n (spechtModuleFDRep (n + 1) la)) =
      if μ.toYoungDiagram ≤ la.toYoungDiagram then 1 else 0 := by
  haveI : Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hscalar := FDRep.scalar_product_char_eq_finrank_equivariant
    (restrictFDRep n (spechtModuleFDRep (n + 1) la)) (spechtModuleFDRep n μ)
  have hpair : branchingPairing n (spechtModuleCharacter n μ)
      (fun σ => spechtModuleCharacter (n + 1) la (permEmb n σ)) =
      (finrank ℂ (restrictFDRep n (spechtModuleFDRep (n + 1) la) ⟶
        spechtModuleFDRep n μ) : ℂ) := by
    have hres : ∀ σ : Equiv.Perm (Fin n),
        (restrictFDRep n (spechtModuleFDRep (n + 1) la)).character σ =
          spechtModuleCharacter (n + 1) la (permEmb n σ) := fun _ => rfl
    simpa [branchingPairing, invOf_eq_inv, smul_eq_mul,
      spechtModuleFDRep_character, hres, map_inv] using hscalar
  have hvalue := ind_spechtModule_multiplicity n μ la
  rw [hpair] at hvalue
  rw [finrank_hom_symm' (spechtModuleFDRep n μ)
    (restrictFDRep n (spechtModuleFDRep (n + 1) la))]
  exact_mod_cast hvalue

/-- **Problem 5.16.1(b), representation-level form.** Induction of `V_μ` from
`Sₙ` to `Sₙ₊₁` is isomorphic to the direct sum of the `V_λ` obtained by adding
one square. -/
theorem induction_spechtModule_iso_addSquareSum (n : ℕ) (μ : Nat.Partition n) :
    Nonempty (inductionSpechtFDRep n μ ≅ addSquareSumFDRep n μ) := by
  classical
  refine iso_of_forall_finrank_hom_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  obtain ⟨la, ⟨e⟩⟩ := simple_iso_spechtModuleFDRep (n + 1) S
  have hleft : finrank ℂ (S ⟶ inductionSpechtFDRep n μ) =
      if μ.toYoungDiagram ≤ la.toYoungDiagram then 1 else 0 := by
    rw [finrank_hom_symm', frobenius_finrank_permEmb]
    rw [finrank_hom_congr_right (spechtModuleFDRep n μ)
      ((Action.res (FGModuleCat ℂ) (permEmb n)).mapIso e)]
    exact specht_restriction_finrank n μ la
  have hiso : ∀ p : ↥(addSquare μ),
      Nonempty (S ≅ spechtModuleFDRep (n + 1) p.1) ↔ la = p.1 := by
    intro p
    constructor
    · rintro ⟨f⟩
      exact (spechtModuleFDRep_iso_iff_eq (n + 1) la p.1).mp
        ⟨e.symm ≪≫ f⟩
    · rintro rfl
      exact ⟨e⟩
  have hright : finrank ℂ (S ⟶ addSquareSumFDRep n μ) =
      if μ.toYoungDiagram ≤ la.toYoungDiagram then 1 else 0 := by
    unfold addSquareSumFDRep
    rw [finrank_hom_congr_right S (FDRep.piIsoBiproduct
      (fun p : ↥(addSquare μ) => spechtModuleFDRep (n + 1) p.1))]
    rw [FDRep.finrank_hom_biproduct]
    by_cases hmem : la ∈ addSquare μ
    · rw [if_pos (by simpa [addSquare] using hmem)]
      calc
        ∑ p : ↥(addSquare μ), finrank ℂ (S ⟶ spechtModuleFDRep (n + 1) p.1) =
            finrank ℂ (S ⟶ spechtModuleFDRep (n + 1) la) := by
          refine Finset.sum_eq_single (s := Finset.univ)
            (f := fun p : ↥(addSquare μ) =>
              finrank ℂ (S ⟶ spechtModuleFDRep (n + 1) p.1))
            (⟨la, hmem⟩ : ↥(addSquare μ)) ?_ ?_
          · intro p _ hp
            rw [FDRep.finrank_hom_simple_simple, if_neg]
            intro hSp
            apply hp
            exact Subtype.ext ((hiso p).mp hSp).symm
          · simp
        _ = 1 := by rw [FDRep.finrank_hom_simple_simple, if_pos ⟨e⟩]
    · rw [if_neg (by simpa [addSquare] using hmem)]
      apply Finset.sum_eq_zero
      intro p _
      rw [FDRep.finrank_hom_simple_simple, if_neg]
      intro hSp
      apply hmem
      rw [(hiso p).mp hSp]
      exact p.2
  rw [hleft, hright]

end Etingof

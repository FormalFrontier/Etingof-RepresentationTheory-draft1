import Mathlib
import EtingofRepresentationTheory.Chapter5.Remark5_2_8
import EtingofRepresentationTheory.Chapter4.Discussion_4_4
import EtingofRepresentationTheory.Infrastructure.FDRepDirectSum
import EtingofRepresentationTheory.Infrastructure.FDRepIsotypic
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Infrastructure.CharacterOrthogonalityCompat

/-!
# Problem 5.2.7: fields of definition and a vanishing character value

> **Problem 5.2.7(b).** Show that if `V` is an irreducible complex representation of a
> finite group `G` of dimension `> 1`, then there exists `g ∈ G` such that `χ_V(g) = 0`.
>
> Hint: Assume the contrary. Use orthonormality of characters to show that the
> arithmetic mean of the numbers `|χ_V(g)|²` for `g ≠ 1` is `< 1`. Deduce that their
> product `β` satisfies `0 < β < 1`. Show that all conjugates of `β` satisfy the same
> inequalities and derive a contradiction.

For part (a), this file proves the full simultaneous field-of-definition assertion. It constructs
a Wedderburn decomposition of the group algebra over the algebraic closure `ℚ̄ ⊆ ℂ`, transports
it to `ℂ`, and obtains a finite complete family of complex simple representations whose standard
bases have algebraic action matrices. Isotypic decomposition then gives algebraic matrix bases for
all representations. Finally, the finitely many coefficients of the simple family are enclosed in
one finite Galois extension of `ℚ`; closure under finite direct sums and representation isomorphisms
shows that this single field works for every finite-dimensional complex representation of `G`.

For part (b), this file supplies the two pieces the book's argument still needs on top of the
Galois-conjugate rationality core already formalized in
`EtingofRepresentationTheory.Chapter5.Remark5_2_8`:

1. `beta_lt_one` — the `0 < β < 1` bound. This is the *only* step where irreducibility
   and `dim V > 1` enter. Writing `β = ∏_{g ≠ 1} |χ_V(g)|²`, the first orthogonality
   relation (`FDRep.char_orthonormal`) gives `∑_g |χ_V(g)|² = |G|`, hence
   `∑_{g ≠ 1} |χ_V(g)|² = |G| - (dim V)²`. Since `dim V > 1` this sum is `< |G| - 1`, the
   number of factors, so the arithmetic mean of the `|χ_V(g)|²` is `< 1`; AM-GM
   (`Real.geom_mean_le_arith_mean`) then forces the product `β < 1`, while positivity of
   each factor (under the contradiction hypothesis `χ_V(g) ≠ 0`) gives `0 < β`.

2. `exists_character_eq_zero` — the honest top-level conclusion `∃ g, χ_V(g) = 0`.
   Assuming the contrary, `β = ∏_{g ≠ 1} χ_V(g)·χ_V(g⁻¹)` is a rational
   (`Etingof.Remark5_2_8.character_prod_rat`) algebraic integer, and step 1 gives
   `0 < β < 1`; `Etingof.Remark5_2_8.beta_rat_not_mem_Ioo` derives `False`.

-/

namespace Etingof.Problem5_2_7

open Finset CategoryTheory
open scoped TensorProduct

variable {G : Type} [Group G]

/-! ## Part (a): finite Galois envelopes for algebraic matrix realizations -/

/-- Scalar extension commutes with a group algebra, without requiring the group to be
commutative:
`C ⊗[A] A[G] ≃ₐ[C] C[G]`.

Mathlib's `MonoidAlgebra.scalarTensorEquiv` currently assumes `CommMonoid G`; the construction
here uses the tensor-product and monoid-algebra universal properties directly, so it applies to
the arbitrary finite groups needed for Problem 5.2.7(a). -/
noncomputable def groupAlgebraScalarTensorEquiv
    (A C G : Type) [Field A] [Field C] [Algebra A C] [Group G] :
    C ⊗[A] MonoidAlgebra A G ≃ₐ[C] MonoidAlgebra C G := by
  let f : C ⊗[A] MonoidAlgebra A G →ₐ[C] MonoidAlgebra C G :=
    Algebra.TensorProduct.lift (Algebra.ofId C (MonoidAlgebra C G))
      (MonoidAlgebra.mapAlgHom G (Algebra.ofId A C)) (fun c x => by
        change Commute (algebraMap C (MonoidAlgebra C G) c) _
        exact Algebra.commutes _ _)
  let groupMap : G →* C ⊗[A] MonoidAlgebra A G :=
    (Algebra.TensorProduct.includeRight.toMonoidHom).comp (MonoidAlgebra.of A G)
  let g : MonoidAlgebra C G →ₐ[C] C ⊗[A] MonoidAlgebra A G :=
    (MonoidAlgebra.lift C _ G) groupMap
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AlgHom.toLinearMap_injective
    ext x m
    simp [f, g, groupMap]
  · apply AlgHom.toLinearMap_injective
    ext c
    have hmap : (MonoidAlgebra.mapAlgHom G (Algebra.ofId A C))
        (MonoidAlgebra.single c 1) = MonoidAlgebra.single c 1 := by
      rw [MonoidAlgebra.mapAlgHom_single]
      simp
    simp [f, g, groupMap, hmap]

/-- A representation is defined over the intermediate field `K ⊆ ℂ` if it has a complex basis
in which every matrix entry of every group element belongs to `K`.

The basis index is fixed to `Fin (finrank ℂ V)`, making this predicate convenient to use without
carrying an additional finite index type. -/
def MatrixDefinedOver (K : IntermediateField ℚ ℂ) (V : FDRep ℂ G) : Prop :=
  ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
    ∀ g i j, LinearMap.toMatrix b b (V.ρ g) i j ∈ K

/-- The representation has a basis whose action matrices have algebraic entries. This is the
precise representation-theoretic input needed before the finitely many entries can be enlarged
to one finite Galois field. -/
def HasAlgebraicMatrixBasis (V : FDRep ℂ G) : Prop :=
  ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
    ∀ g i j, IsAlgebraic ℚ (LinearMap.toMatrix b b (V.ρ g) i j)

/-- The matrices of `V` in an arbitrarily indexed finite basis have algebraic entries.

This auxiliary predicate lets us construct natural bases (for instance, the sigma-indexed
basis of a finite direct sum) before reindexing them by `Fin (finrank ℂ V)`. -/
def BasisHasAlgebraicMatrices {I : Type} [Fintype I] [DecidableEq I] (V : FDRep ℂ G)
    (b : Module.Basis I ℂ V) : Prop :=
  ∀ g i j, IsAlgebraic ℚ (LinearMap.toMatrix b b (V.ρ g) i j)

/-- Reindexing a basis preserves algebraicity of all action-matrix entries. -/
theorem BasisHasAlgebraicMatrices.reindex {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {V : FDRep ℂ G} {b : Module.Basis I ℂ V} (h : BasisHasAlgebraicMatrices V b)
    (e : I ≃ J) : BasisHasAlgebraicMatrices V (b.reindex e) := by
  classical
  intro g i j
  simpa [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply] using h g (e.symm i) (e.symm j)

/-- An algebraic action matrix in any finite basis yields an algebraic matrix basis indexed by
`Fin (finrank ℂ V)`. -/
theorem hasAlgebraicMatrixBasis_of_basis {I : Type} [Fintype I] [DecidableEq I]
    {V : FDRep ℂ G}
    (b : Module.Basis I ℂ V) (h : BasisHasAlgebraicMatrices V b) :
    HasAlgebraicMatrixBasis V := by
  let e : I ≃ Fin (Module.finrank ℂ V) :=
    (Fintype.equivFin I).trans (finCongr (Module.finrank_eq_card_basis b).symm)
  refine ⟨b.reindex e, ?_⟩
  exact h.reindex e

/-- Having an algebraic matrix basis is invariant under isomorphism of representations. -/
theorem HasAlgebraicMatrixBasis.of_iso {V W : FDRep ℂ G} (e : V ≅ W)
    (hV : HasAlgebraicMatrixBasis V) : HasAlgebraicMatrixBasis W := by
  obtain ⟨b, hb⟩ := hV
  let φ : V ≃ₗ[ℂ] W := FDRep.isoToLinearEquiv e
  let bW : Module.Basis (Fin (Module.finrank ℂ V)) ℂ W := b.map φ
  have hbW : BasisHasAlgebraicMatrices W bW := by
    intro g i j
    have hinter : W.ρ g (φ (b j)) = φ (V.ρ g (b j)) := by
      rw [FDRep.Iso.conj_ρ e g, LinearEquiv.conj_apply]
      simp [φ]
    simpa [bW, φ, LinearMap.toMatrix_apply, Module.Basis.map_apply, hinter,
      Module.Basis.map] using hb g i j
  exact hasAlgebraicMatrixBasis_of_basis bW hbW

/-- A finite direct sum of representations with algebraic matrix bases again has one. -/
theorem hasAlgebraicMatrixBasis_pi {I : Type} [Fintype I] (V : I → FDRep ℂ G)
    (hV : ∀ i, HasAlgebraicMatrixBasis (V i)) :
    HasAlgebraicMatrixBasis (Etingof.FDRep.pi V) := by
  classical
  let b (i : I) : Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i) := (hV i).choose
  have hb (i : I) : BasisHasAlgebraicMatrices (V i) (b i) := by
    simpa [BasisHasAlgebraicMatrices, b] using (hV i).choose_spec
  let coord : (Etingof.FDRep.pi V : Type) ≃ₗ[ℂ]
      ((p : Σ i, Fin (Module.finrank ℂ (V i))) → ℂ) := {
    toFun := fun x p => (b p.1).repr (x p.1) p.2
    invFun := fun c i => (b i).equivFun.symm (fun j => c ⟨i, j⟩)
    left_inv := fun x => by
      funext i
      exact (b i).equivFun.symm_apply_apply (x i)
    right_inv := fun c => by
      funext ⟨i, j⟩
      exact congrFun ((b i).equivFun.apply_symm_apply (fun q => c ⟨i, q⟩)) j
    map_add' := fun x y => by
      funext ⟨i, j⟩
      exact congrArg (fun z => z j) (map_add ((b i).repr) (x i) (y i))
    map_smul' := fun c x => by
      funext ⟨i, j⟩
      exact congrArg (fun z => z j) (map_smul ((b i).repr) c (x i)) }
  let bπ : Module.Basis (Σ i, Fin (Module.finrank ℂ (V i))) ℂ
      (Etingof.FDRep.pi V) := Module.Basis.ofEquivFun coord
  have hbπ : BasisHasAlgebraicMatrices (Etingof.FDRep.pi V) bπ := by
    rintro g ⟨i, p⟩ ⟨j, q⟩
    change IsAlgebraic ℚ (LinearMap.toMatrix bπ bπ ((Etingof.FDRep.pi V).ρ g)
      ⟨i, p⟩ ⟨j, q⟩)
    by_cases hij : i = j
    · subst j
      have heq : LinearMap.toMatrix bπ bπ ((Etingof.FDRep.pi V).ρ g)
          ⟨i, p⟩ ⟨i, q⟩ = LinearMap.toMatrix (b i) (b i) ((V i).ρ g) p q := by
        rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
        simp only [bπ, Module.Basis.ofEquivFun_repr_apply,
          Module.Basis.coe_ofEquivFun]
        change (b i).repr ((V i).ρ g ((coord.symm (Pi.single ⟨i, q⟩ 1)) i)) p = _
        change (b i).repr ((V i).ρ g
          ((b i).equivFun.symm (fun j =>
            (Pi.single ⟨i, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, j⟩))) p = _
        congr 3
        apply (b i).equivFun.injective
        rw [(b i).equivFun.apply_symm_apply]
        ext j
        simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
      rw [heq]
      exact hb i g p q
    · have hz : LinearMap.toMatrix bπ bπ ((Etingof.FDRep.pi V).ρ g)
          ⟨i, p⟩ ⟨j, q⟩ = 0 := by
        rw [LinearMap.toMatrix_apply]
        simp only [bπ, Module.Basis.ofEquivFun_repr_apply,
          Module.Basis.coe_ofEquivFun]
        change (b i).repr ((V i).ρ g ((coord.symm (Pi.single ⟨j, q⟩ 1)) i)) p = 0
        change (b i).repr ((V i).ρ g
          ((b i).equivFun.symm (fun r =>
            (Pi.single ⟨j, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, r⟩))) p = 0
        have hfun : (fun r =>
            (Pi.single ⟨j, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, r⟩) = 0 := by
          funext r
          have hne : (⟨j, q⟩ : Σ k, Fin (Module.finrank ℂ (V k))) ≠ ⟨i, r⟩ := by
            intro h
            exact hij (Sigma.mk.inj_iff.mp h).1.symm
          simp [hne]
        rw [hfun, map_zero, map_zero]
        simp
      rw [hz]
      exact isAlgebraic_zero
  exact hasAlgebraicMatrixBasis_of_basis bπ hbπ

/-- **Assembly from a complete simple family.** If a finite complete family of pairwise
non-isomorphic simple representations has algebraic matrix bases, then every representation does.

Thus the remaining descent problem in 5.2.7(a) is reduced to constructing algebraic bases for
one finite complete family of simple representations. -/
theorem hasAlgebraicMatrixBasis_of_complete_simple_family [Fintype G]
    {I : Type} [Fintype I] (T : I → FDRep ℂ G)
    (hsimple : ∀ i, Simple (T i))
    (hinj : ∀ i j, Nonempty (T i ≅ T j) → i = j)
    (hcomplete : ∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ T i))
    (hAlg : ∀ i, HasAlgebraicMatrixBasis (T i)) (V : FDRep ℂ G) :
    HasAlgebraicMatrixBasis V := by
  classical
  let n := Etingof.FDRep.multiplicity T V
  let U : (Σ i, Fin (n i)) → FDRep ℂ G := fun p => T p.1
  have hpi : HasAlgebraicMatrixBasis (Etingof.FDRep.pi U) :=
    hasAlgebraicMatrixBasis_pi U (fun p => hAlg p.1)
  let eV : V ≅ Etingof.FDRep.isotypicSum T n :=
    (Etingof.FDRep.nonempty_iso_isotypicSum T hsimple hinj hcomplete V).some
  let eπ : Etingof.FDRep.pi U ≅ Etingof.FDRep.isotypicSum T n :=
    Etingof.FDRep.piIsoBiproduct U
  exact hpi.of_iso ((eV.trans eπ.symm).symm)

/-- The matrices of `V` in an arbitrarily indexed finite basis all have entries in `K`. -/
def BasisHasMatricesIn (K : IntermediateField ℚ ℂ) {I : Type} [Fintype I]
    [DecidableEq I] (V : FDRep ℂ G) (b : Module.Basis I ℂ V) : Prop :=
  ∀ g i j, LinearMap.toMatrix b b (V.ρ g) i j ∈ K

/-- Reindexing a basis preserves membership of all action-matrix entries in `K`. -/
theorem BasisHasMatricesIn.reindex {K : IntermediateField ℚ ℂ}
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {V : FDRep ℂ G} {b : Module.Basis I ℂ V} (h : BasisHasMatricesIn K V b)
    (e : I ≃ J) : BasisHasMatricesIn K V (b.reindex e) := by
  classical
  intro g i j
  simpa [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply] using h g (e.symm i) (e.symm j)

/-- A matrix realization in any finite basis yields `MatrixDefinedOver K`. -/
theorem matrixDefinedOver_of_basis {K : IntermediateField ℚ ℂ}
    {I : Type} [Fintype I] [DecidableEq I] {V : FDRep ℂ G}
    (b : Module.Basis I ℂ V) (h : BasisHasMatricesIn K V b) : MatrixDefinedOver K V := by
  let e : I ≃ Fin (Module.finrank ℂ V) :=
    (Fintype.equivFin I).trans (finCongr (Module.finrank_eq_card_basis b).symm)
  exact ⟨b.reindex e, h.reindex e⟩

/-- Being defined over `K` is invariant under isomorphism of representations. -/
theorem MatrixDefinedOver.of_iso {K : IntermediateField ℚ ℂ} {V W : FDRep ℂ G}
    (e : V ≅ W) (hV : MatrixDefinedOver K V) : MatrixDefinedOver K W := by
  obtain ⟨b, hb⟩ := hV
  let φ : V ≃ₗ[ℂ] W := FDRep.isoToLinearEquiv e
  let bW : Module.Basis (Fin (Module.finrank ℂ V)) ℂ W := b.map φ
  have hbW : BasisHasMatricesIn K W bW := by
    intro g i j
    have hinter : W.ρ g (φ (b j)) = φ (V.ρ g (b j)) := by
      rw [FDRep.Iso.conj_ρ e g, LinearEquiv.conj_apply]
      simp [φ]
    simpa [bW, φ, LinearMap.toMatrix_apply, Module.Basis.map_apply, hinter,
      Module.Basis.map] using hb g i j
  exact matrixDefinedOver_of_basis bW hbW

/-- A finite direct sum of representations defined over `K` is again defined over `K`. -/
theorem matrixDefinedOver_pi {I : Type} [Fintype I] (V : I → FDRep ℂ G)
    {K : IntermediateField ℚ ℂ} (hV : ∀ i, MatrixDefinedOver K (V i)) :
    MatrixDefinedOver K (Etingof.FDRep.pi V) := by
  classical
  let b (i : I) : Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i) := (hV i).choose
  have hb (i : I) : BasisHasMatricesIn K (V i) (b i) := by
    simpa [BasisHasMatricesIn, b] using (hV i).choose_spec
  let coord : (Etingof.FDRep.pi V : Type) ≃ₗ[ℂ]
      ((p : Σ i, Fin (Module.finrank ℂ (V i))) → ℂ) := {
    toFun := fun x p => (b p.1).repr (x p.1) p.2
    invFun := fun c i => (b i).equivFun.symm (fun j => c ⟨i, j⟩)
    left_inv := fun x => by
      funext i
      exact (b i).equivFun.symm_apply_apply (x i)
    right_inv := fun c => by
      funext ⟨i, j⟩
      exact congrFun ((b i).equivFun.apply_symm_apply (fun q => c ⟨i, q⟩)) j
    map_add' := fun x y => by
      funext ⟨i, j⟩
      exact congrArg (fun z => z j) (map_add ((b i).repr) (x i) (y i))
    map_smul' := fun c x => by
      funext ⟨i, j⟩
      exact congrArg (fun z => z j) (map_smul ((b i).repr) c (x i)) }
  let bπ : Module.Basis (Σ i, Fin (Module.finrank ℂ (V i))) ℂ
      (Etingof.FDRep.pi V) := Module.Basis.ofEquivFun coord
  have hbπ : BasisHasMatricesIn K (Etingof.FDRep.pi V) bπ := by
    rintro g ⟨i, p⟩ ⟨j, q⟩
    by_cases hij : i = j
    · subst j
      have heq : LinearMap.toMatrix bπ bπ ((Etingof.FDRep.pi V).ρ g)
          ⟨i, p⟩ ⟨i, q⟩ = LinearMap.toMatrix (b i) (b i) ((V i).ρ g) p q := by
        rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
        simp only [bπ, Module.Basis.ofEquivFun_repr_apply, Module.Basis.coe_ofEquivFun]
        change (b i).repr ((V i).ρ g ((coord.symm (Pi.single ⟨i, q⟩ 1)) i)) p = _
        change (b i).repr ((V i).ρ g
          ((b i).equivFun.symm (fun j =>
            (Pi.single ⟨i, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, j⟩))) p = _
        congr 3
        apply (b i).equivFun.injective
        rw [(b i).equivFun.apply_symm_apply]
        ext j
        simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
      rw [heq]
      exact hb i g p q
    · have hz : LinearMap.toMatrix bπ bπ ((Etingof.FDRep.pi V).ρ g)
          ⟨i, p⟩ ⟨j, q⟩ = 0 := by
        rw [LinearMap.toMatrix_apply]
        simp only [bπ, Module.Basis.ofEquivFun_repr_apply, Module.Basis.coe_ofEquivFun]
        change (b i).repr ((V i).ρ g ((coord.symm (Pi.single ⟨j, q⟩ 1)) i)) p = 0
        change (b i).repr ((V i).ρ g
          ((b i).equivFun.symm (fun r =>
            (Pi.single ⟨j, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, r⟩))) p = 0
        have hfun : (fun r =>
            (Pi.single ⟨j, q⟩ (1 : ℂ) :
              (Σ k, Fin (Module.finrank ℂ (V k))) → ℂ) ⟨i, r⟩) = 0 := by
          funext r
          have hne : (⟨j, q⟩ : Σ k, Fin (Module.finrank ℂ (V k))) ≠ ⟨i, r⟩ := by
            intro h
            exact hij (Sigma.mk.inj_iff.mp h).1.symm
          simp [hne]
        rw [hfun, map_zero, map_zero]
        simp
      rw [hz]
      exact K.zero_mem
  exact matrixDefinedOver_of_basis bπ hbπ

/-- A finite complete family defined over `K` gives a `K`-matrix realization of every
finite-dimensional representation. -/
theorem matrixDefinedOver_of_complete_simple_family [Fintype G]
    {K : IntermediateField ℚ ℂ} {I : Type} [Fintype I] (T : I → FDRep ℂ G)
    (hsimple : ∀ i, Simple (T i))
    (hinj : ∀ i j, Nonempty (T i ≅ T j) → i = j)
    (hcomplete : ∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ T i))
    (hK : ∀ i, MatrixDefinedOver K (T i)) (V : FDRep ℂ G) : MatrixDefinedOver K V := by
  classical
  let n := Etingof.FDRep.multiplicity T V
  let U : (Σ i, Fin (n i)) → FDRep ℂ G := fun p => T p.1
  have hpi : MatrixDefinedOver K (Etingof.FDRep.pi U) :=
    matrixDefinedOver_pi U (fun p => hK p.1)
  let eV : V ≅ Etingof.FDRep.isotypicSum T n :=
    (Etingof.FDRep.nonempty_iso_isotypicSum T hsimple hinj hcomplete V).some
  let eπ : Etingof.FDRep.pi U ≅ Etingof.FDRep.isotypicSum T n :=
    Etingof.FDRep.piIsoBiproduct U
  exact hpi.of_iso ((eV.trans eπ.symm).symm)

/-- Enlarging the coefficient field preserves a matrix realization. -/
theorem MatrixDefinedOver.mono {K L : IntermediateField ℚ ℂ} (hKL : K ≤ L)
    {V : FDRep ℂ G} (hV : MatrixDefinedOver K V) : MatrixDefinedOver L V := by
  obtain ⟨b, hb⟩ := hV
  exact ⟨b, fun g i j => hKL (hb g i j)⟩

/-- Algebraic matrix entries are exactly matrix entries in the algebraic closure of `ℚ` inside
`ℂ`. -/
theorem hasAlgebraicMatrixBasis_iff (V : FDRep ℂ G) :
    HasAlgebraicMatrixBasis V ↔ MatrixDefinedOver (algebraicClosure ℚ ℂ) V := by
  constructor <;> rintro ⟨b, hb⟩ <;> refine ⟨b, fun g i j => ?_⟩
  · exact mem_algebraicClosure_iff.mpr (hb g i j)
  · exact mem_algebraicClosure_iff.mp (hb g i j)

/-- **Finite Galois envelope, simultaneous form.** A finite family of complex representations
with algebraic matrix bases is defined over one common finite Galois intermediate field of
`ℚ ⊆ ℂ`.

This proves the field-theoretic half of Problem 5.2.7(a), including its important quantifier
order for any finite family. The remaining group-representation input is to reduce all
representations to a finite family and construct algebraic matrix bases for that family. -/
theorem exists_common_finite_galois_matrix_field [Fintype G] {I : Type} [Fintype I]
    (V : I → FDRep ℂ G) (hV : ∀ i, HasAlgebraicMatrixBasis (V i)) :
    ∃ K : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ ∀ i, MatrixDefinedOver K (V i) := by
  classical
  letI : IsAlgClosure ℚ (algebraicClosure ℚ ℂ) :=
    algebraicClosure.isAlgClosure ℚ ℂ
  letI : IsGalois ℚ (algebraicClosure ℚ ℂ) :=
    IsAlgClosure.isGalois ℚ (algebraicClosure ℚ ℂ)
  let b (i : I) : Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i) := (hV i).choose
  have hb (i : I) : ∀ g p q, IsAlgebraic ℚ
      (LinearMap.toMatrix (b i) (b i) ((V i).ρ g) p q) := (hV i).choose_spec
  let CoeffIndex := Σ i : I, G × Fin (Module.finrank ℂ (V i)) ×
    Fin (Module.finrank ℂ (V i))
  let coeff (x : CoeffIndex) : ℂ :=
    LinearMap.toMatrix (b x.1) (b x.1) ((V x.1).ρ x.2.1) x.2.2.1 x.2.2.2
  let coeffA (x : CoeffIndex) : algebraicClosure ℚ ℂ :=
    ⟨coeff x, mem_algebraicClosure_iff.mpr (hb x.1 x.2.1 x.2.2.1 x.2.2.2)⟩
  let s : Set (algebraicClosure ℚ ℂ) := Set.range coeffA
  let L : FiniteGaloisIntermediateField ℚ (algebraicClosure ℚ ℂ) :=
    FiniteGaloisIntermediateField.adjoin ℚ s
  let K : IntermediateField ℚ ℂ :=
    L.toIntermediateField.map (algebraicClosure ℚ ℂ).val
  have hfin : FiniteDimensional ℚ K :=
    LinearEquiv.finiteDimensional
      (IntermediateField.equivMap L.toIntermediateField
        (algebraicClosure ℚ ℂ).val).toLinearEquiv
  have hgal : IsGalois ℚ K :=
    IsGalois.of_algEquiv (IntermediateField.equivMap L.toIntermediateField
      (algebraicClosure ℚ ℂ).val)
  refine ⟨K, hfin, hgal, fun i => ⟨b i, fun g p q => ?_⟩⟩
  change coeff ⟨i, g, p, q⟩ ∈
    L.toIntermediateField.map (algebraicClosure ℚ ℂ).val
  rw [IntermediateField.mem_map]
  refine ⟨coeffA ⟨i, g, p, q⟩, ?_, rfl⟩
  exact FiniteGaloisIntermediateField.subset_adjoin ℚ s ⟨_, rfl⟩

/-- The one-representation specialization of `exists_common_finite_galois_matrix_field`. -/
theorem exists_finite_galois_matrix_field (V : FDRep ℂ G)
    [Fintype G] (hV : HasAlgebraicMatrixBasis V) :
    ∃ K : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ MatrixDefinedOver K V := by
  simpa using exists_common_finite_galois_matrix_field (I := Fin 1) (fun _ => V) (fun _ => hV)

/-! ### Algebraic Wedderburn models and simultaneous descent -/

/-- The algebraic closure of `ℚ` inside `ℂ`. -/
abbrev Qbar : Type := algebraicClosure ℚ ℂ

noncomputable local instance : IsAlgClosure ℚ Qbar :=
  algebraicClosure.isAlgClosure ℚ ℂ

noncomputable local instance : IsAlgClosed Qbar :=
  IsAlgClosure.isAlgClosed (R := ℚ)

local instance qbarNatCardNeZero (H : Type) [Group H] [Fintype H] :
    NeZero (Nat.card H : Qbar) :=
  ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := H)).ne'⟩

local instance complexNatCardNeZero (H : Type) [Group H] [Fintype H] :
    NeZero (Nat.card H : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := H)).ne'⟩

/-- A Wedderburn decomposition of `ℚ̄[G]`. -/
noncomputable def algebraicIrrepDecomp (H : Type) [Group H] [Fintype H] :
    IrrepDecomp Qbar H := by
  exact IrrepDecomp.mk'

/-- The group homomorphism obtained by embedding every matrix entry of the algebraic
Wedderburn decomposition into `ℂ`. -/
noncomputable def mappedWedderburnGroupHom (H : Type) [Group H] [Fintype H] :
    H →* (∀ i : Fin (algebraicIrrepDecomp H).n,
      Matrix (Fin ((algebraicIrrepDecomp H).d i))
        (Fin ((algebraicIrrepDecomp H).d i)) ℂ) where
  toFun g i := ((algebraicIrrepDecomp H).iso (MonoidAlgebra.of Qbar H g) i).map
    (algebraicClosure ℚ ℂ).val
  map_one' := by
    funext i
    change ((algebraicIrrepDecomp H).iso (MonoidAlgebra.of Qbar H 1) i).map
      (algebraicClosure ℚ ℂ).val = 1
    rw [map_one, map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  map_mul' g h := by
    funext i
    rw [map_mul, map_mul]
    change ((((algebraicIrrepDecomp H).iso (MonoidAlgebra.of Qbar H g)) i) *
      (((algebraicIrrepDecomp H).iso (MonoidAlgebra.of Qbar H h)) i)).map
        (algebraicClosure ℚ ℂ).val = _
    rw [Matrix.map_mul]
    rfl

/-- The complex group-algebra map induced by `mappedWedderburnGroupHom`. -/
noncomputable def mappedWedderburnHom (H : Type) [Group H] [Fintype H] :
    MonoidAlgebra ℂ H →ₐ[ℂ] (∀ i : Fin (algebraicIrrepDecomp H).n,
      Matrix (Fin ((algebraicIrrepDecomp H).d i))
        (Fin ((algebraicIrrepDecomp H).d i)) ℂ) :=
  (MonoidAlgebra.lift ℂ _ H) (mappedWedderburnGroupHom H)

theorem mappedWedderburnHom_mapRange {H : Type} [Group H] [Fintype H]
    (a : MonoidAlgebra Qbar H) (i : Fin (algebraicIrrepDecomp H).n)
    (p q : Fin ((algebraicIrrepDecomp H).d i)) :
    mappedWedderburnHom H
        ((MonoidAlgebra.mapAlgHom H (Algebra.ofId Qbar ℂ)) a) i p q =
      ((algebraicIrrepDecomp H).iso a i p q : Qbar) := by
  induction a using MonoidAlgebra.induction_on with
  | hM g => simp [mappedWedderburnHom, mappedWedderburnGroupHom]
  | hadd a b ha hb => simp [map_add, ha, hb]
  | hsmul r a ha =>
      simp only [map_smul]
      change mappedWedderburnHom H
          ((r : ℂ) • (MonoidAlgebra.mapAlgHom H (Algebra.ofId Qbar ℂ)) a) i p q = _
      rw [map_smul, Pi.smul_apply, Matrix.smul_apply, ha]
      rfl

/-- Entrywise scalar extension from algebraic to complex square matrices. -/
noncomputable def matrixScalarExtension (n : ℕ) :
    ℂ ⊗[Qbar] Matrix (Fin n) (Fin n) Qbar ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (TensorProduct.piRight Qbar ℂ ℂ (fun _ : Fin n => Fin n → Qbar)).trans
    (LinearEquiv.piCongrRight (fun _ : Fin n =>
      TensorProduct.piScalarRight Qbar ℂ ℂ (Fin n)))

theorem matrixScalarExtension_one_tmul (n : ℕ)
    (M : Matrix (Fin n) (Fin n) Qbar) (p q : Fin n) :
    matrixScalarExtension n (1 ⊗ₜ[Qbar] M) p q = (M p q : Qbar) := by
  change (M p q : ℂ) * 1 = (M p q : ℂ)
  exact mul_one _

/-- Scalar extension commutes with the finite product of Wedderburn matrix blocks. -/
noncomputable def productMatrixScalarExtension {n : ℕ} (d : Fin n → ℕ) :
    ℂ ⊗[Qbar] (∀ i, Matrix (Fin (d i)) (Fin (d i)) Qbar) ≃ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  (TensorProduct.piRight Qbar ℂ ℂ
    (fun i : Fin n => Matrix (Fin (d i)) (Fin (d i)) Qbar)).trans
      (LinearEquiv.piCongrRight (fun i => matrixScalarExtension (d i)))

/-- The underlying linear equivalence of the mapped algebraic Wedderburn decomposition. -/
noncomputable def mappedWedderburnLinearEquiv (H : Type) [Group H] [Fintype H] :
    MonoidAlgebra ℂ H ≃ₗ[ℂ] (∀ i : Fin (algebraicIrrepDecomp H).n,
      Matrix (Fin ((algebraicIrrepDecomp H).d i))
        (Fin ((algebraicIrrepDecomp H).d i)) ℂ) :=
  (groupAlgebraScalarTensorEquiv Qbar ℂ H).symm.toLinearEquiv ≪≫ₗ
    (algebraicIrrepDecomp H).iso.toLinearEquiv.baseChange Qbar ℂ _ _ ≪≫ₗ
    productMatrixScalarExtension (algebraicIrrepDecomp H).d

theorem mappedWedderburnLinearEquiv_of {H : Type} [Group H] [Fintype H]
    (g : H) (i : Fin (algebraicIrrepDecomp H).n)
    (p q : Fin ((algebraicIrrepDecomp H).d i)) :
    mappedWedderburnLinearEquiv H (MonoidAlgebra.of ℂ H g) i p q =
      ((algebraicIrrepDecomp H).iso (MonoidAlgebra.of Qbar H g) i p q : Qbar) := by
  simp [mappedWedderburnLinearEquiv, productMatrixScalarExtension,
    groupAlgebraScalarTensorEquiv]
  exact matrixScalarExtension_one_tmul _ _ _ _

theorem mappedWedderburnHom_eq_linearEquiv {H : Type} [Group H] [Fintype H] :
    (mappedWedderburnHom H).toLinearMap = (mappedWedderburnLinearEquiv H).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
      ext i p q
      calc
        (mappedWedderburnHom H).toLinearMap (MonoidAlgebra.of ℂ H g) i p q =
            ((algebraicIrrepDecomp H).iso
              (MonoidAlgebra.of Qbar H g) i p q : Qbar) := by
              simp [mappedWedderburnHom, mappedWedderburnGroupHom]
        _ = (mappedWedderburnLinearEquiv H).toLinearMap
            (MonoidAlgebra.of ℂ H g) i p q := mappedWedderburnLinearEquiv_of g i p q |>.symm
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul c x hx => simp only [map_smul, hx]

/-- The complex irreducible decomposition obtained by scalar-extending the algebraic one. -/
noncomputable def mappedIrrepDecomp (H : Type) [Group H] [Fintype H] : IrrepDecomp ℂ H := by
  refine ⟨(algebraicIrrepDecomp H).n, (algebraicIrrepDecomp H).d,
    (algebraicIrrepDecomp H).d_pos, AlgEquiv.ofBijective (mappedWedderburnHom H) ?_⟩
  have heq : ∀ x, mappedWedderburnHom H x = mappedWedderburnLinearEquiv H x :=
    fun x => LinearMap.congr_fun mappedWedderburnHom_eq_linearEquiv x
  constructor
  · intro x y hxy
    apply (mappedWedderburnLinearEquiv H).injective
    rw [← heq x, ← heq y, hxy]
  · intro y
    obtain ⟨x, hx⟩ := (mappedWedderburnLinearEquiv H).surjective y
    exact ⟨x, (heq x).trans hx⟩

/-- Every column representation in the mapped Wedderburn decomposition has algebraic matrices
in its standard basis. -/
theorem mappedColumn_hasAlgebraicMatrixBasis {H : Type} [Group H] [Fintype H]
    (i : Fin (mappedIrrepDecomp H).n) :
    HasAlgebraicMatrixBasis ((mappedIrrepDecomp H).columnFDRep i) := by
  let D := mappedIrrepDecomp H
  let b : Module.Basis (Fin (D.d i)) ℂ (D.columnFDRep i) := by
    change Module.Basis (Fin (D.d i)) ℂ (Fin (D.d i) → ℂ)
    exact Pi.basisFun ℂ (Fin (D.d i))
  apply hasAlgebraicMatrixBasis_of_basis b
  intro g p q
  have hmat : LinearMap.toMatrix b b ((D.columnFDRep i).ρ g) =
      D.projRingHom i (MonoidAlgebra.of ℂ H g) := by
    change LinearMap.toMatrixAlgEquiv'
      (Matrix.toLinAlgEquiv' (D.projRingHom i (MonoidAlgebra.of ℂ H g))) = _
    rw [LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
  rw [hmat]
  have hentry : D.projRingHom i (MonoidAlgebra.of ℂ H g) p q =
      (((algebraicIrrepDecomp H).iso
        (MonoidAlgebra.of Qbar H g) i p q : Qbar) : ℂ) := by
    change mappedWedderburnHom H (MonoidAlgebra.of ℂ H g) i p q = _
    simp [mappedWedderburnHom, mappedWedderburnGroupHom]
  rw [hentry]
  exact mem_algebraicClosure_iff.mp
    ((algebraicIrrepDecomp H).iso (MonoidAlgebra.of Qbar H g) i p q).2

/-- Every finite-dimensional complex representation of a finite group has an algebraic matrix
basis. -/
theorem all_hasAlgebraicMatrixBasis [Fintype G] (V : FDRep ℂ G) :
    HasAlgebraicMatrixBasis V := by
  let D := mappedIrrepDecomp G
  exact hasAlgebraicMatrixBasis_of_complete_simple_family D.columnFDRep
    D.columnFDRep_simple D.columnFDRep_injective D.columnFDRep_surjective
    mappedColumn_hasAlgebraicMatrixBasis V

/-- **Problem 5.2.7(a).** A single finite Galois extension of `ℚ` contains matrix entries
for every finite-dimensional complex representation of a finite group. -/
theorem exists_finite_galois_field_of_definition [Fintype G] :
    ∃ K : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧
        ∀ V : FDRep ℂ G, MatrixDefinedOver K V := by
  let D := mappedIrrepDecomp G
  obtain ⟨K, hfd, hgal, hK⟩ :=
    exists_common_finite_galois_matrix_field D.columnFDRep
      mappedColumn_hasAlgebraicMatrixBasis
  refine ⟨K, hfd, hgal, ?_⟩
  exact matrixDefinedOver_of_complete_simple_family D.columnFDRep
    D.columnFDRep_simple D.columnFDRep_injective D.columnFDRep_surjective hK

variable [Fintype G] [DecidableEq G]

/-- Each character factor is the squared modulus: `χ_V(g)·χ_V(g⁻¹) = |χ_V(g)|²`, using
`χ_V(g⁻¹) = conj χ_V(g)` (`Etingof.char_inv_eq_conj`) and `z·conj z = |z|²`. -/
private theorem char_mul_inv_eq_normSq (V : FDRep ℂ G) (g : G) :
    V.character g * V.character g⁻¹ = ((Complex.normSq (V.character g) : ℝ) : ℂ) := by
  rw [Etingof.char_inv_eq_conj V g, Complex.mul_conj]

/-- **Orthonormality sum.** For an irreducible complex representation `V` of a finite
group `G`, `∑_{g} χ_V(g)·χ_V(g⁻¹) = |G|`. This is the first orthogonality relation
`FDRep.char_orthonormal V V` (the `V ≅ V` case), cleared of its `⅟|G|` normalization. -/
theorem sum_char_mul_inv_eq_card (V : FDRep ℂ G) [Simple V]
    [Invertible (Fintype.card G : ℂ)] :
    ∑ g : G, V.character g * V.character g⁻¹ = (Fintype.card G : ℂ) := by
  have horth := FDRep.char_orthonormal_fintype V V
  rw [if_pos ⟨Iso.refl V⟩, smul_eq_mul] at horth
  -- `⅟|G| * S = 1`, so multiplying by `|G|` gives `S = |G|`.
  have h2 : (Fintype.card G : ℂ) * (⅟(Fintype.card G : ℂ) *
      ∑ g : G, V.character g * V.character g⁻¹) = (Fintype.card G : ℂ) * 1 := by rw [horth]
  rwa [← mul_assoc, mul_invOf_self, one_mul, mul_one] at h2

/-- **The `0 < β < 1` bound (Problem 5.2.7(b), main argument).** Let `V` be an
irreducible complex representation of a finite group `G` with `dim V > 1`, and suppose
`χ_V(g) ≠ 0` for every `g` (the hint's contradiction hypothesis). Then the product
`β = ∏_{g ≠ 1} |χ_V(g)|²` satisfies `0 < β < 1`.

Here `β` is the real product of squared moduli; it maps to
`∏_{g ≠ 1} χ_V(g)·χ_V(g⁻¹)` under `ℝ → ℂ` via `char_mul_inv_eq_normSq`. -/
theorem beta_lt_one (V : FDRep ℂ G) [Simple V] (h : 1 < Module.finrank ℂ V)
    (hne : ∀ g : G, V.character g ≠ 0) :
    0 < ∏ g ∈ univ.filter (· ≠ 1), Complex.normSq (V.character g) ∧
      ∏ g ∈ univ.filter (· ≠ 1), Complex.normSq (V.character g) < 1 := by
  haveI : Nonempty G := ⟨1⟩
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero (α := G))
  set s : Finset G := univ.filter (· ≠ 1) with hs_def
  have hs_erase : s = univ.erase 1 := Finset.filter_ne' univ 1
  -- `dim V ≥ 2`, as a real number.
  have hfrn : 2 ≤ Module.finrank ℂ V := h
  have hfr : (2 : ℝ) ≤ (Module.finrank ℂ V : ℝ) := by exact_mod_cast hfrn
  -- `∑_{g} |χ_V(g)|² = |G|`, as a real identity.
  have hsumreal : ∑ g : G, Complex.normSq (V.character g) = (Fintype.card G : ℝ) := by
    have hC : (↑(∑ g : G, Complex.normSq (V.character g)) : ℂ) = (Fintype.card G : ℂ) := by
      rw [Complex.ofReal_sum]
      rw [Finset.sum_congr rfl (fun g _ => (char_mul_inv_eq_normSq V g).symm)]
      exact sum_char_mul_inv_eq_card V
    exact_mod_cast hC
  -- `|χ_V(1)|² = (dim V)²`.
  have h1 : Complex.normSq (V.character (1 : G)) = (Module.finrank ℂ V : ℝ) ^ 2 := by
    rw [FDRep.char_one, Complex.normSq_natCast]; ring
  -- `∑_{g ≠ 1} |χ_V(g)|² = |G| - (dim V)²`.
  have hSs : ∑ g ∈ s, Complex.normSq (V.character g)
      = (Fintype.card G : ℝ) - (Module.finrank ℂ V : ℝ) ^ 2 := by
    have hsplit := Finset.add_sum_erase univ
      (fun g => Complex.normSq (V.character g)) (Finset.mem_univ (1 : G))
    rw [hs_erase]
    have hrw : ∑ g ∈ univ.erase 1, Complex.normSq (V.character g)
        = (∑ g : G, Complex.normSq (V.character g)) - Complex.normSq (V.character 1) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hsplit)
    rw [hrw, hsumreal, h1]
  -- `|G| ≥ 4` (since `∑ |χ|² = |G| ≥ |χ_V(1)|² = (dim V)² ≥ 4`).
  have hcardge : (4 : ℝ) ≤ (Fintype.card G : ℝ) := by
    rw [← hsumreal]
    calc (4 : ℝ) ≤ (Module.finrank ℂ V : ℝ) ^ 2 := by nlinarith [hfr]
      _ = Complex.normSq (V.character 1) := h1.symm
      _ ≤ ∑ g : G, Complex.normSq (V.character g) :=
          Finset.single_le_sum (fun g _ => Complex.normSq_nonneg _) (Finset.mem_univ 1)
  -- `s.card = |G| - 1 > 0`.
  have hcard_real : (s.card : ℝ) = (Fintype.card G : ℝ) - 1 := by
    rw [hs_erase, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hcardpos : 0 < s.card := by
    have : (0 : ℝ) < (s.card : ℝ) := by rw [hcard_real]; linarith
    exact_mod_cast this
  -- Each factor is positive, hence so is the product.
  have hβpos : 0 < ∏ g ∈ s, Complex.normSq (V.character g) :=
    Finset.prod_pos (fun g _ => Complex.normSq_pos.mpr (hne g))
  refine ⟨hβpos, ?_⟩
  -- The sum over `s` is strictly below the number of terms.
  have hlt : ∑ g ∈ s, Complex.normSq (V.character g) < (s.card : ℝ) := by
    rw [hSs, hcard_real]; nlinarith [hfr]
  -- AM-GM with all weights `1`.
  have hgm := Real.geom_mean_le_arith_mean s (fun _ => (1 : ℝ))
    (fun g => Complex.normSq (V.character g)) (fun i _ => zero_le_one)
    (by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hcardpos)
    (fun i _ => Complex.normSq_nonneg _)
  simp only [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at hgm
  -- `β ^ (1/card) ≤ (∑)/card < 1`, hence `β < 1`.
  have hrhs : (∑ g ∈ s, Complex.normSq (V.character g)) / (s.card : ℝ) < 1 := by
    rw [div_lt_one (by exact_mod_cast hcardpos)]; exact hlt
  have hβt : (∏ g ∈ s, Complex.normSq (V.character g)) ^ ((s.card : ℝ)⁻¹) < 1 :=
    lt_of_le_of_lt hgm hrhs
  by_contra hge
  push Not at hge
  have : 1 ≤ (∏ g ∈ s, Complex.normSq (V.character g)) ^ ((s.card : ℝ)⁻¹) :=
    Real.one_le_rpow hge (by positivity)
  linarith

/-- **Problem 5.2.7(b).** If `V` is an irreducible complex representation of a finite
group `G` with `dim V > 1`, then `χ_V(g) = 0` for some `g ∈ G`.

Assume not: `χ_V(g) ≠ 0` for all `g`. Then `β = ∏_{g ≠ 1} χ_V(g)·χ_V(g⁻¹)` is rational
(`Etingof.Remark5_2_8.character_prod_rat`) with value `q : ℚ`, and its real form
`∏_{g ≠ 1} |χ_V(g)|²` satisfies `0 < β < 1` (`beta_lt_one`), so `0 < q < 1`. As `β` is
also an algebraic integer, `Etingof.Remark5_2_8.beta_rat_not_mem_Ioo` yields `False`. -/
theorem exists_character_eq_zero (V : FDRep ℂ G) [Simple V]
    (h : 1 < Module.finrank ℂ V) : ∃ g : G, V.character g = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hβpos, hβlt⟩ := beta_lt_one V h hcon
  set s : Finset G := univ.filter (· ≠ 1) with hs_def
  obtain ⟨q, hq⟩ := Etingof.Remark5_2_8.character_prod_rat V
  rw [← hs_def] at hq
  -- `algebraMap ℚ ℂ q = ↑q` as a real, matched against the real product `β`.
  have hqcast : algebraMap ℚ ℂ q = ((q : ℝ) : ℂ) := by
    rw [Complex.ofReal_ratCast]; simp
  have hβeq : (q : ℝ) = ∏ g ∈ s, Complex.normSq (V.character g) := by
    have hC : ((q : ℝ) : ℂ) = ∏ g ∈ s, ((Complex.normSq (V.character g) : ℝ) : ℂ) := by
      rw [← hqcast, hq]
      exact Finset.prod_congr rfl (fun g _ => char_mul_inv_eq_normSq V g)
    rw [← Complex.ofReal_prod] at hC
    exact_mod_cast hC
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (q : ℝ) := by rw [hβeq]; exact hβpos
    exact_mod_cast this
  have hq1 : q < 1 := by
    have : (q : ℝ) < 1 := by rw [hβeq]; exact hβlt
    exact_mod_cast this
  exact Etingof.Remark5_2_8.beta_rat_not_mem_Ioo V (hs_def ▸ hq) hq0 hq1

end Etingof.Problem5_2_7

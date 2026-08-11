import EtingofRepresentationTheory.Chapter9.SemisimpleQuotientMatrixForm
import EtingofRepresentationTheory.Chapter9.MoritaStructural
import EtingofRepresentationTheory.Chapter9.ProjectiveCoverDelta
import EtingofRepresentationTheory.Infrastructure.SimpleModuleFamily

universe u v w

/-!
# The Wedderburn sizes of the Cartan algebras

This file identifies the matrix sizes in the semisimple quotient of
`B_n = End(⊕_i n_i P_i)ᵐᵒᵖ`.  The assembly theorem is stated for a family `P_i` of projective
covers of a complete family of simples `S_i`, encoded by the characteristic delta-Hom formula.
-/

open CategoryTheory CategoryTheory.Limits Module

namespace Etingof

private lemma simple_of_functor_obj' {C : Type u} {D : Type v}
    [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms]
    (X : C) [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f _ := by
    constructor
    · intro _ h
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

private lemma simple_of_equivalence' {C : Type u} {D : Type v}
    [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (E : C ≌ D) (X : C) [Simple X] : Simple (E.functor.obj X) := by
  haveI : Simple ((𝟭 C).obj X) := inferInstanceAs (Simple X)
  haveI : Simple (E.inverse.obj (E.functor.obj X)) := Simple.of_iso (E.unitIso.app X).symm
  exact simple_of_functor_obj' E.inverse (E.functor.obj X)

section LinearBiproduct

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasFiniteBiproducts C]
variable {J : Type*} [Fintype J] (f : J → C) (Y : C)

/-- A map out of a finite biproduct is determined linearly by its restrictions to the
summands. -/
noncomputable def biproductSourceHomLinearEquiv :
    (⨁ f ⟶ Y) ≃ₗ[k] ∀ j, (f j ⟶ Y) where
  toFun g j := biproduct.ι f j ≫ g
  invFun g := biproduct.desc g
  map_add' g h := by
    funext j
    simp [Preadditive.comp_add]
  map_smul' r g := by
    funext j
    simp [Linear.comp_smul]
  left_inv g := by
    apply biproduct.hom_ext'
    intro j
    simp
  right_inv g := by
    funext j
    simp

end LinearBiproduct

section CartanSizes

variable {k : Type w} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C] [Linear k C]
  [IsFiniteAbelianCategoryOverField k C] [HasFiniteBiproducts C]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

omit [IsAlgClosed k] in
/-- The Hom-space dimension from the multiplicity projective generator to its indexed simple
is the corresponding multiplicity. -/
theorem finrank_multBiproduct_hom_simple (P S : ι → C) (n : ι → ℕ)
    (hdelta : ∀ i j, finrank k (P i ⟶ S j) = if i = j then 1 else 0) (j : ι) :
    finrank k (multBiproduct P n ⟶ S j) = n j := by
  haveI : ∀ p : Σ i, Fin (n i), FiniteDimensional k (P p.1 ⟶ S j) := fun p =>
    IsFiniteAbelianCategoryOverField.finiteDimensional_hom (P p.1) (S j)
  unfold multBiproduct
  rw [(biproductSourceHomLinearEquiv (fun p : Σ i, Fin (n i) => P p.1) (S j)
    (k := k)).finrank_eq, Module.finrank_pi_fintype k]
  simp_rw [hdelta]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

/-- **The indexed Wedderburn form of `B_n`.** If `P_i` are projective covers of a complete,
irredundant family of simples `S_i`, expressed by
`dim_k Hom(P_i,S_j) = δ_ij`, then

`B_n / Rad(B_n) ≃ₐ[k] ∏_i Mat_{n_i}(k)`.

The proof uses the Morita equivalence `Hom(P_n,-)`. It sends `S_i` to a complete irredundant
family of simple `B_n`-modules, whose dimensions are `n_i` by the preceding biproduct
calculation. Theorem 3.5.4 applied to this particular family then gives exactly the claimed
indexing and sizes. -/
theorem matrix_structure_cartanAlgebra_of_hom_delta (P S : ι → C)
    (hproj : ∀ i, Projective (P i)) [IsProgenerator (⨁ P)]
    (hsimple : ∀ i, Simple (S i))
    (hdistinct : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hcomplete : ∀ X : C, Simple X → ∃ i, Nonempty (X ≅ S i))
    (hdelta : ∀ i j, finrank k (P i ⟶ S j) = if i = j then 1 else 0)
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    Nonempty ((((End (multBiproduct P n))ᵐᵒᵖ) ⧸
        Etingof.Radical ((End (multBiproduct P n))ᵐᵒᵖ)) ≃ₐ[k]
      ∀ i, Matrix (Fin (n i)) (Fin (n i)) k) := by
  classical
  let Q := multBiproduct P n
  let B := (End Q)ᵐᵒᵖ
  haveI : ∀ i, Projective (P i) := hproj
  letI : IsProgenerator Q := isProgenerator_multBiproduct P n hn
  haveI : FiniteDimensional k B := finiteDimensional_endOp Q
  haveI : IsNoetherianRing B := isNoetherianRing_endOp_of_overField (k := k) Q
  letI := Theorem_9_6_4 (k := k) (P := Q)
  let E : C ≌ FGModuleCat.{v} B :=
    IsProgenerator.preadditiveCoyonedaObjFG.asEquivalence
  let V : ι → Type v := fun i => Q ⟶ S i
  haveI hVfiniteB : ∀ i, Module.Finite B (V i) := fun i =>
    IsProgenerator.finite_hom_module (S i)
  haveI hVfiniteK : ∀ i, FiniteDimensional k (V i) := fun i =>
    IsFiniteAbelianCategoryOverField.finiteDimensional_hom Q (S i)
  haveI hVsimple : ∀ i, IsSimpleModule B (V i) := by
    intro i
    haveI : Simple (S i) := hsimple i
    haveI : Simple (E.functor.obj (S i)) := simple_of_equivalence' E (S i)
    change IsSimpleModule B (E.functor.obj (S i))
    exact isSimpleModule_of_simple_fgModuleCat (E.functor.obj (S i))
  have hnoniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[B] V j) := by
    intro i j hij
    refine ⟨fun e => hij (hdistinct i j ?_)⟩
    have eFG : E.functor.obj (S i) ≅ E.functor.obj (S j) := by
      exact e.toFGModuleCatIso
    exact ⟨E.unitIso.app (S i) ≪≫ E.inverse.mapIso eFG ≪≫
      (E.unitIso.app (S j)).symm⟩
  have hcompleteV : ∀ (W : Type v) [AddCommGroup W] [Module k W] [Module B W]
      [IsScalarTower k B W] [FiniteDimensional k W] [IsSimpleModule B W],
      ∃ i, Nonempty (W ≃ₗ[B] V i) := by
    intro W _ _ _ _ _ _
    letI : Module.Finite B W := Module.Finite.of_restrictScalars_finite k B W
    let X : FGModuleCat.{v} B := FGModuleCat.of B W
    haveI : Simple X := simple_fgModuleCat_of_isSimpleModule W
    haveI : Simple (E.inverse.obj X) := simple_of_equivalence' E.symm X
    obtain ⟨i, ⟨e⟩⟩ := hcomplete (E.inverse.obj X) inferInstance
    refine ⟨i, ⟨?_⟩⟩
    exact FGModuleCat.isoToLinearEquiv ((E.counitIso.app X).symm ≪≫ E.functor.mapIso e)
  letI : ∀ i, IsScalarTower k B (V i) := fun i => by
    dsimp [V, E]
    set_option backward.isDefEq.respectTransparency false in
      constructor
      intro c b f
      change ((c • b).unop ≫ f) = c • (b.unop ≫ f)
      rw [Algebra.smul_def, MulOpposite.unop_mul, End.mul_def]
      change (((c • 𝟙 Q) ≫ b.unop) ≫ f) = c • (b.unop ≫ f)
      simp
  obtain ⟨e⟩ := structure_mod_radical k B ι V hnoniso hcompleteV
  have hdim : ∀ i, finrank k (V i) = n i := by
    intro i
    change finrank k (Q ⟶ S i) = n i
    exact finrank_multBiproduct_hom_simple P S n hdelta i
  let b : ∀ i, Module.Basis (Fin (n i)) k (V i) := fun i =>
    (Module.finBasis k (V i)).reindex
      (Fintype.equivOfCardEq (by simpa using hdim i))
  let toMat : ∀ i, Module.End k (V i) ≃ₐ[k]
      Matrix (Fin (n i)) (Fin (n i)) k := fun i =>
    LinearMap.toMatrixAlgEquiv (b i)
  exact ⟨e.trans (AlgEquiv.piCongrRight toMat)⟩

/-- The indexed matrix form immediately gives Etingof's criterion: `B_n` is basic exactly
when every multiplicity is one. -/
theorem isBasicAlgebra_cartanAlgebra_iff_of_hom_delta (P S : ι → C)
    (hproj : ∀ i, Projective (P i)) [IsProgenerator (⨁ P)]
    (hsimple : ∀ i, Simple (S i))
    (hdistinct : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hcomplete : ∀ X : C, Simple X → ∃ i, Nonempty (X ≅ S i))
    (hdelta : ∀ i j, finrank k (P i ⟶ S j) = if i = j then 1 else 0)
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    IsBasicAlgebra k ((End (multBiproduct P n))ᵐᵒᵖ) ↔ ∀ i, n i = 1 := by
  obtain ⟨e⟩ := matrix_structure_cartanAlgebra_of_hom_delta P S hproj hsimple hdistinct
    hcomplete hdelta n hn
  exact isBasicAlgebra_iff_of_matrixForm k ((End (multBiproduct P n))ᵐᵒᵖ) n hn e

omit [DecidableEq ι] in
/-- **The indexed Wedderburn form of `B_n`, without a separately supplied simple family.**
An irredundant family of indecomposable projectives whose biproduct is a progenerator determines
its complete irredundant family of simple tops.  Consequently the matrix blocks of the genuine
semisimple quotient of `B_n` are indexed by `ι`, and their sizes are exactly the multiplicities
`n i`. -/
theorem matrix_structure_cartanAlgebra (P : ι → C)
    (hproj : ∀ i, Projective (P i))
    (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    [IsProgenerator (⨁ P)] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    Nonempty ((((End (multBiproduct P n))ᵐᵒᵖ) ⧸
        Etingof.Radical ((End (multBiproduct P n))ᵐᵒᵖ)) ≃ₐ[k]
      ∀ i, Matrix (Fin (n i)) (Fin (n i)) k) := by
  classical
  obtain ⟨S, hsimple, hSdistinct, hcomplete, hdelta⟩ :=
    exists_simple_family_hom_delta (k := k) P hproj hindec hdistinct
  exact matrix_structure_cartanAlgebra_of_hom_delta P S hproj hsimple hSdistinct
    hcomplete hdelta n hn

omit [DecidableEq ι] in
/-- **Etingof's basic-algebra criterion for the Cartan family.** For an irredundant complete
family of indecomposable projectives, `B_n` is basic exactly when every multiplicity is one.
No simple family or delta-Hom formula is required as input: both are constructed by
`exists_simple_family_hom_delta`. -/
theorem isBasicAlgebra_cartanAlgebra_iff (P : ι → C)
    (hproj : ∀ i, Projective (P i))
    (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    [IsProgenerator (⨁ P)] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    IsBasicAlgebra k ((End (multBiproduct P n))ᵐᵒᵖ) ↔ ∀ i, n i = 1 := by
  classical
  obtain ⟨e⟩ := matrix_structure_cartanAlgebra (k := k) P hproj hindec hdistinct n hn
  exact isBasicAlgebra_iff_of_matrixForm k ((End (multBiproduct P n))ᵐᵒᵖ) n hn e

end CartanSizes

end Etingof

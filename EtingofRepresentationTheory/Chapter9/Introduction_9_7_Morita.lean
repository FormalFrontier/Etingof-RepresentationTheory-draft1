import EtingofRepresentationTheory.Chapter9.Introduction_9_7
import EtingofRepresentationTheory.Chapter9.Theorem9_6_4
import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import EtingofRepresentationTheory.Chapter2.Problem2_3_17
import EtingofRepresentationTheory.Infrastructure.FGModuleCatEnoughProjectives
import EtingofRepresentationTheory.Infrastructure.MoritaFGRestriction
import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Ring.Equiv

universe w u u' v

/-!
# §9.7 capstone: the `B_𝐧` enumerate the Morita class of `𝒞`

Etingof §9.7 closes the discussion of projective generators with the claim that ties
the family `B_𝐧 = End(P_𝐧)ᵒᵖ` to Morita equivalence:

> Defining `B_𝐧 = B_𝐧(𝒞) := End(P_𝐧)ᵒᵖ`, we see that the algebras `B_𝐧` are all the
> finite dimensional algebras whose category of finite dimensional modules is
> equivalent to `𝒞`.

and, in the Discussion after Definition 9.7.1, its global restatement:

> Thus, Morita equivalence classes of finite dimensional algebras are the collections
> of the form `{B_𝐧(𝒞), 𝐧 ∈ ℕᵐ}`.

This file formalizes both claims, building on three already-proven pieces:

* `Etingof.Theorem_9_6_4_corollary_of_isNoetherian`: for any progenerator `P` of a finite
  abelian category `𝒞` with `(End P)ᵐᵒᵖ` Noetherian, `𝒞 ≌ FGModuleCat (End P)ᵐᵒᵖ`. This is
  the ring-level Morita identification: the endomorphism algebra of a progenerator realizes
  `𝒞` as its module category. (The over-a-field headline is `Etingof.Theorem_9_6_4`.)
* `Etingof.progenerator_iff_multBiproduct`, the §9.7 classification: an object `Q` is
  a progenerator iff `Q ≅ P_𝐧 := ⊕ᵢ nᵢ Pᵢ` for some multiplicities `nᵢ ≥ 1`.
* `Etingof.isProgenerator_multBiproduct`: each `P_𝐧` with all `nᵢ ≥ 1` is a
  progenerator.

## What is proved here

The project's `IsFiniteAbelianCategory` is a ring-level abstraction (an abelian
category with enough projectives and finitely many simples; it carries no `k`-linear
structure), so `B_𝐧 = (End P_𝐧)ᵐᵒᵖ` is a ring and the comparisons below are ring
isomorphisms `≃+*` rather than `k`-algebra isomorphisms.

* `Etingof.Bn`: the algebra `B_𝐧(𝒞) = (End P_𝐧)ᵐᵒᵖ`.
* `Etingof.nonempty_equivalence_fgModuleCat_Bn`, each `B_𝐧` realizes `𝒞`:
  `𝒞 ≌ FGModuleCat (B_𝐧)` (the `⊇` of the book's claim).
* `Etingof.ringEquiv_endOp_iff_isBn` classifies endomorphism rings already presented by a
  progenerator.
* `Etingof.nonempty_fgModuleCat_equivalence_iff_isBn` supplies the missing Morita
  reconstruction from an arbitrary equivalence `FGModuleCat A ≌ 𝒞`, proving that these and
  only these rings are the `B_𝐧`.
* `Etingof.moritaEquivalentFmod_iff_isBn` is the Discussion's global restatement: the
  entire Morita class of any one positive `B_𝐧` is exactly the positive `B_𝐧` family.
* `Etingof.nonempty_fgModuleCat_equivalence_of_isBn` records the forward containment
  separately: any two positive `B_𝐧` have equivalent finitely generated module categories.
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Iso

variable {C : Type u} [Category.{v} C] [Preadditive C] {X Y : C}

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by an isomorphism `e : X ≅ Y` as a ring isomorphism of endomorphism
rings, `End X ≃+* End Y`, `f ↦ e.inv ≫ f ≫ e.hom`. This upgrades Mathlib's multiplicative
`Iso.conj` with additivity, which holds because composition is bilinear in a preadditive
category. -/
def conjRingEquiv (e : X ≅ Y) : End X ≃+* End Y :=
  { e.conj with
    map_add' := fun f g =>
      show e.inv ≫ (f + g) ≫ e.hom = e.inv ≫ f ≫ e.hom + e.inv ≫ g ≫ e.hom by
        rw [Preadditive.add_comp, Preadditive.comp_add] }

@[simp]
theorem conjRingEquiv_apply (e : X ≅ Y) (f : End X) :
    e.conjRingEquiv f = e.inv ≫ f ≫ e.hom := rfl

end CategoryTheory.Iso

namespace Etingof

variable {C : Type u} [Category.{v} C]

/-! ## Recovering a progenerator from a module-category equivalence -/

/-- The regular module, regarded as an object of the finitely generated module category. -/
noncomputable def fgModuleCatRegular (A : Type u) [Ring A] : FGModuleCat.{u} A :=
  FGModuleCat.of A A

/-- The regular module is a progenerator of `FGModuleCat A`: it is projective, and every
finitely generated module is a quotient of a finite-rank free module. -/
theorem fgModuleCatRegular_isProgenerator (A : Type u) [Ring A] :
    IsProgenerator (fgModuleCatRegular A) := by
  letI : HasFiniteBiproducts (FGModuleCat.{u} A) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  let R := fgModuleCatRegular A
  have hproj : Projective R :=
    FGModuleCat.projective_of_forget₂_projective
      (inferInstanceAs (Projective (ModuleCat.of A A)))
  refine { toProjective := hproj, epiFromBiproduct := fun X => ?_ }
  obtain ⟨n, l, hl⟩ := Module.Finite.exists_fin' (R := A) (M := X)
  let F : Fin n → FGModuleCat.{u} A := fun _ => R
  letI : PreservesBiproduct F (FGModuleCat.incl A) :=
    preservesBiproduct_of_preservesCoproduct (FGModuleCat.incl A)
  let free : FGModuleCat.{u} A := FGModuleCat.of A (Fin n → A)
  let eUnder : (FGModuleCat.incl A).obj free ≅
      (FGModuleCat.incl A).obj (⨁ F) :=
    (ModuleCat.biproductIsoPi (fun _ : Fin n => ModuleCat.of A A)).symm.trans
      ((FGModuleCat.incl A).mapBiproduct F).symm
  let e : free ≅ ⨁ F := (ModuleCat.isFG A).isoMk eUnder
  let f : (⨁ F) ⟶ X := e.inv ≫ FGModuleCat.ofHom l
  refine ⟨n, inferInstance, f, ?_⟩
  apply FGModuleCat.epi_of_forget₂_epi f
  rw [Functor.map_comp]
  haveI : Epi ((FGModuleCat.incl A).map (FGModuleCat.ofHom l)) :=
    (ModuleCat.epi_iff_surjective _).mpr hl
  exact epi_comp _ _

/-- An equivalence between preadditive categories with finite biproducts carries finite
progenerators to finite progenerators. -/
theorem IsProgenerator.map_equivalence
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    {D : Type u'} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    (E : C ≌ D) (P : C) (hP : IsProgenerator P) :
    IsProgenerator (E.functor.obj P) := by
  letI : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  letI : Functor.PreservesEpimorphisms E.functor :=
    Functor.preservesEpimorphisms_of_adjunction E.toAdjunction
  have hproj : Projective (E.functor.obj P) :=
    (E.map_projective_iff P).mpr hP.toProjective
  refine { toProjective := hproj, epiFromBiproduct := fun X => ?_ }
  obtain ⟨n, hbp, f, hf⟩ := hP.epiFromBiproduct (E.inverse.obj X)
  let F : Fin n → C := fun _ => P
  haveI : HasBiproduct F := hbp
  let g : (⨁ fun _ : Fin n => E.functor.obj P) ⟶ X :=
    (E.functor.mapBiproduct F).inv ≫ E.functor.map f ≫ (E.counitIso.app X).hom
  refine ⟨n, inferInstance, g, ?_⟩
  haveI : Epi f := hf
  haveI : Epi (E.functor.map f) := inferInstance
  have htail : Epi (E.functor.map f ≫ (E.counitIso.app X).hom) := epi_comp _ _
  haveI := htail
  exact epi_comp _ _

/-- Endomorphisms of the regular object in `FGModuleCat A` are the usual `A`-linear
endomorphisms of the left regular module. -/
noncomputable def fgModuleCatRegularEndRingEquiv (A : Type u) [Ring A] :
    End (fgModuleCatRegular A) ≃+* Module.End A A where
  toFun f := f.hom.hom
  invFun f := FGModuleCat.ofHom f
  left_inv f := by apply FGModuleCat.hom_ext; rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The opposite endomorphism ring of the regular object of `FGModuleCat A` recovers `A`.
This is the categorical form of `End_A(A) = Aᵒᵖ`. -/
noncomputable def ringEquiv_fgModuleCatRegularEndOp (A : Type u) [Ring A] :
    A ≃+* (End (fgModuleCatRegular A))ᵐᵒᵖ :=
  (((RingEquiv.op ((fgModuleCatRegularEndRingEquiv A).trans (EndSelfEquivOp A))).trans
    (RingEquiv.opOp A).symm)).symm

/-- A categorical equivalence between preadditive categories induces a ring isomorphism between
the endomorphism rings of an object and its image. -/
noncomputable def equivalenceEndRingEquiv
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    {D : Type u'} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    (E : C ≌ D) (X : C) : End X ≃+* End (E.functor.obj X) := by
  letI : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  exact { E.fullyFaithfulFunctor.mulEquivEnd X with
    map_add' := fun _ _ => E.functor.map_add }

/-- **`B_𝐧(𝒞) = End(P_𝐧)ᵒᵖ`** (Etingof §9.7): the (opposite of the) endomorphism ring of
the multiplicity biproduct `P_𝐧 = ⊕ᵢ nᵢ Pᵢ`. The opposite matches the convention of
Theorem 9.6.4, under which `𝒞 ≌ FGModuleCat (End P_𝐧)ᵐᵒᵖ`. -/
noncomputable abbrev Bn [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {ι : Type v} [Fintype ι] (P : ι → C) (n : ι → ℕ) : Type v :=
  (End (multBiproduct P n))ᵐᵒᵖ

variable [IsFiniteAbelianCategory C] [HasFiniteBiproducts C]
  {ι : Type v} [Fintype ι] (P : ι → C)

/-- **Each `B_𝐧` realizes `𝒞`** (the `⊇` direction of Etingof's §9.7 claim).

If every multiplicity `nᵢ ≥ 1`, then `P_𝐧` is a progenerator, so by Theorem 9.6.4 the
category `𝒞` is equivalent to the category of finitely generated `B_𝐧`-modules. -/
theorem nonempty_equivalence_fgModuleCat_Bn
    (hproj : ∀ i, Projective (P i)) [IsProgenerator (⨁ P)]
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) [IsNoetherianRing (Bn P n)] :
    Nonempty (C ≌ FGModuleCat.{v} (Bn P n)) := by
  haveI : ∀ i, Projective (P i) := hproj
  haveI : IsProgenerator (multBiproduct P n) := isProgenerator_multBiproduct P n hn
  exact Theorem_9_6_4_corollary_of_isNoetherian C (multBiproduct P n)

/-- **§9.7 capstone biconditional.** Let `P : ι → 𝒞` be the indecomposable projectives of
the finite abelian category `𝒞` (each indecomposable, pairwise non-isomorphic, exhausting
the indecomposable projectives, with `⨁ P` a progenerator). Then a ring `A` is isomorphic
to the endomorphism algebra `(End Q)ᵐᵒᵖ` of some progenerator `Q` of `𝒞` iff `A` is
isomorphic to some `B_𝐧` with all multiplicities `nᵢ ≥ 1`.

By Theorem 9.6.4 the left-hand condition is exactly "`A`'s category of finitely generated
modules is equivalent to `𝒞`". So this is Etingof's statement that the `B_𝐧` are precisely
the algebras whose module category is `𝒞`. -/
theorem ringEquiv_endOp_iff_isBn
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    [IsProgenerator (⨁ P)] (A : Type v) [Ring A] :
    (∃ Q : C, IsProgenerator Q ∧ Nonempty (A ≃+* (End Q)ᵐᵒᵖ)) ↔
      ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (A ≃+* Bn P n) := by
  haveI : ∀ i, Projective (P i) := hproj
  constructor
  · rintro ⟨Q, hQ, ⟨φ⟩⟩
    obtain ⟨n, hn, ⟨e⟩⟩ :=
      (progenerator_iff_multBiproduct P hproj hindec hdistinct hcomplete Q).mp hQ
    exact ⟨n, hn, ⟨φ.trans (RingEquiv.op e.conjRingEquiv)⟩⟩
  · rintro ⟨n, hn, ⟨φ⟩⟩
    haveI : IsProgenerator (multBiproduct P n) := isProgenerator_multBiproduct P n hn
    exact ⟨multBiproduct P n, inferInstance, ⟨φ⟩⟩

/-- **§9.7 capstone, stated for an arbitrary module-category equivalence.**

Let `C` be a finite abelian category over `k`, and let `P` enumerate its indecomposable
projectives. For any ring `A`, the category `FGModuleCat A` is equivalent to `C` if and only if
`A` is isomorphic to one of the rings `B_𝐧(C)`, with every multiplicity positive.

The forward implication is the Morita reconstruction missing from
`ringEquiv_endOp_iff_isBn`: transport the regular `A`-module across the supplied equivalence.
Its image is a progenerator `Q` of `C`, and full faithfulness identifies
`A ≃+* (End Q)ᵐᵒᵖ`; the projective-generator classification then identifies `Q` with
some `P_𝐧`. The reverse implication combines change of rings with Theorem 9.6.4.

The conclusion is deliberately a ring isomorphism. A bare categorical equivalence need not be
`k`-linear (it may twist scalars by a field automorphism), so a `k`-algebra isomorphism would
require a `k`-linear equivalence hypothesis. -/
theorem nonempty_fgModuleCat_equivalence_iff_isBn
    {k : Type w} [Field k] [Linear k C] [IsFiniteAbelianCategoryOverField k C]
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    [IsProgenerator (⨁ P)] (A : Type v) [Ring A] :
    Nonempty (FGModuleCat.{v} A ≌ C) ↔
      ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (A ≃+* Bn P n) := by
  letI : HasFiniteBiproducts (FGModuleCat.{v} A) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  constructor
  · rintro ⟨E⟩
    let R := fgModuleCatRegular A
    let Q := E.functor.obj R
    have hR : IsProgenerator R := fgModuleCatRegular_isProgenerator A
    have hQ : IsProgenerator Q := hR.map_equivalence E
    let endEquiv : End R ≃+* End Q := equivalenceEndRingEquiv E R
    let ringEquiv : A ≃+* (End Q)ᵐᵒᵖ :=
      (ringEquiv_fgModuleCatRegularEndOp A).trans (RingEquiv.op endEquiv)
    exact (ringEquiv_endOp_iff_isBn P hproj hindec hdistinct hcomplete A).mp
      ⟨Q, hQ, ⟨ringEquiv⟩⟩
  · rintro ⟨n, hn, ⟨e⟩⟩
    haveI : IsNoetherianRing (Bn P n) :=
      isNoetherianRing_endOp_of_overField (k := k) (multBiproduct P n)
    let full : ModuleCat.{v} A ≌ ModuleCat.{v} (Bn P n) :=
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm
    obtain ⟨fg⟩ :=
      MoritaEquivalent.fgModuleCatEquiv (⟨full⟩ : MoritaEquivalent A (Bn P n))
    obtain ⟨eC⟩ := nonempty_equivalence_fgModuleCat_Bn P hproj n hn
    exact ⟨fg.trans eC.symm⟩

/-- **Discussion after Definition 9.7.1: the whole Morita class is the `B_𝐧` family.**

Fix one positive multiplicity vector `n₀`. A ring `A` is Morita equivalent, in the book's
finitely generated-module sense, to `B_(n₀)` if and only if `A` is isomorphic to some
`B_𝐧(C)` with positive multiplicities. Thus the Morita equivalence class is exactly the
family advertised in the Discussion, not merely a family contained in one class. -/
theorem moritaEquivalentFmod_iff_isBn
    {k : Type w} [Field k] [Linear k C] [IsFiniteAbelianCategoryOverField k C]
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    [IsProgenerator (⨁ P)] (A : Type v) [Ring A]
    (n₀ : ι → ℕ) (hn₀ : ∀ i, 1 ≤ n₀ i) :
    MoritaEquivalentFmod A (Bn P n₀) ↔
      ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (A ≃+* Bn P n) := by
  haveI : IsNoetherianRing (Bn P n₀) :=
    isNoetherianRing_endOp_of_overField (k := k) (multBiproduct P n₀)
  obtain ⟨eC⟩ := nonempty_equivalence_fgModuleCat_Bn P hproj n₀ hn₀
  rw [MoritaEquivalentFmod]
  constructor
  · rintro ⟨e⟩
    exact (nonempty_fgModuleCat_equivalence_iff_isBn (k := k) P hproj hindec hdistinct
      hcomplete A).mp ⟨e.trans eC.symm⟩
  · intro h
    obtain ⟨e⟩ := (nonempty_fgModuleCat_equivalence_iff_isBn (k := k) P hproj hindec
      hdistinct hcomplete A).mpr h
    exact ⟨e.trans eC⟩

/-- **The positive `B_𝐧` all belong to one Morita class.**

Any two members `B_𝐧` and `B_𝐧'` of the family have equivalent module categories (both
are equivalent to `𝒞`), so they are Morita equivalent. The converse containment, which
says that every ring in this class is one of the `B_𝐧`, is `moritaEquivalentFmod_iff_isBn`. -/
theorem nonempty_fgModuleCat_equivalence_of_isBn
    (hproj : ∀ i, Projective (P i)) [IsProgenerator (⨁ P)]
    (n n' : ι → ℕ) (hn : ∀ i, 1 ≤ n i) (hn' : ∀ i, 1 ≤ n' i)
    [IsNoetherianRing (Bn P n)] [IsNoetherianRing (Bn P n')] :
    Nonempty (FGModuleCat.{v} (Bn P n) ≌ FGModuleCat.{v} (Bn P n')) := by
  obtain ⟨e⟩ := nonempty_equivalence_fgModuleCat_Bn P hproj n hn
  obtain ⟨e'⟩ := nonempty_equivalence_fgModuleCat_Bn P hproj n' hn'
  exact ⟨e.symm.trans e'⟩

end Etingof

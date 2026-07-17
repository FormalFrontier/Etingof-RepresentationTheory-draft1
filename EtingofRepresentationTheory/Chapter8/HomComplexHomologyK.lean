import EtingofRepresentationTheory.Chapter8.ExtCohomologyHomK
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Identifying the two `Hⁿ Hom(P•, N)` presentations

Both `Ext` notions used in Problem 8.2.8 (`Ext` half) compute `Extⁿ_A(M, N)` as the cohomology of
`Hom_A(P•, N)` for a projective resolution `P` of `M`, but through two different Mathlib
presentations of that cohomology that Mathlib does not identify:

* **Derived-category side** (feeds `CategoryTheory.Abelian.Ext`): the `AddCommGrp`-valued cochain
  complex `HomComplex P.cochainComplex ((singleFunctor (ModuleCat A) 0).obj N)`, an `ℤ`-indexed
  `CochainComplex AddCommGrp ℤ` whose degree-`i` term is `Cochain P.cochainComplex (single 0 N) i`.
* **Left-derived-functor side** (feeds `Etingof.Extₖ`): the `ModuleCat k`-valued cochain complex
  `P.complex.linearYonedaObj k N` (`ChainComplex.linearYonedaObj`), an `ℕ`-indexed
  `CochainComplex (ModuleCat k) ℕ` whose degree-`i` term is `Hom_A(P.complex.X i, N)`.

This file provides `Etingof.homComplexHomologyAddEquivₖ`, the additive isomorphism of the degree-`n`
homologies of these two complexes.

## Construction

The two complexes are degreewise "the same" `Hom(P•, N)`:

* `homDegEquiv i : Cochain P.cochainComplex (single 0 N) i ≃+ (P.complex.X i ⟶ N)` identifies the
  degree-`i` term of the `HomComplex` with the categorical hom `P.complex.X i ⟶ N` (which underlies
  the degree-`i` term `ModuleCat.of k (P.complex.X i ⟶ N)` of `linearYonedaObj`), via
  `Cochain.toSingleEquiv` and `ProjectiveResolution.cochainComplexXIso`.
* `homDegEquiv_δ` records the degreewise **sign twist**: the `HomComplex` differential `δ` becomes
  `(i+1).negOnePow •` precomposition with `P.complex.d (i+1) i`, whereas the `linearYonedaObj`
  differential is precomposition with no sign (`ChainComplex.linearYonedaObj_d`).

The category change `ModuleCat k → AddCommGrp` is handled by
`(forget₂ (ModuleCat k) Ab).PreservesHomology`.
-/

universe u

open CategoryTheory Limits CochainComplex.HomComplex

namespace Etingof

variable (k : Type u) [Field k]
variable {A : Type u} [Ring A] [Algebra k A]
variable {M : ModuleCat.{u} A} (N : ModuleCat.{u} A) (P : ProjectiveResolution M)

/-- Precomposition with an isomorphism, as an additive equivalence of hom-groups. -/
def isoPrecompHomEquiv {C : Type*} [Category C] [Preadditive C] {X X' Y : C} (α : X ≅ X') :
    (X ⟶ Y) ≃+ (X' ⟶ Y) where
  toFun f := α.inv ≫ f
  invFun g := α.hom ≫ g
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp only [Preadditive.comp_add]

@[simp] lemma isoPrecompHomEquiv_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y : C} (α : X ≅ X') (f : X ⟶ Y) :
    isoPrecompHomEquiv α f = α.inv ≫ f := rfl

@[simp] lemma isoPrecompHomEquiv_symm_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y : C} (α : X ≅ X') (g : X' ⟶ Y) :
    (isoPrecompHomEquiv α).symm g = α.hom ≫ g := rfl

/-- The `AddCommGrp`-valued `HomComplex` of the projective resolution into `N[0]`, whose degree-`n`
homology feeds the derived-category `Ext`. -/
noncomputable abbrev homCochainComplex : CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.HomComplex P.cochainComplex
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)

/-- The degree-`i` term of the `HomComplex` is the categorical hom `P.complex.X i ⟶ N`, via the
`toSingle` identification and the reindexing `P.cochainComplex.X (-i) ≅ P.complex.X i`. -/
noncomputable def homDegEquiv (i : ℕ) :
    Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) (i : ℤ)
      ≃+ (P.complex.X i ⟶ N) :=
  (Cochain.toSingleEquiv (K := P.cochainComplex) (X := N)
      (p := -(i : ℤ)) (q := 0) (n := (i : ℤ)) (by ring)).trans
    (isoPrecompHomEquiv (P.cochainComplexXIso (-(i : ℤ)) i (by ring)))

lemma homDegEquiv_apply (i : ℕ)
    (z : Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)
      (i : ℤ)) :
    homDegEquiv N P i z =
      (P.cochainComplexXIso (-(i : ℤ)) i (by ring)).inv ≫
        Cochain.toSingleEquiv (K := P.cochainComplex) (X := N)
          (p := -(i : ℤ)) (q := 0) (n := (i : ℤ)) (by ring) z := rfl

/-- The genuinely new content: under `homDegEquiv`, the `HomComplex` differential `δ i (i+1)`
becomes `(i+1).negOnePow •` precomposition with the resolution differential `P.complex.d (i+1) i`.
The `linearYonedaObj` differential is the same precomposition with no sign, so the two complexes
differ by a degreewise sign twist. -/
lemma homDegEquiv_δ (i : ℕ)
    (z : Cochain P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N)
      (i : ℤ)) :
    homDegEquiv N P (i + 1) (δ (i : ℤ) (↑(i + 1)) z) =
      ((↑(i + 1) : ℤ)).negOnePow • (P.complex.d (i + 1) i ≫ homDegEquiv N P i z) := by
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective z (-(i : ℤ)) (by ring)
  rw [homDegEquiv_apply, homDegEquiv_apply,
    Cochain.δ_toSingleMk g (by ring) (↑(i + 1)) (-(↑(i + 1) : ℤ)) (by ring),
    Units.smul_def, map_zsmul, Cochain.toSingleEquiv_toSingleMk, Cochain.toSingleEquiv_toSingleMk,
    ProjectiveResolution.cochainComplex_d P (-(↑(i + 1) : ℤ)) (-(i : ℤ)) (i + 1) i
      (by ring) (by ring)]
  -- LHS: `xiso'.inv ≫ (negOnePow • (xiso'.hom ≫ d ≫ xiso.inv ≫ g))`;
  -- RHS: `negOnePow • (d ≫ xiso.inv ≫ g)`. Move the sign out and cancel `xiso'.inv ≫ xiso'.hom`.
  simp only [Units.smul_def, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]

/-!
## Remaining assembly (follow-up)

The target of this file is the additive isomorphism

```
homComplexHomologyAddEquivₖ (n : ℕ) :
    (homCochainComplex N P).homology (n : ℤ) ≃+ (P.complex.linearYonedaObj k N).homology n
```

Write `L := homCochainComplex N P : CochainComplex AddCommGrp ℤ`,
`R := P.complex.linearYonedaObj k N : CochainComplex (ModuleCat k) ℕ`, and
`F := forget₂ (ModuleCat k) AddCommGrp` (which has `PreservesHomology`, from
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`). The reduction from the degreewise data above is:

* For `n = m + 1`: `homDegEquiv N P (m), homDegEquiv N P (m+1), homDegEquiv N P (m+2)` are the three
  vertical isomorphisms of a `ShortComplex.isoMk` between `L.sc (↑(m+1))` and `(R.sc (m+1)).map F`;
  the two commutativity squares are exactly `homDegEquiv_δ` (the sign is a unit, and precomposition
  with a unit does not change the square up to the isomorphisms). `R.d` on the target side is the
  unsigned precomposition `ChainComplex.linearYonedaObj_d`. Then
  `ShortComplex.homologyMapIso` + `ShortComplex.mapHomologyIso F (R.sc (m+1))` give
  `L.homology ↑(m+1) ≅ F.obj (R.homology (m+1))`.
* For `n = 0`: the incoming differentials vanish on both sides (`L.X (-1) ≅ 0`, and the source of
  `R.d` is `(ComplexShape.up ℕ).prev 0 = 0` with `R.d 0 0 = 0`), so both homologies are the kernel
  via `HomologicalComplex.isoHomologyπ`; `homDegEquiv N P 0` and `homDegEquiv N P 1` conjugate the
  two kernels (`homDegEquiv_δ` again, with the sign an isomorphism of the kernels).
* Finally `F.obj (R.homology n)` has the same underlying additive group as `R.homology n`
  (`ModuleCat`'s `forget₂` is the identity on carriers), giving the `≃+`.

This assembly is tracked as follow-up issue #6904.
-/

end Etingof

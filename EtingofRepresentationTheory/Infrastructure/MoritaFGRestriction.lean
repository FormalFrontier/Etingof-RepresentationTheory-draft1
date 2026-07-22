import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Finsupp.Span

/-!
# Morita equivalence restricts to finitely generated modules

A Morita equivalence `E : ModuleCat A ≌ ModuleCat B` (the definition underlying
`Etingof.MoritaEquivalent`) restricts to an equivalence of the finitely generated
module categories `FGModuleCat A ≌ FGModuleCat B`.

The crux is that an equivalence of module categories **preserves finite generation**:
`E.functor.obj M` is finitely generated over `B` iff `M` is finitely generated over `A`.
This is *not* a formal consequence of being an additive equivalence for a fixed module;
it rests on the fact that the regular module is a compact projective generator, whose
image under the equivalence is therefore again finitely generated.

## Main results

* `Etingof.inverse_regular_finite`: for `E : ModuleCat R ≌ ModuleCat S`, the object
  `E.inverse.obj (of S S)` is finitely generated over `R`. (The regular module of `S`
  is a separator, so its image `E.functor (of R R)` is a module-theoretic generator of
  `ModuleCat S`; a finite sub-family of maps already covers `S`, and applying `E.inverse`
  exhibits `E.inverse (of S S)` as a quotient of a finite power of `R`.)
* `Etingof.MoritaEquivalent.fgModuleCatEquiv`: `MoritaEquivalent A B` yields
  `Nonempty (FGModuleCat A ≌ FGModuleCat B)`.
-/

universe u

open CategoryTheory Limits

namespace Etingof

/-- The regular module `R` is a separator of `ModuleCat R`. -/
lemma isSeparator_regular (R : Type u) [Ring R] :
    IsSeparator (ModuleCat.of.{u} R R) := fun X Y f g h => by
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff,
    ModuleCat.hom_comp, LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply,
    forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom (LinearMap.toSpanSingleton R X x)) 1

/-- An additive functor between module categories sends a finite biproduct of objects with
finitely generated image to an object with finitely generated image. -/
lemma finite_functor_biproduct {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    {n : ℕ} (f : Fin n → ModuleCat.{u} R)
    (h : ∀ i, Module.Finite S (F.obj (f i))) :
    Module.Finite S (F.obj (⨁ f)) := by
  haveI : ∀ i, Module.Finite S ((F.obj ∘ f) i) := h
  -- `F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f) ≅ of S (∀ i, (F.obj ∘ f) i)`
  let e : F.obj (⨁ f) ≅ ModuleCat.of S (∀ i, (F.obj ∘ f) i) :=
    (F.mapBiproduct f).trans (ModuleCat.biproductIsoPi _)
  haveI : Module.Finite S (∀ i, (F.obj ∘ f) i) := inferInstance
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- **Core lemma.** For an equivalence `E : ModuleCat R ≌ ModuleCat S`, the image
`E.inverse.obj (of S S)` of the regular module is finitely generated over `R`. -/
lemma inverse_regular_finite {R S : Type u} [Ring R] [Ring S]
    (E : ModuleCat.{u} R ≌ ModuleCat.{u} S) :
    Module.Finite R (E.inverse.obj (ModuleCat.of.{u} S S)) := by
  haveI : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  haveI : E.inverse.Additive := Equivalence.inverse_additive E
  haveI : Functor.PreservesEpimorphisms E.inverse :=
    Functor.preservesEpimorphisms_of_adjunction E.symm.toAdjunction
  -- `G` is a separator of `ModuleCat S`.
  set G := E.functor.obj (ModuleCat.of.{u} R R) with hG
  have hsep : IsSeparator G := (isSeparator_regular R).of_equivalence E
  -- The sum of ranges of all maps `G ⟶ S` is everything.
  set N : Submodule S (ModuleCat.of.{u} S S) :=
    ⨆ (φ : G ⟶ ModuleCat.of.{u} S S), LinearMap.range φ.hom with hN
  have hNtop : N = ⊤ := by
    have hmkQ : ModuleCat.ofHom N.mkQ = (0 : ModuleCat.of.{u} S S ⟶ ModuleCat.of S (_ ⧸ N)) := by
      refine hsep _ _ (fun G' hG' hh => ?_)
      obtain rfl := (ObjectProperty.singleton_iff G G').mp hG'
      apply ModuleCat.hom_ext
      ext x
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      refine (Submodule.Quotient.mk_eq_zero N).mpr ?_
      exact le_iSup (fun φ : G ⟶ ModuleCat.of.{u} S S => LinearMap.range φ.hom) hh
        (LinearMap.mem_range_self hh.hom x)
    -- `mkQ = 0` forces `N = ⊤`.
    have hzero : N.mkQ = 0 := by
      have := congrArg ModuleCat.Hom.hom hmkQ
      simpa using this
    refine Submodule.eq_top_iff'.mpr (fun s => ?_)
    have : N.mkQ s = 0 := by rw [hzero]; rfl
    exact (Submodule.Quotient.mk_eq_zero N).mp this
  -- `1 ∈ N`, extract a finite family of maps whose combined image contains `1`.
  have h1 : (1 : (ModuleCat.of.{u} S S : Type u)) ∈ N := hNtop ▸ Submodule.mem_top
  rw [hN] at h1
  obtain ⟨t, ht⟩ := Submodule.mem_iSup_iff_exists_finset.mp h1
  obtain ⟨μ, hμ⟩ :=
    (Submodule.mem_iSup_finset_iff_exists_sum
      (fun φ : G ⟶ ModuleCat.of.{u} S S => LinearMap.range φ.hom) 1).mp ht
  -- Reindex `t` to `Fin n`.
  set n := t.card with hn
  let e := (t.equivFin)
  let g : Fin n → (G ⟶ ModuleCat.of.{u} S S) := fun i => ((e.symm i : {x // x ∈ t}) : G ⟶ _)
  -- choose preimages
  have hx : ∀ i : Fin n, ∃ y : (G : Type u),
      (g i).hom y = (↑(μ (g i)) : (ModuleCat.of.{u} S S : Type u)) :=
    fun i => LinearMap.mem_range.mp (μ (g i)).2
  choose x hx using hx
  -- reindexed sum equals `1`
  have hsum1 : (∑ i : Fin n, ((μ (g i)).1 : (ModuleCat.of.{u} S S : Type u))) = 1 := by
    have hre : (∑ i : Fin n, ((μ (g i)).1 : (ModuleCat.of.{u} S S : Type u)))
        = ∑ φ : {x // x ∈ t}, ((μ (↑φ : G ⟶ ModuleCat.of.{u} S S)).1 : (ModuleCat.of.{u} S S : Type u)) :=
      Fintype.sum_equiv e.symm _ _ (fun i => rfl)
    rw [hre, Finset.sum_coe_sort t (fun φ => ((μ φ).1 : (ModuleCat.of.{u} S S : Type u)))]
    exact hμ
  -- the descent map `Φ : ⨁ (fun _ => G) ⟶ S`
  let Φ : (⨁ fun _ : Fin n => G) ⟶ ModuleCat.of.{u} S S := biproduct.desc g
  -- element `z` with `Φ z = 1`
  let z := ∑ i : Fin n, (biproduct.ι (fun _ : Fin n => G) i).hom (x i)
  have hΦz : Φ.hom z = 1 := by
    have hstep : ∀ i : Fin n,
        Φ.hom ((biproduct.ι (fun _ : Fin n => G) i).hom (x i))
          = (↑(μ (g i)) : (ModuleCat.of.{u} S S : Type u)) := by
      intro i
      have hid : biproduct.ι (fun _ : Fin n => G) i ≫ Φ = g i := biproduct.ι_desc g i
      have := congrArg (fun m : G ⟶ ModuleCat.of.{u} S S => m.hom (x i)) hid
      simpa [ModuleCat.hom_comp] using this.trans (hx i)
    show Φ.hom (∑ i : Fin n, (biproduct.ι (fun _ : Fin n => G) i).hom (x i)) = 1
    calc Φ.hom (∑ i : Fin n, (biproduct.ι (fun _ : Fin n => G) i).hom (x i))
        = ∑ i : Fin n, Φ.hom ((biproduct.ι (fun _ : Fin n => G) i).hom (x i)) := by
          rw [map_sum]
      _ = ∑ i : Fin n, (↑(μ (g i)) : (ModuleCat.of.{u} S S : Type u)) :=
          Finset.sum_congr rfl (fun i _ => hstep i)
      _ = 1 := hsum1
  -- `Φ` is surjective, hence epi.
  have hsurj : Function.Surjective Φ.hom := by
    intro s
    exact ⟨s • z, by rw [map_smul, hΦz, smul_eq_mul, mul_one]⟩
  haveI hepi : Epi Φ := (ModuleCat.epi_iff_surjective Φ).mpr hsurj
  haveI : Epi (E.inverse.map Φ) := inferInstance
  -- the domain has finitely generated `E.inverse`-image
  haveI hdom : Module.Finite R (E.inverse.obj (⨁ fun _ : Fin n => G)) := by
    apply finite_functor_biproduct E.inverse (fun _ : Fin n => G)
    intro i
    have hiso : ModuleCat.of.{u} R R ≅ E.inverse.obj G := E.unitIso.app (ModuleCat.of.{u} R R)
    exact Module.Finite.equiv hiso.toLinearEquiv
  -- `E.inverse.map Φ` is a surjection onto `E.inverse (of S S)`.
  have hsurj2 : Function.Surjective (E.inverse.map Φ).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact Module.Finite.of_surjective (E.inverse.map Φ).hom hsurj2

/-- An equivalence of module categories carries finitely generated modules to finitely
generated modules, given that the image of the regular module is finitely generated. -/
lemma functor_finite_of_finite {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] [Functor.PreservesEpimorphisms F]
    (hreg : Module.Finite S (F.obj (ModuleCat.of.{u} R R)))
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite S (F.obj M) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  -- surjection `⨁ (fun _ => of R R) ⟶ M`
  let p : (⨁ fun _ : Fin n => ModuleCat.of.{u} R R) ⟶ M :=
    biproduct.desc (fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton R M (s i)))
  have hptop : LinearMap.range p.hom = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hid : biproduct.ι (fun _ : Fin n => ModuleCat.of.{u} R R) i ≫ p
        = ModuleCat.ofHom (LinearMap.toSpanSingleton R M (s i)) := biproduct.ι_desc _ i
    refine ⟨(biproduct.ι (fun _ : Fin n => ModuleCat.of.{u} R R) i).hom 1, ?_⟩
    have hcongr := congrArg (fun m : ModuleCat.of.{u} R R ⟶ M => m.hom 1) hid
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, one_smul] at hcongr
    exact hcongr
  haveI hepi : Epi p := (ModuleCat.epi_iff_range_eq_top p).mpr hptop
  haveI : Epi (F.map p) := inferInstance
  haveI : Module.Finite S (F.obj (⨁ fun _ : Fin n => ModuleCat.of.{u} R R)) := by
    apply finite_functor_biproduct F (fun _ : Fin n => ModuleCat.of.{u} R R)
    intro _; exact hreg
  have hsurj : Function.Surjective (F.map p).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact Module.Finite.of_surjective (F.map p).hom hsurj

/-- Image of the regular module under `E.functor` is finitely generated. -/
lemma functor_regular_finite {R S : Type u} [Ring R] [Ring S]
    (E : ModuleCat.{u} R ≌ ModuleCat.{u} S) :
    Module.Finite S (E.functor.obj (ModuleCat.of.{u} R R)) := by
  exact inverse_regular_finite E.symm

/-- An equivalence of module categories preserves and reflects finite generation. -/
lemma finite_functor_iff {A B : Type u} [Ring A] [Ring B]
    (E : ModuleCat.{u} A ≌ ModuleCat.{u} B) (M : ModuleCat.{u} A) :
    Module.Finite B (E.functor.obj M) ↔ Module.Finite A M := by
  haveI hFadd : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  haveI hIadd : E.inverse.Additive := Equivalence.inverse_additive E
  haveI : Functor.PreservesEpimorphisms E.functor :=
    Functor.preservesEpimorphisms_of_adjunction E.toAdjunction
  haveI : Functor.PreservesEpimorphisms E.inverse :=
    Functor.preservesEpimorphisms_of_adjunction E.symm.toAdjunction
  constructor
  · intro hEM
    -- reflect via `E.inverse` and the unit iso
    haveI : Module.Finite B (E.functor.obj M) := hEM
    haveI hfin : Module.Finite A ((E.functor ⋙ E.inverse).obj M) :=
      functor_finite_of_finite E.inverse (inverse_regular_finite E) (E.functor.obj M)
    exact Module.Finite.equiv (E.unitIso.app M).symm.toLinearEquiv
  · intro hM
    haveI : Module.Finite A M := hM
    exact functor_finite_of_finite E.functor (functor_regular_finite E) M

/-- `ModuleCat.isFG` is closed under isomorphisms. -/
instance isFG_isClosedUnderIsomorphisms (R : Type u) [Ring R] :
    (ModuleCat.isFG.{u} R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    haveI : Module.Finite R X := hX
    exact Module.Finite.equiv e.toLinearEquiv

/-- A Morita equivalence restricts to an equivalence of finitely generated module
categories. -/
theorem MoritaEquivalent.fgModuleCatEquiv {A B : Type u} [Ring A] [Ring B]
    (h : Etingof.MoritaEquivalent A B) :
    Nonempty (FGModuleCat.{u} A ≌ FGModuleCat.{u} B) := by
  obtain ⟨E⟩ := h
  have hobj : (ModuleCat.isFG.{u} B).inverseImage E.functor = ModuleCat.isFG.{u} A := by
    funext M
    apply propext
    exact finite_functor_iff E M
  exact ⟨E.congrFullSubcategory hobj⟩

end Etingof

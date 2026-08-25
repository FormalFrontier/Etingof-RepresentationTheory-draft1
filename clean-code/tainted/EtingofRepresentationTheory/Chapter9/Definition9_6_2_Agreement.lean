import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import EtingofRepresentationTheory.Chapter9.Definition9_6_2
import EtingofRepresentationTheory.Chapter9.Theorem9_6_4
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Order.KrullDimension

universe u v

/-!
# Definition 9.6.2: agreement of the general and finite progenerator notions

`Etingof.IsProjectiveGenerator P` is the **general** notion of Definition 9.6.2 (projective
separator), which allows the *infinite* coproducts needed to realize an arbitrary module over an
arbitrary ring. `Etingof.IsProgenerator P` is the **finite** variant used by the
finite-abelian-category development of §9.6: every object admits an epimorphism from a *finite*
biproduct `P^n`.

The forward agreement (finite ⟹ general) is `Etingof.IsProgenerator.isProjectiveGenerator`
(`Chapter9.Theorem9_6_4`). This file proves the **reverse** agreement: in a finite abelian
category (`Etingof.IsFiniteAbelianCategory`, whose objects all have finite length), a general
projective generator is a finite progenerator. This closes the "the two notions agree in the
finite abelian / finite-length setting used by Theorem 9.6.4" requirement.

## Proof outline

Finite abelian categories do **not** have arbitrary infinite coproducts, so the general
"quotient of a coproduct of copies of `P`" cannot be invoked directly. Instead we use the
finite-length standing assumption of §9.6, recorded as `FiniteDimensionalOrder (Subobject X)`
for every `X`. This makes every object **Noetherian** (`IsNoetherianObject`): an infinite
strictly increasing chain of subobjects would give `krullDim (Subobject X) = ⊤`, contradicting
finite dimensionality.

Given a Noetherian object `X` and a projective separator `P`, consider the subobjects of `X` that
are images of finite maps `P^n ⟶ X` (built with `biproduct.desc` of a finite family of maps
`P ⟶ X`). This set is nonempty (it contains `⊥`, the image of the empty family) and, by the
ascending chain condition, has a maximal element `m = im φ₀` for some `φ₀ : P^{n₀} ⟶ X`. If
`m ≠ ⊤` then the cokernel `X ⧸ m` is nonzero, so the separator property yields a nonzero
`g : P ⟶ X ⧸ m`; projectivity of `P` lifts it to `glift : P ⟶ X` along the (epi) quotient map.
Adjoining `glift` to the family gives `φ₁ : P^{n₀+1} ⟶ X` whose image strictly contains `m`
(it meets `X ⧸ m` nontrivially), contradicting maximality. Hence `m = ⊤`, i.e. `φ₀` is an
epimorphism `P^{n₀} ⟶ X`.
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An object whose subobject lattice is order-theoretically finite dimensional is Noetherian:
its subobjects satisfy the ascending chain condition. An infinite strictly increasing chain of
subobjects would embed `ℕ` (of infinite Krull dimension) into `Subobject X`, forcing
`krullDim (Subobject X) = ⊤` and contradicting finite dimensionality. -/
theorem isNoetherianObject_of_finiteDimensionalOrder_subobject (X : C)
    [FiniteDimensionalOrder (Subobject X)] : IsNoetherianObject X := by
  rw [isNoetherianObject_iff_not_strictMono]
  intro f hf
  have h1 : Order.krullDim ℕ ≤ Order.krullDim (Subobject X) :=
    Order.krullDim_le_of_strictMono f hf
  rw [Order.krullDim_nat] at h1
  exact Order.krullDim_ne_top_of_finiteDimensionalOrder (top_le_iff.mp h1)

end CategoryTheory

namespace Etingof

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C] {P : C}

/-- **Reverse agreement, core statement.** In a finite abelian category, if `P` is a projective
generator in the general sense of Definition 9.6.2 (a projective separator), then every object
`X` admits an epimorphism from a finite biproduct of copies of `P`. -/
theorem IsProjectiveGenerator.exists_finite_biproduct_epi
    (h : IsProjectiveGenerator P) (X : C) :
    ∃ (n : ℕ) (φ : (⨁ fun _ : Fin n => P) ⟶ X), Epi φ := by
  haveI : IsNoetherianObject X := isNoetherianObject_of_finiteDimensionalOrder_subobject X
  -- The subobjects of `X` that are images of finite maps `P^n ⟶ X`.
  let S : Set (Subobject X) :=
    fun Y => ∃ (n : ℕ) (v : Fin n → (P ⟶ X)), imageSubobject (biproduct.desc v) = Y
  have hSne : S.Nonempty :=
    ⟨imageSubobject (biproduct.desc (finZeroElim : Fin 0 → (P ⟶ X))), 0, finZeroElim, rfl⟩
  -- By the ascending chain condition, `S` has a maximal element.
  obtain ⟨m, ⟨n₀, v₀, hm⟩, hmax⟩ := wellFounded_gt.has_min S hSne
  by_cases hmtop : m = ⊤
  · -- Maximal image is everything: the corresponding map is an epimorphism.
    refine ⟨n₀, biproduct.desc v₀, ?_⟩
    have htop : imageSubobject (biproduct.desc v₀) = ⊤ := hm.trans hmtop
    haveI : IsIso (imageSubobject (biproduct.desc v₀)).arrow := by
      rw [Subobject.isIso_arrow_iff_eq_top]; exact htop
    have hfac := imageSubobject_arrow_comp (biproduct.desc v₀)
    rw [← hfac]
    exact epi_comp _ _
  · exfalso
    -- The quotient `X ⧸ m` is nonzero.
    let π : X ⟶ cokernel m.arrow := cokernel.π m.arrow
    have hcoker_ne : ¬ IsZero (cokernel m.arrow) := by
      intro hz
      have hπ0 : cokernel.π m.arrow = 0 := hz.eq_of_tgt _ _
      haveI : Epi m.arrow := Abelian.epi_of_cokernel_π_eq_zero _ hπ0
      haveI : IsIso m.arrow := isIso_of_mono_of_epi m.arrow
      exact hmtop (Subobject.eq_top_of_isIso_arrow m)
    -- Separator ⟹ a nonzero map `P ⟶ X ⧸ m`.
    have hsep : IsSeparator P := h.2
    obtain ⟨g, hg⟩ : ∃ g : P ⟶ cokernel m.arrow, g ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hcoker_ne
      rw [Preadditive.isSeparator_iff] at hsep
      have hid : 𝟙 (cokernel m.arrow) = 0 :=
        hsep _ (fun hh => by rw [Category.comp_id, hcon hh])
      exact (IsZero.iff_id_eq_zero _).mpr hid
    -- Lift `g` through the (epi) quotient map using projectivity of `P`.
    haveI : Projective P := h.1
    let glift : P ⟶ X := Projective.factorThru g π
    have hlift : glift ≫ π = g := Projective.factorThru_comp g π
    -- Adjoin `glift` to the family to get a larger image.
    let v₁ : Fin (n₀ + 1) → (P ⟶ X) := Fin.cons glift v₀
    let φ₁ := biproduct.desc v₁
    have hmemφ₁ : imageSubobject φ₁ ∈ S := ⟨n₀ + 1, v₁, rfl⟩
    -- `m ≤ im φ₁`: `φ₀` factors through `φ₁` via the tail inclusion.
    let incl : (⨁ fun _ : Fin n₀ => P) ⟶ (⨁ fun _ : Fin (n₀ + 1) => P) :=
      biproduct.desc (fun i => biproduct.ι (fun _ : Fin (n₀ + 1) => P) i.succ)
    have hfac : biproduct.desc v₀ = incl ≫ φ₁ := by
      refine biproduct.hom_ext' _ _ (fun i => ?_)
      simp only [incl, φ₁, v₁, biproduct.ι_desc, biproduct.ι_desc_assoc, Fin.cons_succ]
    have hle : m ≤ imageSubobject φ₁ := by
      rw [← hm, hfac]
      exact imageSubobject_comp_le incl φ₁
    -- Strictness: `glift` meets `X ⧸ m` nontrivially, so `im φ₁ ⊄ m`.
    have hne : m ≠ imageSubobject φ₁ := by
      intro heq
      have hφ₁le : imageSubobject φ₁ ≤ m := heq.ge
      -- `glift` factors through `φ₁`, hence its image is ≤ `im φ₁ ≤ m`.
      have hgliftfac : biproduct.ι (fun _ : Fin (n₀ + 1) => P) 0 ≫ φ₁ = glift := by
        simp only [φ₁, v₁, biproduct.ι_desc, Fin.cons_zero]
      have hgliftle : imageSubobject glift ≤ m := by
        calc imageSubobject glift
            = imageSubobject (biproduct.ι (fun _ : Fin (n₀ + 1) => P) 0 ≫ φ₁) := by rw [hgliftfac]
          _ ≤ imageSubobject φ₁ := imageSubobject_comp_le _ _
          _ ≤ m := hφ₁le
      -- So `glift` factors through `m.arrow`, forcing `g = glift ≫ π = 0`, a contradiction.
      let k : P ⟶ (m : C) := factorThruImageSubobject glift ≫ Subobject.ofLE _ _ hgliftle
      have hk : k ≫ m.arrow = glift := by
        simp only [k, Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
      have : g = 0 := by
        rw [← hlift, ← hk, Category.assoc]
        rw [show m.arrow ≫ π = 0 from cokernel.condition m.arrow, comp_zero]
      exact hg this
    exact hmax (imageSubobject φ₁) hmemφ₁ (lt_of_le_of_ne hle hne)

/-- **Reverse agreement (Definition 9.6.2).** In a finite abelian category (in which every object
has finite length), a general projective generator `P` (`Etingof.IsProjectiveGenerator`, i.e. a
projective separator) is a finite progenerator (`Etingof.IsProgenerator`): every object admits an
epimorphism from a finite biproduct of copies of `P`.

Together with `Etingof.IsProgenerator.isProjectiveGenerator` (the forward direction), this shows
the general and finite notions of Definition 9.6.2 agree in the finite-abelian-category setting of
Theorem 9.6.4. -/
theorem IsProjectiveGenerator.isProgenerator (h : IsProjectiveGenerator P) :
    IsProgenerator P :=
  { toProjective := h.1
    epiFromBiproduct := fun X => by
      obtain ⟨n, φ, hφ⟩ := h.exists_finite_biproduct_epi X
      exact ⟨n, inferInstance, φ, hφ⟩ }

end Etingof

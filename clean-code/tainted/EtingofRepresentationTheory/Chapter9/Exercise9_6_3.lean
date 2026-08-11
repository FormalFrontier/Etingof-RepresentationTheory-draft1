import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import EtingofRepresentationTheory.Chapter9.Definition9_6_2
import EtingofRepresentationTheory.Chapter9.KrullSchmidt.Length

/-!
# Exercise 9.6.3: Characterization of projective generators

Etingof Exercise 9.6.3. In a finite abelian category, a projective object `P` is a
**projective generator** if and only if for every simple object `L`, one has
`Hom(P, L) ≠ 0`. Deduce that any finite abelian category has a projective generator.

## Statement-pass note

We use `Etingof.IsProgenerator` (Definition 9.6.2) for "projective generator" and
`CategoryTheory.Simple` for simple objects. "`Hom(P, L) ≠ 0`" is rendered as the existence of
a nonzero morphism `∃ f : P ⟶ L, f ≠ 0`. The projectivity hypothesis is carried as an
instance `[Projective P]`, matching the book's "a projective object `P` is a projective
generator iff …". The deduction is the existence statement `∃ P, Nonempty (IsProgenerator P)`;
a witness is the direct sum of the projective covers of the (finitely many) simple objects.

## Proof outline

The nontrivial direction of the characterization is the *generation lemma*
`exists_epi_biproduct_of_hom_simple`: if `Hom(P, L) ≠ 0` for every simple `L`, then every
object `X` receives an epimorphism from a finite biproduct of copies of `P`. This is proved by
strong induction on the composition length `Etingof.clength X` (the §9.6 finite-length standing
assumption makes `Subobject X` finite dimensional, so `clength` is a well-founded rank). A
nonzero `X` has a simple subobject `S ↪ X` (`CategoryTheory.exists_simple_subobject`, using that
`Subobject X` is Artinian); the quotient `X / S` has strictly smaller length, so induction gives
an epi `P^m ↠ X/S`. Lifting it through `X ↠ X/S` (projectivity of `P^m`) and adjoining a copy of
`P ↠ S ↪ X` (from `Hom(P, S) ≠ 0`) produces an epi `P^{m+1} ↠ X`.

The forward direction extracts, from an epi `P^n ↠ L` onto a simple `L`, a nonzero component
`P ⟶ L` (a map out of a biproduct is zero iff all its components vanish). For the deduction we
take `P = ⨁ᵢ Projective.over (simpleObj i)`, a projective object with `Hom(P, L) ≠ 0` for every
simple `L`, and apply the characterization.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof.Exercise963

variable {C : Type u} [Category.{v} C]

/-- A finite biproduct of projective objects is projective. Mathlib's `Projective (⨁ g)` instance
constrains the index type to the morphism universe; this universe-polymorphic restatement lets us
form biproducts indexed by `Fin n` (and by the simple-object index type) in a category with an
arbitrary morphism universe. -/
theorem projective_biproduct {β : Type*} (g : β → C) [HasZeroMorphisms C] [HasBiproduct g]
    [∀ b, Projective (g b)] : Projective (biproduct g) where
  factors f e _ :=
    ⟨biproduct.desc fun b => Projective.factorThru (biproduct.ι g b ≫ f) e, by
      refine biproduct.hom_ext' _ _ (fun b => ?_)
      simp [Projective.factorThru_comp]⟩

/-- **Generation lemma.** In a finite abelian category, if a projective object `P` satisfies
`Hom(P, L) ≠ 0` for every simple object `L`, then every object `X` admits an epimorphism from a
finite biproduct of copies of `P`. Proved by strong induction on `Etingof.clength X`. -/
theorem exists_epi_biproduct_of_hom_simple [Etingof.IsFiniteAbelianCategory C] (P : C)
    [Projective P] (hHom : ∀ (L : C), Simple L → ∃ f : P ⟶ L, f ≠ 0) (X : C) :
    ∃ (n : ℕ) (_ : HasBiproduct (fun _ : Fin n => P))
      (f : biproduct (fun _ : Fin n => P) ⟶ X), Epi f := by
  haveI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  -- Strong induction on the composition length.
  suffices key : ∀ n, ∀ X : C, Etingof.clength X = n →
      ∃ (m : ℕ) (_ : HasBiproduct (fun _ : Fin m => P))
        (f : biproduct (fun _ : Fin m => P) ⟶ X), Epi f by
    exact key (Etingof.clength X) X rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro X hX
    by_cases hz : IsZero X
    · -- Base case: `X` is a zero object, so the empty biproduct maps onto it.
      refine ⟨0, inferInstance, 0, ⟨fun g h _ => hz.eq_of_src g h⟩⟩
    · -- Inductive step. `Subobject X` is Artinian (well-founded), so `X` has a simple subobject.
      haveI : IsArtinianObject X :=
        isArtinianObject.is_of_prop (Etingof.wellFoundedLT_subobject (X := X))
      set S : C := simpleSubobject hz with hSdef
      set i : S ⟶ X := simpleSubobjectArrow hz with hidef
      haveI : Simple S := inferInstance
      haveI : Mono i := inferInstance
      -- The cokernel square `0 → S → X → X/S → 0` is short exact.
      set q : X ⟶ cokernel i := cokernel.π i with hqdef
      have hSE : (ShortComplex.cokernelSequence i).ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
          (inferInstanceAs (Mono i)) (inferInstanceAs (Epi (cokernel.π i)))
      -- Additivity of length forces `clength (X/S) < clength X = n`.
      have hadd : Etingof.clength X = Etingof.clength S + Etingof.clength (cokernel i) := by
        simpa using Etingof.clength_additive hSE
      have hS1 : Etingof.clength S = 1 := Etingof.clength_simple inferInstance
      have hnpos : 0 < n := hX ▸ Etingof.clength_pos_of_not_isZero hz
      have hQlt : Etingof.clength (cokernel i) < n := by
        rw [hS1] at hadd; omega
      -- Induction gives an epi `π_Q : P^m ↠ X/S`.
      obtain ⟨m, hbpm, πQ, hπQ⟩ := IH _ hQlt (cokernel i) rfl
      haveI : HasBiproduct (fun _ : Fin m => P) := hbpm
      haveI : ∀ b : Fin m, Projective ((fun _ : Fin m => P) b) := fun _ => inferInstance
      haveI : Projective (biproduct (fun _ : Fin m => P)) := projective_biproduct _
      haveI : Epi πQ := hπQ
      -- Lift it through the quotient `q : X ↠ X/S` using projectivity of `P^m`.
      set a : biproduct (fun _ : Fin m => P) ⟶ X := Projective.factorThru πQ q with hadef
      have ha_comp : a ≫ q = πQ := Projective.factorThru_comp πQ q
      -- A nonzero map `g : P ↠ S` (simple `S`), giving `b = g ≫ i : P ⟶ X`.
      obtain ⟨g, hg⟩ := hHom S inferInstance
      haveI : Epi g := epi_of_nonzero_to_simple hg
      set b : P ⟶ X := g ≫ i with hbdef
      -- Assemble `c : P^{m+1} ⟶ X` from the `m` components of `a` and the extra copy `b`.
      set p : Fin (m + 1) → (P ⟶ X) :=
        Fin.lastCases b (fun k => biproduct.ι (fun _ : Fin m => P) k ≫ a) with hpdef
      refine ⟨m + 1, inferInstance, biproduct.desc p, ?_⟩
      -- It suffices to show the cokernel projection of `c` vanishes.
      apply Abelian.epi_of_cokernel_π_eq_zero
      set π₀ : X ⟶ cokernel (biproduct.desc p) := cokernel.π (biproduct.desc p) with hπ₀def
      have hcπ : biproduct.desc p ≫ π₀ = 0 := cokernel.condition _
      -- The last component gives `b ≫ π₀ = 0`, hence `i ≫ π₀ = 0` (cancel the epi `g`).
      have hb : b ≫ π₀ = 0 := by
        have h1 : biproduct.ι (fun _ : Fin (m + 1) => P) (Fin.last m) ≫ biproduct.desc p = b := by
          simp [hpdef]
        calc b ≫ π₀
            = (biproduct.ι (fun _ : Fin (m + 1) => P) (Fin.last m) ≫ biproduct.desc p) ≫ π₀ := by
              rw [h1]
          _ = biproduct.ι (fun _ : Fin (m + 1) => P) (Fin.last m) ≫ (biproduct.desc p ≫ π₀) := by
              rw [Category.assoc]
          _ = 0 := by rw [hcπ, comp_zero]
      have hi : i ≫ π₀ = 0 := by
        have hgi : g ≫ (i ≫ π₀) = 0 := by rw [← Category.assoc]; exact hb
        exact (cancel_epi g).1 (by rw [hgi, comp_zero])
      -- The first `m` components give `a ≫ π₀ = 0`.
      have ha : a ≫ π₀ = 0 := by
        refine biproduct.hom_ext' _ _ (fun k => ?_)
        have h2 : biproduct.ι (fun _ : Fin (m + 1) => P) k.castSucc ≫ biproduct.desc p
            = biproduct.ι (fun _ : Fin m => P) k ≫ a := by simp [hpdef]
        calc biproduct.ι (fun _ : Fin m => P) k ≫ (a ≫ π₀)
            = (biproduct.ι (fun _ : Fin m => P) k ≫ a) ≫ π₀ := by rw [Category.assoc]
          _ = (biproduct.ι (fun _ : Fin (m + 1) => P) k.castSucc ≫ biproduct.desc p) ≫ π₀ := by
              rw [h2]
          _ = biproduct.ι (fun _ : Fin (m + 1) => P) k.castSucc ≫ (biproduct.desc p ≫ π₀) := by
              rw [Category.assoc]
          _ = biproduct.ι (fun _ : Fin m => P) k ≫ 0 := by rw [hcπ, comp_zero, comp_zero]
      -- `π₀` factors through `X/S` (it kills `i`); the factor vanishes since `π_Q` is epi.
      set π' : cokernel i ⟶ cokernel (biproduct.desc p) := cokernel.desc i π₀ hi with hπ'def
      have hfact : q ≫ π' = π₀ := cokernel.π_desc i π₀ hi
      have hπQ' : πQ ≫ π' = 0 := by
        have : a ≫ (q ≫ π') = 0 := by rw [hfact]; exact ha
        rwa [← Category.assoc, ha_comp] at this
      have hπ'zero : π' = 0 := (cancel_epi πQ).1 (by rw [hπQ', comp_zero])
      rw [← hfact, hπ'zero, comp_zero]

/-- **Exercise 9.6.3.** In a finite abelian category, a projective object `P` is a projective
generator (`Etingof.IsProgenerator`) if and only if `Hom(P, L) ≠ 0` for every simple object
`L`. -/
theorem isProgenerator_iff_hom_simple_ne_zero
    [Etingof.IsFiniteAbelianCategory C] (P : C) [Projective P] :
    Nonempty (Etingof.IsProgenerator P) ↔
      ∀ (L : C), Simple L → ∃ f : P ⟶ L, f ≠ 0 := by
  constructor
  · -- Forward: a progenerator hits every simple through some biproduct component.
    rintro ⟨hpg⟩ L hL
    haveI : Simple L := hL
    obtain ⟨n, hbp, f, hf⟩ := hpg.epiFromBiproduct L
    haveI : HasBiproduct (fun _ : Fin n => P) := hbp
    haveI : Epi f := hf
    -- `f ≠ 0`: an epi onto a nonzero simple object cannot be the zero map.
    have hfne : f ≠ 0 := by
      rintro rfl
      have : 𝟙 L = 0 := (cancel_epi (0 : biproduct (fun _ : Fin n => P) ⟶ L)).1 (by simp)
      exact id_nonzero L this
    -- Some component `biproduct.ι k ≫ f : P ⟶ L` is therefore nonzero.
    have : ∃ k, biproduct.ι (fun _ : Fin n => P) k ≫ f ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hfne (biproduct.hom_ext' _ _ (fun k => by rw [hc k, comp_zero]))
    obtain ⟨k, hk⟩ := this
    exact ⟨_, hk⟩
  · -- Reverse: the generation lemma supplies the required epimorphisms.
    intro hHom
    exact ⟨{ toProjective := inferInstance
             epiFromBiproduct := fun X => exists_epi_biproduct_of_hom_simple P hHom X }⟩

/-- **Exercise 9.6.3, deduction.** Any finite abelian category has a projective generator.
A witness is `P = ⨁ᵢ Projective.over (simpleObj i)`, the direct sum of the projective covers of
the finitely many simple objects: it is projective and satisfies `Hom(P, L) ≠ 0` for every
simple `L`, so it is a progenerator by the characterization above. -/
theorem exists_progenerator (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] :
    ∃ P : C, Nonempty (Etingof.IsProgenerator P) := by
  haveI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  haveI : Fintype (Etingof.IsFiniteAbelianCategory.ι C) := Etingof.IsFiniteAbelianCategory.finι
  set Pi : Etingof.IsFiniteAbelianCategory.ι C → C :=
    fun i => Projective.over (Etingof.IsFiniteAbelianCategory.simpleObj i) with hPidef
  haveI : HasBiproduct Pi := inferInstance
  haveI : ∀ b, Projective (Pi b) := fun _ => inferInstance
  haveI : Projective (biproduct Pi) := projective_biproduct _
  refine ⟨biproduct Pi, ?_⟩
  rw [isProgenerator_iff_hom_simple_ne_zero]
  intro L hL
  haveI : Simple L := hL
  -- `L` is isomorphic to some representative simple `simpleObj j`.
  obtain ⟨j, ⟨e⟩⟩ := Etingof.IsFiniteAbelianCategory.iso_of_simple L hL
  -- Project onto the `j`-summand, hit `simpleObj j`, and transport back along `e`.
  refine ⟨biproduct.π Pi j ≫ Projective.π (Etingof.IsFiniteAbelianCategory.simpleObj j) ≫ e.inv, ?_⟩
  intro hzero
  -- Precomposing with the `j`-inclusion turns the map into `Projective.π _ ≫ e.inv`, an epi.
  have hj : Projective.π (Etingof.IsFiniteAbelianCategory.simpleObj j) ≫ e.inv = 0 := by
    have := congrArg (fun t => biproduct.ι Pi j ≫ t) hzero
    simpa [hPidef, biproduct.ι_π_self_assoc] using this
  haveI : Epi (Projective.π (Etingof.IsFiniteAbelianCategory.simpleObj j) ≫ e.inv) :=
    epi_comp _ _
  have : 𝟙 L = 0 :=
    (cancel_epi (Projective.π (Etingof.IsFiniteAbelianCategory.simpleObj j) ≫ e.inv)).1
      (by rw [hj]; simp)
  exact id_nonzero L this

end Etingof.Exercise963

/-
Copyright (c) 2026 FormalFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier contributors
-/
import EtingofRepresentationTheory.Chapter9.Introduction_9_6
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Order.KrullDimension
import Mathlib.Data.ENat.Basic

/-!
# Bridging the two finite-length encodings for abelian categories

Etingof §9.6 records the finite-length standing assumption in two different ways:

* order-theoretically, as `FiniteDimensionalOrder (Subobject X)` for every object `X`
  (the field `finiteDimensionalOrder_subobject` of `Etingof.IsFiniteAbelianCategory`,
  `Chapter9/Definition9_6_1.lean`), and
* inductively, as `Etingof.HasFiniteLength X` — `X` is built from the zero object and simple
  objects by finitely many extensions (`Chapter9/Introduction_9_6.lean`), the field
  `finiteLength` of `Etingof.IsFiniteAbelianCategoryOverField`.

Issue #7424 flags these as two disconnected encodings with no bridge. This file supplies the
*general abelian-category* bridge in the forward direction:

`Etingof.finiteDimensionalOrder_subobject_of_hasFiniteLength :`
`  HasFiniteLength X → FiniteDimensionalOrder (Subobject X)`,

so the two finite-length fields of #7424 are provably the same condition rather than
duplicated data.

## Strategy

Induct on `HasFiniteLength X`:

* `of_isZero`: `Subobject X` is a subsingleton, hence `FiniteDimensionalOrder`.
* `of_simple`: for `Simple X` the lattice `Subobject X` is `IsSimpleOrder`, hence order
  isomorphic to `Bool`, a finite order.
* `of_shortExact`: for `0 → X₁ → X₂ → X₃ → 0` with `FiniteDimensionalOrder` on
  `Subobject X₁` and `Subobject X₃`, the map
  `P ↦ ((pullback f).obj P, ((«exists» g).obj P))` from `Subobject X₂` into
  `Subobject X₁ × Subobject X₃` is strictly monotone (length additivity in a short exact
  sequence). The product of two finite-dimensional orders is finite dimensional
  (`Order.finiteDimensionalOrder_prod`, proved here by bounding a chain's length by the sum
  of the two Krull dimensions via `Order.height`), so `Order.krullDim_le_of_strictMono`
  transports finite dimensionality back to `Subobject X₂`.

The general order-theoretic helpers (`finiteDimensionalOrder_of_finite`,
`finiteDimensionalOrder_of_orderIso`, `finiteDimensionalOrder_prod`) are stated for arbitrary
preorders and are reusable Mathlib-style facts.
-/

open CategoryTheory CategoryTheory.Limits

namespace Order

variable {α : Type*} {β : Type*} [Preorder α] [Preorder β]

/-- In a finite-dimensional order, every element has finite height. -/
lemma height_lt_top [FiniteDimensionalOrder α] (x : α) : height x < ⊤ := by
  rw [← WithBot.coe_lt_coe]
  apply lt_of_le_of_lt (height_le_krullDim x)
  simpa using krullDim_ne_top_of_finiteDimensionalOrder.lt_top

/-- A nonempty finite preorder is finite dimensional: its `<`-series are bounded by the
cardinality. -/
theorem finiteDimensionalOrder_of_finite (γ : Type*) [Preorder γ] [Finite γ] [Nonempty γ] :
    FiniteDimensionalOrder γ := by
  rw [finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
  refine ⟨by rw [Ne, krullDim_eq_bot_iff, not_isEmpty_iff]; exact ‹Nonempty γ›, ?_⟩
  rw [Ne, krullDim_eq_top_iff]
  intro hinf
  have : Fintype γ := Fintype.ofFinite γ
  have hinj : Function.Injective (LTSeries.withLength γ (Fintype.card γ)) :=
    (LTSeries.withLength γ (Fintype.card γ)).strictMono.injective
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, LTSeries.length_withLength] at hcard
  omega

/-- Finite dimensionality of an order is invariant under order isomorphism. -/
theorem finiteDimensionalOrder_of_orderIso (e : α ≃o β) [FiniteDimensionalOrder β] :
    FiniteDimensionalOrder α := by
  rw [finiteDimensionalOrder_iff_krullDim_ne_bot_and_top, krullDim_eq_of_orderIso e]
  exact ⟨krullDim_ne_bot_of_finiteDimensionalOrder, krullDim_ne_top_of_finiteDimensionalOrder⟩

/-- A strict inequality of extended naturals descends to `toNat` when the larger value is
finite. -/
private lemma toNat_lt_toNat {m n : ℕ∞} (hmn : m < n) (hn : n ≠ ⊤) : m.toNat < n.toNat := by
  have hm : m ≠ ⊤ := (hmn.trans (lt_top_iff_ne_top.mpr hn)).ne
  have : (m.toNat : ℕ∞) < (n.toNat : ℕ∞) := by
    rw [ENat.coe_toNat hm, ENat.coe_toNat hn]; exact hmn
  exact_mod_cast this

/-- The product of two finite-dimensional orders is finite dimensional: a strictly increasing
chain in `α × β` has length at most the sum of the two Krull dimensions, because the map
`(a, b) ↦ height a + height b` into `ℕ` is strictly monotone and bounded. -/
theorem finiteDimensionalOrder_prod [FiniteDimensionalOrder α] [FiniteDimensionalOrder β] :
    FiniteDimensionalOrder (α × β) := by
  haveI := LTSeries.nonempty_of_finiteDimensionalOrder α
  haveI := LTSeries.nonempty_of_finiteDimensionalOrder β
  -- Uniform ℕ-bounds for the heights in each factor.
  set na := (LTSeries.longestOf α).length with hna
  set nb := (LTSeries.longestOf β).length with hnb
  have hkα : krullDim α = (na : ℕ∞) := krullDim_eq_length_of_finiteDimensionalOrder
  have hkβ : krullDim β = (nb : ℕ∞) := krullDim_eq_length_of_finiteDimensionalOrder
  have hha : ∀ a : α, (height a).toNat ≤ na := fun a => by
    apply ENat.toNat_le_of_le_coe
    have : (height a : WithBot ℕ∞) ≤ (na : ℕ∞) := hkα ▸ height_le_krullDim a
    exact_mod_cast this
  have hhb : ∀ b : β, (height b).toNat ≤ nb := fun b => by
    apply ENat.toNat_le_of_le_coe
    have : (height b : WithBot ℕ∞) ≤ (nb : ℕ∞) := hkβ ▸ height_le_krullDim b
    exact_mod_cast this
  -- The bounded, strictly monotone measure `α × β → Fin (na + nb + 1)`.
  let g : α × β → Fin (na + nb + 1) := fun p =>
    ⟨(height p.1).toNat + (height p.2).toNat, by have := hha p.1; have := hhb p.2; omega⟩
  have hg : StrictMono g := by
    intro p q hpq
    rw [Fin.lt_def]
    change (height p.1).toNat + (height p.2).toNat < (height q.1).toNat + (height q.2).toNat
    rw [Prod.lt_iff] at hpq
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := toNat_lt_toNat (height_strictMono h1 (height_lt_top p.1)) (height_lt_top q.1).ne
      have := ENat.toNat_le_toNat (height_mono h2) (height_lt_top q.2).ne
      omega
    · have := ENat.toNat_le_toNat (height_mono h1) (height_lt_top q.1).ne
      have := toNat_lt_toNat (height_strictMono h2 (height_lt_top p.2)) (height_lt_top q.2).ne
      omega
  -- Transport finite dimensionality of `Fin (na + nb + 1)` back through this strict monotone.
  haveI : FiniteDimensionalOrder (Fin (na + nb + 1)) := finiteDimensionalOrder_of_finite _
  rw [finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
  refine ⟨by rw [Ne, krullDim_eq_bot_iff, not_isEmpty_iff]; infer_instance, fun htop => ?_⟩
  have hle := krullDim_le_of_strictMono g hg
  rw [htop] at hle
  exact krullDim_ne_top_of_finiteDimensionalOrder (top_le_iff.mp hle)

/-- Finite dimensionality transfers backwards along a strictly monotone map into a
finite-dimensional order, provided the domain is nonempty: a `<`-series in `α` maps to one of
the same length in `β`, so `krullDim α ≤ krullDim β < ⊤`. -/
theorem finiteDimensionalOrder_of_strictMono {f : α → β} (hf : StrictMono f)
    [FiniteDimensionalOrder β] [Nonempty α] : FiniteDimensionalOrder α := by
  rw [finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
  refine ⟨by rw [Ne, krullDim_eq_bot_iff, not_isEmpty_iff]; infer_instance, fun htop => ?_⟩
  have hle := krullDim_le_of_strictMono f hf
  rw [htop] at hle
  exact krullDim_ne_top_of_finiteDimensionalOrder (top_le_iff.mp hle)

end Order

namespace Etingof

variable {C : Type*} [Category C] [Abelian C]

/-- **Image–pullback correspondence (intersection).** Pulling a subobject `P` back along a mono
`f` and pushing it forward again recovers the intersection `P ⊓ mk f`, where `mk f` is the image
of `f`. This is one half of the subobject correspondence used to prove length additivity. -/
theorem map_pullback_obj_inf {X Y : C} (f : X ⟶ Y) [Mono f] (P : Subobject Y) :
    (Subobject.map f).obj ((Subobject.pullback f).obj P) = P ⊓ Subobject.mk f := by
  rw [inf_comm, Subobject.inf_def]
  exact (Subobject.inf_eq_map_pullback' (MonoOver.mk f) P).symm

/-- A subobject `Q` lies below `S` as soon as `Q.arrow` becomes zero after composing with the
cokernel projection of `S.arrow`: in an abelian category `S.arrow` is the kernel of its own
cokernel, so `Q.arrow` factors through `S.arrow`. -/
private theorem le_of_arrow_comp_cokernel {X : C} (Q S : Subobject X)
    (h : Q.arrow ≫ cokernel.π S.arrow = 0) : Q ≤ S :=
  Subobject.le_of_comm (Abelian.monoLift S.arrow Q.arrow h) (Abelian.monoLift_comp _ _ _)

/-- **Image–pullback correspondence (join).** For an arbitrary morphism `g`, the preimage under
`g` of the image `g(P)` of a subobject `P` is `P` joined with the kernel of `g`. This is the
other half of the subobject correspondence used to prove length additivity. -/
theorem pullback_exists_obj_sup {X Y : C} (g : X ⟶ Y) (P : Subobject X) :
    (Subobject.pullback g).obj ((Subobject.«exists» g).obj P) = P ⊔ kernelSubobject g := by
  refine le_antisymm ?_ ?_
  · -- `pullback g (∃_g P) ≤ P ⊔ ker g`.  We show `Q.arrow ≫ cokernel.π S.arrow = 0`.
    set Q := (Subobject.pullback g).obj ((Subobject.«exists» g).obj P) with hQ
    set S := P ⊔ kernelSubobject g with hS
    -- Epi–mono factorisation `g = e ≫ image.ι g`.
    set e := Limits.factorThruImage g with he
    have hgfac : e ≫ Limits.image.ι g = g := Limits.image.fac g
    -- `(ker g).arrow` and `kernel.ι e` both die against `cokernel.π S.arrow`.
    have hKc : (kernelSubobject g).arrow ≫ cokernel.π S.arrow = 0 := by
      rw [← Subobject.ofLE_arrow (le_sup_right : kernelSubobject g ≤ S), Category.assoc,
        cokernel.condition, comp_zero]
    have hkerc : Limits.kernel.ι e ≫ cokernel.π S.arrow = 0 := by
      have hkeg : Limits.kernel.ι e ≫ g = 0 := by
        calc Limits.kernel.ι e ≫ g
            = (Limits.kernel.ι e ≫ e) ≫ Limits.image.ι g := by rw [Category.assoc, hgfac]
          _ = 0 := by rw [Limits.kernel.condition, zero_comp]
      have hfac := kernelSubobject_factors g (Limits.kernel.ι e) hkeg
      rw [← Subobject.factorThru_arrow (kernelSubobject g) (Limits.kernel.ι e) hfac,
        Category.assoc, hKc, comp_zero]
    -- `c̄ : image g ⟶ cokernel S.arrow` with `e ≫ c̄ = cokernel.π S.arrow`.
    set cbar := Abelian.epiDesc e (cokernel.π S.arrow) hkerc with hcbar
    have hecbar : e ≫ cbar = cokernel.π S.arrow := Abelian.comp_epiDesc e _ hkerc
    -- `v : ∃_g P ⟶ image g` with `v ≫ image.ι g = (∃_g P).arrow`.
    let F' : Limits.MonoFactorisation (P.arrow ≫ g) :=
      { I := Limits.image g
        m := Limits.image.ι g
        e := P.arrow ≫ e
        fac := by rw [Category.assoc, hgfac] }
    set v := (Subobject.imageFactorisation g P).isImage.lift F' with hvdef
    have hv : v ≫ Limits.image.ι g = ((Subobject.«exists» g).obj P).arrow := by
      have h := (Subobject.imageFactorisation g P).isImage.lift_fac F'
      rw [Subobject.imageFactorisation_F_m] at h
      exact h
    -- The image factorisation of `P.arrow ≫ g` through `∃_g P`, with `F.e` a (strong) epi.
    set fe := (Subobject.imageFactorisation g P).F.e with hfe
    have hfefac : fe ≫ ((Subobject.«exists» g).obj P).arrow = P.arrow ≫ g := by
      have h := (Subobject.imageFactorisation g P).F.fac
      rw [Subobject.imageFactorisation_F_m] at h
      exact h
    haveI : Epi fe := by
      rw [hfe]
      haveI : StrongEpi ((Subobject.imageFactorisation g P).F.e) :=
        Limits.strongEpi_of_strongEpiMonoFactorisation
          (Classical.choice (Limits.HasStrongEpiMonoFactorisations.has_fac (P.arrow ≫ g)))
          (Subobject.imageFactorisation g P).isImage
      infer_instance
    -- `v ≫ c̄ = 0`: precomposing with the epi `fe` gives `P.arrow ≫ (e ≫ c̄) = P.arrow ≫ π = 0`.
    have hfev : fe ≫ v = P.arrow ≫ e := by
      rw [← cancel_mono (Limits.image.ι g), Category.assoc, hv, hfefac, Category.assoc, hgfac]
    have hvc : v ≫ cbar = 0 := by
      rw [← cancel_epi fe, comp_zero, ← Category.assoc, hfev, Category.assoc, hecbar,
        ← Subobject.ofLE_arrow (le_sup_left : P ≤ S), Category.assoc, cokernel.condition,
        comp_zero]
    -- Assemble `Q.arrow ≫ cokernel.π S.arrow = 0` using `Q.arrow ≫ e = w ≫ v`.
    refine le_of_arrow_comp_cokernel Q S ?_
    set w := Subobject.pullbackπ g ((Subobject.«exists» g).obj P) with hw
    have hwsq : w ≫ ((Subobject.«exists» g).obj P).arrow = Q.arrow ≫ g :=
      (Subobject.isPullback g ((Subobject.«exists» g).obj P)).w
    have hQe : Q.arrow ≫ e = w ≫ v := by
      rw [← cancel_mono (Limits.image.ι g), Category.assoc, Category.assoc, hv, hwsq, hgfac]
    calc Q.arrow ≫ cokernel.π S.arrow
        = Q.arrow ≫ e ≫ cbar := by rw [hecbar]
      _ = (Q.arrow ≫ e) ≫ cbar := by rw [Category.assoc]
      _ = (w ≫ v) ≫ cbar := by rw [hQe]
      _ = w ≫ v ≫ cbar := by rw [Category.assoc]
      _ = w ≫ 0 := by rw [hvc]
      _ = 0 := comp_zero
  · -- `P ⊔ ker g ≤ pullback g (∃_g P)`.
    refine sup_le ?_ ?_
    · exact leOfHom ((Subobject.existsPullbackAdj g).unit.app P)
    · refine Subobject.le_of_comm
        ((Subobject.isPullback g ((Subobject.«exists» g).obj P)).lift 0
          (kernelSubobject g).arrow ?_) ?_
      · rw [zero_comp, kernelSubobject_arrow_comp]
      · exact (Subobject.isPullback g ((Subobject.«exists» g).obj P)).lift_snd _ _ _

/-- **Epi-descent for subobject factoring.** If `π` is an epimorphism and `π ≫ a` factors through
a subobject `T`, then `a` itself factors through `T`. (In an abelian category `T.arrow` is the
kernel of its cokernel, so `a ≫ cokernel.π T.arrow = 0` lifts `a` through `T.arrow`.) -/
private theorem factors_of_epi_comp {X : C} (T : Subobject X) {A' A : C} (π : A' ⟶ A) [Epi π]
    {a : A ⟶ X} (h : T.Factors (π ≫ a)) : T.Factors a := by
  have hc : T.factorThru (π ≫ a) h ≫ T.arrow = π ≫ a := T.factorThru_arrow _ _
  have key : a ≫ cokernel.π T.arrow = 0 := by
    rw [← cancel_epi π, comp_zero, ← Category.assoc, ← hc, Category.assoc, cokernel.condition,
      comp_zero]
  haveI : Mono (ShortComplex.cokernelSequence T.arrow).f := by
    simpa only [ShortComplex.cokernelSequence_f] using (inferInstance : Mono T.arrow)
  obtain ⟨d, hd⟩ := (ShortComplex.cokernelSequence_exact T.arrow).lift' a key
  have hd' : d ≫ T.arrow = a := by simpa only [ShortComplex.cokernelSequence_f] using hd
  exact hd' ▸ T.factors_comp_arrow d

/-- **Join membership up to refinements.** If `a : A ⟶ X` factors through `P ⊔ Q`, then, after
precomposing with a suitable epimorphism `π`, it decomposes as a sum of a morphism into `P` and a
morphism into `Q`. This is the categorical replacement for "an element of `P + Q` is a sum `p + q`"
used in the module-theoretic proof of the modular law. -/
private theorem sup_factors_refinements {X : C} (P Q : Subobject X) {A : C} (a : A ⟶ X)
    (h : (P ⊔ Q).Factors a) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (p : A' ⟶ (P : C)) (q : A' ⟶ (Q : C)),
      π ≫ a = p ≫ P.arrow + q ≫ Q.arrow := by
  set d : ((P : C) ⊞ (Q : C)) ⟶ X := biprod.desc P.arrow Q.arrow with hd
  -- `P ⊔ Q` is the image of `d = biprod.desc P.arrow Q.arrow`.
  have hPQ : (P ⊔ Q : Subobject X) = imageSubobject d := by
    set fP : (P : C) ⟶ (P ⊔ Q : Subobject X) :=
      (P ⊔ Q).factorThru P.arrow (Subobject.sup_factors_of_factors_left P.factors_self) with hfP
    set fQ : (Q : C) ⟶ (P ⊔ Q : Subobject X) :=
      (P ⊔ Q).factorThru Q.arrow (Subobject.sup_factors_of_factors_right Q.factors_self) with hfQ
    refine le_antisymm (sup_le ?_ ?_) (imageSubobject_le d (biprod.desc fP fQ) ?_)
    · refine Subobject.le_of_factors ?_
      have hPd : biprod.inl ≫ d = P.arrow := by rw [hd, biprod.inl_desc]
      rw [← hPd]
      exact imageSubobject_factors_comp_self d biprod.inl
    · refine Subobject.le_of_factors ?_
      have hQd : biprod.inr ≫ d = Q.arrow := by rw [hd, biprod.inr_desc]
      rw [← hQd]
      exact imageSubobject_factors_comp_self d biprod.inr
    · apply biprod.hom_ext'
      · simp only [hfP, biprod.inl_desc_assoc, Subobject.factorThru_arrow, hd, biprod.inl_desc]
      · simp only [hfQ, biprod.inr_desc_assoc, Subobject.factorThru_arrow, hd, biprod.inr_desc]
  -- Lift `a` through the epimorphism `factorThruImageSubobject d` onto the biproduct.
  set b : A ⟶ (imageSubobject d : C) := (imageSubobject d).factorThru a (hPQ ▸ h) with hb
  have hbfac : b ≫ (imageSubobject d).arrow = a := Subobject.factorThru_arrow _ _ _
  obtain ⟨A', π, hπ, w, hw⟩ :=
    surjective_up_to_refinements_of_epi (factorThruImageSubobject d) b
  refine ⟨A', π, hπ, w ≫ biprod.fst, w ≫ biprod.snd, ?_⟩
  have hπa : π ≫ a = w ≫ d :=
    calc π ≫ a = π ≫ b ≫ (imageSubobject d).arrow := by rw [hbfac]
      _ = (w ≫ factorThruImageSubobject d) ≫ (imageSubobject d).arrow := by
          rw [← Category.assoc, hw]
      _ = w ≫ d := by rw [Category.assoc, imageSubobject_arrow_comp]
  rw [hπa, hd, biprod.desc_eq, Preadditive.comp_add]
  simp only [Category.assoc]

/-- **Modularity of the subobject lattice.** The lattice of subobjects of an object in an abelian
category is modular. Not currently in Mathlib; needed for the short-exact length-additivity
step. -/
theorem isModularLattice_subobject (X : C) : IsModularLattice (Subobject X) where
  sup_inf_le_assoc_of_le := by
    intro P Q R hPR
    -- Reduce `(P ⊔ Q) ⊓ R ≤ P ⊔ Q ⊓ R` to a factoring statement for the intersection arrow.
    refine Subobject.le_of_factors ?_
    have haPQ : (P ⊔ Q).Factors ((P ⊔ Q) ⊓ R).arrow := Subobject.inf_arrow_factors_left _ _
    have haR : R.Factors ((P ⊔ Q) ⊓ R).arrow := Subobject.inf_arrow_factors_right _ _
    obtain ⟨A', π, hπ, p, q, hpq⟩ := sup_factors_refinements P Q _ haPQ
    haveI := hπ
    -- `P ≤ R`, so `P.arrow` factors through `R`.
    have hPR' : R.Factors P.arrow := Subobject.factors_of_le P.arrow hPR P.factors_self
    -- `q ≫ Q.arrow = (π ≫ a) - (p ≫ P.arrow)` factors through `R` (both summands do).
    have hqQ_R : R.Factors (q ≫ Q.arrow) := by
      have haRf : R.factorThru _ haR ≫ R.arrow = ((P ⊔ Q) ⊓ R).arrow :=
        Subobject.factorThru_arrow _ _ _
      have hPRf : R.factorThru P.arrow hPR' ≫ R.arrow = P.arrow := Subobject.factorThru_arrow _ _ _
      have hwR : (π ≫ R.factorThru _ haR - p ≫ R.factorThru P.arrow hPR') ≫ R.arrow
          = q ≫ Q.arrow := by
        rw [Preadditive.sub_comp, Category.assoc, Category.assoc, haRf, hPRf, hpq]
        abel
      exact hwR ▸ Subobject.factors_comp_arrow _
    -- `q ≫ Q.arrow` factors through `Q` and through `R`, hence through `Q ⊓ R`.
    have hqQR : (Q ⊓ R).Factors (q ≫ Q.arrow) :=
      (Subobject.inf_factors _).2 ⟨Subobject.factors_comp_arrow q, hqQ_R⟩
    -- Assemble: `π ≫ a = (p ≫ P.arrow) + (q ≫ Q.arrow)` factors through `P ⊔ Q ⊓ R`.
    have hstep : (P ⊔ Q ⊓ R).Factors (π ≫ ((P ⊔ Q) ⊓ R).arrow) := by
      rw [hpq]
      exact Subobject.factors_add _ _
        (Subobject.sup_factors_of_factors_left (Subobject.factors_comp_arrow p))
        (Subobject.sup_factors_of_factors_right hqQR)
    -- Descend through the epimorphism `π`.
    exact factors_of_epi_comp _ π hstep

/-- Cancellation in a modular lattice: an element `Q` above `P` that agrees with `P` on both the
meet and the join with a third element `K` equals `P`. This is the abstract heart of length
additivity in a short exact sequence. -/
private theorem eq_of_le_of_inf_eq_of_sup_eq {X : C} [IsModularLattice (Subobject X)]
    {P Q K : Subobject X} (hPQ : P ≤ Q) (hinf : P ⊓ K = Q ⊓ K) (hsup : P ⊔ K = Q ⊔ K) :
    P = Q := by
  refine le_antisymm hPQ ?_
  calc Q = Q ⊓ (Q ⊔ K) := inf_sup_self.symm
    _ = Q ⊓ (P ⊔ K) := by rw [hsup]
    _ ≤ Q ⊓ K ⊔ P := by rw [sup_comm P K]; exact inf_sup_le_assoc_of_le K hPQ
    _ = P ⊓ K ⊔ P := by rw [hinf]
    _ = P := by rw [sup_comm]; exact sup_inf_self

/-- **The bridge (forward direction).** If `X` has finite length in the inductive sense
(`Etingof.HasFiniteLength`), then its subobject lattice is finite dimensional as an order.
This proves the two finite-length encodings of Etingof §9.6 (issue #7424) — the inductive
`finiteLength` field of `IsFiniteAbelianCategoryOverField` and the order-theoretic
`finiteDimensionalOrder_subobject` field of `IsFiniteAbelianCategory` — record the same
condition. -/
theorem finiteDimensionalOrder_subobject_of_hasFiniteLength {X : C}
    (hX : HasFiniteLength X) : FiniteDimensionalOrder (Subobject X) := by
  induction hX with
  | @of_isZero Y h =>
      haveI : Subsingleton (Subobject Y) := Subobject.subsingleton_of_isZero h
      haveI : Inhabited (Subobject Y) := ⟨⊥⟩
      haveI : Unique (Subobject Y) := Unique.mk' _
      infer_instance
  | @of_simple Y h =>
      haveI := h
      letI : DecidableEq (Subobject Y) := Classical.decEq _
      haveI : FiniteDimensionalOrder Bool := Order.finiteDimensionalOrder_of_finite Bool
      exact Order.finiteDimensionalOrder_of_orderIso IsSimpleOrder.orderIsoBool
  | @of_shortExact S hS h₁ h₃ ih₁ ih₃ =>
      -- Length additivity in a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, via the strictly
      -- monotone measuring map `θ P = (f⁻¹P, g(P))` into the finite-dimensional product
      -- `Subobject S.X₁ × Subobject S.X₃`. See issue #7643.
      haveI := hS.mono_f
      haveI := hS.epi_g
      haveI := ih₁
      haveI := ih₃
      haveI : IsModularLattice (Subobject S.X₂) := isModularLattice_subobject S.X₂
      haveI : FiniteDimensionalOrder (Subobject S.X₁ × Subobject S.X₃) :=
        Order.finiteDimensionalOrder_prod
      haveI : Nonempty (Subobject S.X₂) := ⟨⊥⟩
      -- `K = im f = ker g` by exactness.
      set K : Subobject S.X₂ := kernelSubobject S.g with hKdef
      have hmkK : Subobject.mk S.f = K := by
        rw [hKdef, ← imageSubobject_mono S.f, S.exact_iff_image_eq_kernel.mp hS.exact]
      -- The measuring map and its (strict) monotonicity.
      set θ : Subobject S.X₂ → Subobject S.X₁ × Subobject S.X₃ :=
        fun P => ((Subobject.pullback S.f).obj P, (Subobject.«exists» S.g).obj P) with hθ
      have hmono : Monotone θ := fun P Q h =>
        ⟨leOfHom ((Subobject.pullback S.f).map (homOfLE h)),
         leOfHom ((Subobject.«exists» S.g).map (homOfLE h))⟩
      have hstrict : StrictMono θ := by
        refine fun P Q hlt => lt_of_le_of_ne (hmono hlt.le) (fun heq => hlt.ne ?_)
        rw [hθ, Prod.mk.injEq] at heq
        obtain ⟨h1, h2⟩ := heq
        have hinf : P ⊓ K = Q ⊓ K := by
          have h1' := congrArg (Subobject.map S.f).obj h1
          rwa [map_pullback_obj_inf, map_pullback_obj_inf, hmkK] at h1'
        have hsup : P ⊔ K = Q ⊔ K := by
          have h2' := congrArg (Subobject.pullback S.g).obj h2
          rwa [pullback_exists_obj_sup, pullback_exists_obj_sup] at h2'
        exact eq_of_le_of_inf_eq_of_sup_eq hlt.le hinf hsup
      exact Order.finiteDimensionalOrder_of_strictMono hstrict

end Etingof

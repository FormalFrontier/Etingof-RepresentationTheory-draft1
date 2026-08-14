import RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional
import RepresentationTheory.CategoryTheory.Abelian.FiniteLength
import Mathlib.Order.KrullDimension
import Mathlib.Order.OrderIsoNat
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Lengths of subobject lattices

This module assigns each object a natural number obtained from the order height at its maximal
subobject. Short exact sequences control this value additively, and the resulting rank yields
well-founded strict descent together with eventual constancy for images and kernels of iterated
endomorphisms.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.Abelian.SubobjectLength

variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]

attribute [local instance] CategoryTheory.Abelian.Pseudoelement.objectToSort
  CategoryTheory.Abelian.Pseudoelement.homToFun CategoryTheory.Abelian.Pseudoelement.overToSort


/-- A natural-number-valued length assigned to an object of a category. -/
noncomputable def objectLength (X : C) : ℕ :=
  (Order.height (⊤ : Subobject X)).toNat


/-- A zero object has length zero. -/
theorem objectLength_eq_zero_of_isZero {X : C} (h : IsZero X) : objectLength X = 0 := by
  have : Subsingleton (Subobject X) := Subobject.subsingleton_of_isZero h
  have hmin : IsMin (⊤ : Subobject X) := fun b _ => le_of_eq (Subsingleton.elim _ _)
  simp only [objectLength, Order.height_eq_zero.2 hmin, ENat.toNat_zero]


/-- A simple object has length one. -/
theorem objectLength_eq_one_of_simple {X : C} (h : Simple X) : objectLength X = 1 := by
  haveI : IsSimpleOrder (Subobject X) := (simple_iff_subobject_isSimpleOrder X).mp h
  have hheight : Order.height (⊤ : Subobject X) = 1 := by
    refine le_antisymm (Order.height_le_coe_iff.mpr ?_) ?_
    · intro y hy
      have hy0 : y = ⊥ := (IsSimpleOrder.eq_bot_or_eq_top y).resolve_right (ne_of_lt hy)
      subst hy0
      simp [Order.height_eq_zero.mpr isMin_bot]
    · have := Order.height_add_one_le (bot_lt_top : (⊥ : Subobject X) < ⊤)
      simpa [Order.height_eq_zero.mpr isMin_bot] using this
  simp [objectLength, hheight]


/-- The subobject order of a zero object is finite-dimensional. -/
theorem finiteDimensionalOrder_subobject_of_isZero {X : C} (h : IsZero X) :
    FiniteDimensionalOrder (Subobject X) := by
  haveI := Subobject.subsingleton_of_isZero h
  haveI : Nonempty (Subobject X) := ⟨⊤⟩
  haveI : Unique (Subobject X) := Unique.mk' _
  infer_instance


/-- For a finite-dimensional subobject order, its top height is finite. -/
theorem subobject_height_lt_top {X : C} [FiniteDimensionalOrder (Subobject X)] :
    Order.height (⊤ : Subobject X) < ⊤ := by
  rw [← WithBot.coe_lt_coe]
  apply lt_of_le_of_lt (Order.height_le_krullDim (⊤ : Subobject X))
  simpa using (Order.krullDim_ne_top_of_finiteDimensionalOrder
    (α := Subobject X)).lt_top


/-- With a finite-dimensional subobject order, length zero characterizes zero objects. -/
theorem objectLength_eq_zero_iff_isZero_of_finiteDimensionalOrder {X : C}
    [FiniteDimensionalOrder (Subobject X)] : objectLength X = 0 ↔ IsZero X := by
  refine ⟨fun h => ?_, objectLength_eq_zero_of_isZero⟩
  have h0 : Order.height (⊤ : Subobject X) = 0 := by
    rw [objectLength, ENat.toNat_eq_zero] at h
    exact h.resolve_right (ne_of_lt subobject_height_lt_top)
  have hmin : IsMin (⊤ : Subobject X) := Order.height_eq_zero.mp h0
  by_contra hX
  haveI := Subobject.nontrivial_of_not_isZero hX
  refine not_subsingleton (Subobject X) ⟨fun a b => ?_⟩
  rw [le_antisymm (le_top : a ≤ ⊤) (hmin le_top), le_antisymm (le_top : b ≤ ⊤) (hmin le_top)]


/-- An object has length zero exactly when it is a zero object. -/
theorem objectLength_eq_zero_iff_isZero {X : C} : objectLength X = 0 ↔ IsZero X :=
  objectLength_eq_zero_iff_isZero_of_finiteDimensionalOrder


/-- The length of an object that is not zero is positive. -/
theorem objectLength_pos_of_not_isZero {X : C} (h : ¬ IsZero X) : 0 < objectLength X :=
  Nat.pos_of_ne_zero fun hz => h (objectLength_eq_zero_iff_isZero.mp hz)


private theorem map_pullback_of_le {X Y : C} (f : X ⟶ Y) [Mono f] {b : Subobject Y}
    (hb : b ≤ Subobject.mk f) :
    (Subobject.map f).obj ((Subobject.pullback f).obj b) = b := by
  have hfac : Subobject.ofLEMk b f hb ≫ f = b.arrow := Subobject.ofLEMk_comp hb
  set a₁ : Subobject X := Subobject.mk (Subobject.ofLEMk b f hb) with ha₁
  have hb_eq : (Subobject.map f).obj a₁ = b := by
    rw [ha₁, Subobject.map_mk,
      Subobject.mk_eq_mk_of_comm _ b.arrow (Iso.refl _) (by simp [hfac]), Subobject.mk_arrow]
  calc (Subobject.map f).obj ((Subobject.pullback f).obj b)
      = (Subobject.map f).obj ((Subobject.pullback f).obj ((Subobject.map f).obj a₁)) := by
        rw [hb_eq]
    _ = (Subobject.map f).obj a₁ := by rw [Subobject.pullback_map_self]
    _ = b := hb_eq


private theorem height_mk_eq_height_top {X Y : C} (f : X ⟶ Y) [Mono f] :
    Order.height (Subobject.mk f : Subobject Y) = Order.height (⊤ : Subobject X) := by
  have hmono : Monotone (fun a : Subobject X => (Subobject.map f).obj a) :=
    fun a b h => leOfHom ((Subobject.map f).map (homOfLE h))
  have hsm : StrictMono (fun a : Subobject X => (Subobject.map f).obj a) :=
    hmono.strictMono_of_injective (Subobject.map_obj_injective f)
  have hcond : ∀ (a : Subobject X) (b : Subobject Y),
      b < (Subobject.map f).obj a → ∃ a', a' < a ∧ (Subobject.map f).obj a' = b := by
    intro a b hba
    have hble : b ≤ Subobject.mk f := by
      refine hba.le.trans ?_
      have h : (Subobject.map f).obj a ≤ (Subobject.map f).obj ⊤ := hmono (le_top : a ≤ ⊤)
      rwa [Subobject.map_top] at h
    refine ⟨(Subobject.pullback f).obj b, lt_of_le_of_ne ?_ ?_, map_pullback_of_le f hble⟩
    · have h1 : (Subobject.pullback f).obj b
          ≤ (Subobject.pullback f).obj ((Subobject.map f).obj a) :=
        leOfHom ((Subobject.pullback f).map (homOfLE hba.le))
      rwa [Subobject.pullback_map_self] at h1
    · intro heq
      have hcontra : (Subobject.map f).obj a = b := by
        rw [← heq]; exact map_pullback_of_le f hble
      rw [hcontra] at hba
      exact lt_irrefl _ hba
  have hres := Order.height_eq_of_strictMono
    (fun a : Subobject X => (Subobject.map f).obj a) hsm hcond ⊤
  rw [Subobject.map_top] at hres
  exact hres.symm


private theorem height_add_coheight_le_height_top {α : Type*} [Preorder α] [OrderTop α]
    [FiniteDimensionalOrder α] (a : α) :
    Order.height a + Order.coheight a ≤ Order.height (⊤ : α) := by
  have hh : Order.height a ≠ ⊤ := by
    have hlt : Order.height a < ⊤ := by
      rw [← WithBot.coe_lt_coe]
      apply lt_of_le_of_lt (Order.height_le_krullDim a)
      simpa using Order.krullDim_ne_top_of_finiteDimensionalOrder.lt_top
    exact hlt.ne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hh
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Order.coheight_lt_top a).ne
  obtain ⟨p₁, hlast, hlen₁⟩ := Order.exists_series_of_height_eq_coe a hn.symm
  obtain ⟨p₂, hhead, hlen₂⟩ := Order.exists_series_of_coheight_eq_coe a hm.symm
  have hconnect : p₁.last = p₂.head := by rw [hlast, hhead]
  have hsl : (p₁.smash p₂ hconnect).length = p₁.length + p₂.length := rfl
  have key : Order.height a + Order.coheight a = ((p₁.smash p₂ hconnect).length : ℕ∞) := by
    rw [← hn, ← hm, hsl, hlen₁, hlen₂, Nat.cast_add]
  rw [key]
  calc ((p₁.smash p₂ hconnect).length : ℕ∞)
      ≤ Order.height ((p₁.smash p₂ hconnect).last) := Order.length_le_height_last
    _ ≤ Order.height (⊤ : α) := Order.height_mono le_top


private theorem height_prod_le {α : Type*} {β : Type*} [Preorder α] [Preorder β] (a : α) (b : β) :
    Order.height ((a, b) : α × β) ≤ Order.height a + Order.height b := by
  apply Order.height_le
  intro p hlast
  suffices h : ∀ q : LTSeries (α × β),
      (q.length : ℕ∞) ≤ Order.height (q.last).1 + Order.height (q.last).2 by
    have hp := h p
    rw [hlast] at hp
    exact hp
  intro q
  induction q using RelSeries.inductionOn' with
  | singleton x => simp
  | snoc p x hx ih =>
    rw [RelSeries.snoc_length, RelSeries.last_snoc]
    have hx' : p.last < x := hx
    push_cast
    rcases Prod.lt_iff.mp hx' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · calc (p.length : ℕ∞) + 1
          ≤ (Order.height (p.last).1 + Order.height (p.last).2) + 1 := add_le_add ih le_rfl
        _ = (Order.height (p.last).1 + 1) + Order.height (p.last).2 := by rw [add_right_comm]
        _ ≤ Order.height x.1 + Order.height x.2 :=
              add_le_add (Order.height_add_one_le h1) (Order.height_mono h2)
    · calc (p.length : ℕ∞) + 1
          ≤ (Order.height (p.last).1 + Order.height (p.last).2) + 1 := add_le_add ih le_rfl
        _ = Order.height (p.last).1 + (Order.height (p.last).2 + 1) := by rw [add_assoc]
        _ ≤ Order.height x.1 + Order.height x.2 :=
              add_le_add (Order.height_mono h1) (Order.height_add_one_le h2)


private theorem pullback_bot_eq_kernelSubobject {Y Z : C} (g : Y ⟶ Z) :
    (Subobject.pullback g).obj ⊥ = kernelSubobject g := by
  have hsq := Subobject.isPullback g (⊥ : Subobject Z)
  apply le_antisymm
  · refine le_kernelSubobject _ _ ?_
    have hw : ((Subobject.pullback g).obj ⊥).arrow ≫ g
        = Subobject.pullbackπ g ⊥ ≫ (⊥ : Subobject Z).arrow := hsq.w.symm
    rw [hw, Subobject.bot_arrow, comp_zero]
  · refine Subobject.le_of_comm
      (hsq.lift (0 : (kernelSubobject g : C) ⟶ _) (kernelSubobject g).arrow ?_) ?_
    · simp [kernelSubobject_arrow_comp]
    · exact hsq.lift_snd _ _ _


private theorem imageSubobject_pullback_arrow_comp {Y Z : C} (g : Y ⟶ Z) [Epi g]
    (T : Subobject Z) :
    imageSubobject (((Subobject.pullback g).obj T).arrow ≫ g) = T := by
  have hsq := Subobject.isPullback g T
  haveI hπ : Epi (Subobject.pullbackπ g T) := Abelian.epi_fst_of_isLimit _ _ hsq.isLimit
  have hw : ((Subobject.pullback g).obj T).arrow ≫ g = Subobject.pullbackπ g T ≫ T.arrow :=
    hsq.w.symm
  rw [hw]
  have hle : imageSubobject (Subobject.pullbackπ g T ≫ T.arrow) ≤ imageSubobject T.arrow :=
    imageSubobject_comp_le _ _
  haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi _ _
  haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
  have heq : imageSubobject (Subobject.pullbackπ g T ≫ T.arrow) = imageSubobject T.arrow :=
    Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp [Subobject.ofLE_arrow])
  rw [heq, imageSubobject_mono, Subobject.mk_arrow]


private theorem height_top_le_coheight_kernel {S : ShortComplex C} (hS : S.ShortExact) :
    Order.height (⊤ : Subobject S.X₃)
      ≤ Order.coheight (kernelSubobject S.g : Subobject S.X₂) := by
  haveI := hS.epi_g
  have hmono : Monotone (fun T : Subobject S.X₃ => (Subobject.pullback S.g).obj T) :=
    fun a b h => leOfHom ((Subobject.pullback S.g).map (homOfLE h))
  have hinj : Function.Injective (fun T : Subobject S.X₃ => (Subobject.pullback S.g).obj T) := by
    intro T T' h
    have h2 : imageSubobject (((Subobject.pullback S.g).obj T).arrow ≫ S.g)
        = imageSubobject (((Subobject.pullback S.g).obj T').arrow ≫ S.g) :=
      congrArg (fun B : Subobject S.X₂ => imageSubobject (B.arrow ≫ S.g)) h
    rwa [imageSubobject_pullback_arrow_comp, imageSubobject_pullback_arrow_comp] at h2
  have hsm : StrictMono (fun T : Subobject S.X₃ => (Subobject.pullback S.g).obj T) :=
    hmono.strictMono_of_injective hinj
  have hkey : Order.coheight (⊥ : Subobject S.X₃)
      ≤ Order.coheight ((Subobject.pullback S.g).obj ⊥) :=
    Order.coheight_le_coheight_apply_of_strictMono _ hsm (⊥ : Subobject S.X₃)
  rw [pullback_bot_eq_kernelSubobject] at hkey
  have hbt : Order.height (⊤ : Subobject S.X₃) = Order.coheight (⊥ : Subobject S.X₃) := by
    have : (Order.height (⊤ : Subobject S.X₃) : WithBot ℕ∞)
        = (Order.coheight (⊥ : Subobject S.X₃) : WithBot ℕ∞) := by
      rw [Order.height_top_eq_krullDim, Order.coheight_bot_eq_krullDim]
    exact WithBot.coe_inj.mp this
  rwa [hbt]


private theorem height_top_add_le {S : ShortComplex C} (hS : S.ShortExact) :
    Order.height (⊤ : Subobject S.X₁) + Order.height (⊤ : Subobject S.X₃)
      ≤ Order.height (⊤ : Subobject S.X₂) := by
  haveI := hS.mono_f
  have hA : Subobject.mk S.f = kernelSubobject S.g :=
    (imageSubobject_mono S.f).symm.trans (S.exact_iff_image_eq_kernel.mp hS.exact)
  have hh : Order.height (kernelSubobject S.g : Subobject S.X₂)
      = Order.height (⊤ : Subobject S.X₁) := by rw [← hA, height_mk_eq_height_top S.f]
  calc Order.height (⊤ : Subobject S.X₁) + Order.height (⊤ : Subobject S.X₃)
      = Order.height (kernelSubobject S.g : Subobject S.X₂)
          + Order.height (⊤ : Subobject S.X₃) := by rw [hh]
    _ ≤ Order.height (kernelSubobject S.g : Subobject S.X₂)
          + Order.coheight (kernelSubobject S.g : Subobject S.X₂) :=
        add_le_add le_rfl (height_top_le_coheight_kernel hS)
    _ ≤ Order.height (⊤ : Subobject S.X₂) := height_add_coheight_le_height_top _


private theorem clength_add_le {S : ShortComplex C} (hS : S.ShortExact) :
    objectLength S.X₁ + objectLength S.X₃ ≤ objectLength S.X₂ := by
  have h1 : Order.height (⊤ : Subobject S.X₁) ≠ ⊤ := subobject_height_lt_top.ne
  have h3 : Order.height (⊤ : Subobject S.X₃) ≠ ⊤ := subobject_height_lt_top.ne
  have h2 : Order.height (⊤ : Subobject S.X₂) ≠ ⊤ := subobject_height_lt_top.ne
  simp only [objectLength]
  rw [← ENat.toNat_add h1 h3]
  exact ENat.toNat_le_toNat (height_top_add_le hS) h2


private theorem mem_pullback_obj {X Y : C} (f : X ⟶ Y) (y : Subobject Y) {x : X} {b : (y : C)}
    (h : y.arrow b = f x) :
    ∃ w : ((Subobject.pullback f).obj y : C), ((Subobject.pullback f).obj y).arrow w = x := by
  obtain ⟨s, _, hs2⟩ := Abelian.Pseudoelement.pseudo_pullback h
  refine ⟨(Subobject.isPullback f y).isoPullback.inv s, ?_⟩
  rw [← Abelian.Pseudoelement.comp_apply, IsPullback.isoPullback_inv_snd]
  exact hs2


private theorem Φ_reflecting {S : ShortComplex C} (hS : S.ShortExact) {A B : Subobject S.X₂}
    (hAB : A ≤ B) (h1 : (Subobject.pullback S.f).obj A = (Subobject.pullback S.f).obj B)
    (h2 : imageSubobject (A.arrow ≫ S.g) = imageSubobject (B.arrow ≫ S.g)) :
    B ≤ A := by
  haveI := hS.mono_f
  set ι : (A : C) ⟶ (B : C) := Subobject.ofLE A B hAB with hι
  haveI : Mono ι := mono_of_mono_fac (Subobject.ofLE_arrow hAB)
  -- It suffices to show `ι` is epi: then it is an iso and `B ≤ A`.
  suffices hEpi : Epi ι by
    haveI := hEpi
    haveI : IsIso ι := isIso_of_mono_of_epi ι
    exact Subobject.le_of_comm (inv ι)
      (by rw [← Subobject.ofLE_arrow hAB, IsIso.inv_hom_id_assoc])
  apply Abelian.Pseudoelement.epi_of_pseudo_surjective
  intro b
  -- Reduce `∃ a, ι a = b` to `∃ a, A.arrow a = B.arrow b`.
  suffices hh : ∃ a, A.arrow a = B.arrow b by
    obtain ⟨a, ha⟩ := hh
    refine ⟨a, ?_⟩
    apply Abelian.Pseudoelement.pseudo_injective_of_mono B.arrow
    rw [← Abelian.Pseudoelement.comp_apply, hι, Subobject.ofLE_arrow, ha]
  -- Step 1: `g (B.arrow b)` lies in `image (A.arrow ≫ g)`; extract `a₀`.
  have hle : imageSubobject (B.arrow ≫ S.g) ≤ imageSubobject (A.arrow ≫ S.g) := h2.ge
  obtain ⟨a₀, ha₀⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi
    (factorThruImageSubobject (A.arrow ≫ S.g))
    (Subobject.ofLE _ _ hle (factorThruImageSubobject (B.arrow ≫ S.g) b))
  have hgeq : S.g (A.arrow a₀) = S.g (B.arrow b) := by
    have lhs : (A.arrow ≫ S.g) a₀
        = (imageSubobject (A.arrow ≫ S.g)).arrow
            (factorThruImageSubobject (A.arrow ≫ S.g) a₀) := by
      rw [← Abelian.Pseudoelement.comp_apply, imageSubobject_arrow_comp]
    have rhs : (B.arrow ≫ S.g) b
        = (imageSubobject (B.arrow ≫ S.g)).arrow
            (factorThruImageSubobject (B.arrow ≫ S.g) b) := by
      rw [← Abelian.Pseudoelement.comp_apply, imageSubobject_arrow_comp]
    have e : (A.arrow ≫ S.g) a₀ = (B.arrow ≫ S.g) b := by
      rw [lhs, rhs, ha₀, ← Abelian.Pseudoelement.comp_apply, Subobject.ofLE_arrow]
    rwa [Abelian.Pseudoelement.comp_apply, Abelian.Pseudoelement.comp_apply] at e
  -- Step 2: form the "difference" `z` with `g z = 0`.
  obtain ⟨z, hz0, hzprop⟩ :=
    Abelian.Pseudoelement.sub_of_eq_image S.g (B.arrow b) (A.arrow a₀) hgeq.symm
  -- `cokernel.π A.arrow` kills `A.arrow a₀`.
  have hcAA0 : (cokernel.π A.arrow) (A.arrow a₀) = 0 := by
    rw [← Abelian.Pseudoelement.comp_apply, cokernel.condition,
      Abelian.Pseudoelement.zero_apply]
  -- So `cokernel.π A.arrow (B.arrow b) = cokernel.π A.arrow z`.
  have hbz : (cokernel.π A.arrow) (B.arrow b) = (cokernel.π A.arrow) z :=
    (hzprop _ (cokernel.π A.arrow) hcAA0).symm
  -- Step 3: `z ∈ B`.
  have hcBA0 : (cokernel.π B.arrow) (A.arrow a₀) = 0 := by
    have hAa : A.arrow a₀ = B.arrow (ι a₀) := by
      rw [← Abelian.Pseudoelement.comp_apply, hι, Subobject.ofLE_arrow]
    rw [hAa, ← Abelian.Pseudoelement.comp_apply, cokernel.condition,
      Abelian.Pseudoelement.zero_apply]
  have hzB : (cokernel.π B.arrow) z = 0 := by
    rw [hzprop _ (cokernel.π B.arrow) hcBA0, ← Abelian.Pseudoelement.comp_apply,
      cokernel.condition, Abelian.Pseudoelement.zero_apply]
  obtain ⟨b', hb'⟩ := Abelian.Pseudoelement.pseudo_exact_of_exact
    (ShortComplex.cokernelSequence_exact B.arrow) z hzB
  -- Step 4: `z ∈ A`, using `g z = 0` (so `z ∈ im f`) and the preimage equality `h1`.
  have hcAz : (cokernel.π A.arrow) z = 0 := by
    obtain ⟨x₁, hx₁⟩ := Abelian.Pseudoelement.pseudo_exact_of_exact hS.exact z hz0
    have hcone : B.arrow b' = S.f x₁ := hb'.trans hx₁.symm
    obtain ⟨w, hw⟩ := mem_pullback_obj S.f B hcone
    have hw'arrow : ((Subobject.pullback S.f).obj A).arrow (Subobject.ofLE _ _ h1.ge w) = x₁ := by
      rw [← Abelian.Pseudoelement.comp_apply, Subobject.ofLE_arrow, hw]
    have ha' : A.arrow (Subobject.pullbackπ S.f A (Subobject.ofLE _ _ h1.ge w)) = z := by
      rw [← Abelian.Pseudoelement.comp_apply, (Subobject.isPullback S.f A).w,
        Abelian.Pseudoelement.comp_apply, hw'arrow, hx₁]
    rw [← ha', ← Abelian.Pseudoelement.comp_apply, cokernel.condition,
      Abelian.Pseudoelement.zero_apply]
  -- Conclude `B.arrow b ∈ A`.
  have hfin : (cokernel.π A.arrow) (B.arrow b) = 0 := by rw [hbz, hcAz]
  exact Abelian.Pseudoelement.pseudo_exact_of_exact
    (ShortComplex.cokernelSequence_exact A.arrow) (B.arrow b) hfin


private theorem clength_le_add {S : ShortComplex C} (hS : S.ShortExact) :
    objectLength S.X₂ ≤ objectLength S.X₁ + objectLength S.X₃ := by
  haveI := hS.mono_f
  set Φ : Subobject S.X₂ → Subobject S.X₁ × Subobject S.X₃ :=
    fun B => ((Subobject.pullback S.f).obj B, imageSubobject (B.arrow ≫ S.g)) with hΦ
  have hmono : Monotone Φ := by
    intro A B hAB
    refine Prod.mk_le_mk.mpr ⟨leOfHom ((Subobject.pullback S.f).map (homOfLE hAB)), ?_⟩
    have he : A.arrow ≫ S.g = Subobject.ofLE A B hAB ≫ (B.arrow ≫ S.g) := by
      rw [← Category.assoc, Subobject.ofLE_arrow]
    rw [he]
    exact imageSubobject_comp_le _ _
  have hsm : StrictMono Φ := by
    intro A B hAB
    refine lt_of_le_of_ne (hmono hAB.le) ?_
    intro hEq
    exact absurd (le_antisymm hAB.le
      (Φ_reflecting hS hAB.le (congrArg Prod.fst hEq) (congrArg Prod.snd hEq))) (ne_of_lt hAB)
  have hheight : Order.height (⊤ : Subobject S.X₂)
      ≤ Order.height (⊤ : Subobject S.X₁) + Order.height (⊤ : Subobject S.X₃) :=
    calc Order.height (⊤ : Subobject S.X₂)
        ≤ Order.height (Φ ⊤) := Order.height_le_height_apply_of_strictMono Φ hsm ⊤
      _ ≤ Order.height (Φ ⊤).1 + Order.height (Φ ⊤).2 := height_prod_le _ _
      _ ≤ Order.height (⊤ : Subobject S.X₁) + Order.height (⊤ : Subobject S.X₃) :=
          add_le_add (Order.height_mono le_top) (Order.height_mono le_top)
  have h1 : Order.height (⊤ : Subobject S.X₁) ≠ ⊤ := subobject_height_lt_top.ne
  have h3 : Order.height (⊤ : Subobject S.X₃) ≠ ⊤ := subobject_height_lt_top.ne
  simp only [objectLength]
  rw [← ENat.toNat_add h1 h3]
  exact ENat.toNat_le_toNat hheight (WithTop.add_ne_top.mpr ⟨h1, h3⟩)


/-- Object length is additive across a short exact sequence. -/
theorem objectLength_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    objectLength S.X₂ = objectLength S.X₁ + objectLength S.X₃ :=
  le_antisymm (clength_le_add hS) (clength_add_le hS)


/-- The length of a binary biproduct is the sum of the lengths of its two objects. -/
theorem objectLength_biprod (Y Z : C) : objectLength (Y ⊞ Z) = objectLength Y + objectLength Z := by
  have spl :
      (ShortComplex.mk (biprod.inl : Y ⟶ Y ⊞ Z) (biprod.snd : Y ⊞ Z ⟶ Z) (by simp)).Splitting :=
    { r := biprod.fst, s := biprod.inr, f_r := by simp, s_g := by simp, id := biprod.total }
  exact objectLength_shortExact spl.shortExact

/-! ## Monotonicity of `clength` over the subobject lattice

For an inclusion of subobjects `A ≤ B` of a fixed `X`, the canonical short exact sequence
`0 → (A : C) → (B : C) → (B/A) → 0` (with `(A : C) → (B : C)` the inclusion `Subobject.ofLE`
and `B/A` its cokernel) together with `clength_additive` gives `clength (A : C) ≤ clength (B : C)`,
strictly so when `A < B` (then `B/A` is nonzero, so has positive length). This is the order-theoretic
input that makes `clength` a well-founded induction measure on `Subobject X`. -/


/-- The length of the larger subobject is the length of the smaller one plus that of the induced cokernel. -/
theorem objectLength_eq_add_cokernel_of_subobject_le {X : C} {A B : Subobject X} (h : A ≤ B) :
    objectLength (B : C) = objectLength (A : C) + objectLength (cokernel (Subobject.ofLE A B h)) := by
  have hSE : (ShortComplex.cokernelSequence (Subobject.ofLE A B h)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
      (inferInstanceAs (Mono (Subobject.ofLE A B h))) inferInstance
  have hadd := objectLength_shortExact hSE
  simpa using hadd


/-- Inclusion of subobjects gives an inequality between the lengths of their underlying objects. -/
theorem objectLength_le_of_subobject_le {X : C} {A B : Subobject X} (h : A ≤ B) :
    objectLength (A : C) ≤ objectLength (B : C) := by
  rw [objectLength_eq_add_cokernel_of_subobject_le h]; exact Nat.le_add_right _ _


/-- A strict inclusion of subobjects gives a strict inequality between the lengths of their underlying objects. -/
theorem objectLength_lt_of_subobject_lt {X : C} {A B : Subobject X} (h : A < B) :
    objectLength (A : C) < objectLength (B : C) := by
  rw [objectLength_eq_add_cokernel_of_subobject_le h.le]
  have hpos : 0 < objectLength (cokernel (Subobject.ofLE A B h.le)) := by
    apply objectLength_pos_of_not_isZero
    intro hZ
    -- A zero cokernel makes `ofLE A B h.le` epi, hence (it is also mono) an iso, forcing `B ≤ A`.
    have hπ : cokernel.π (Subobject.ofLE A B h.le) = 0 := hZ.eq_zero_of_tgt _
    haveI : Epi (Subobject.ofLE A B h.le) := Abelian.epi_of_cokernel_π_eq_zero _ hπ
    haveI : IsIso (Subobject.ofLE A B h.le) := isIso_of_mono_of_epi _
    have hBA : B ≤ A :=
      Subobject.le_of_comm (inv (Subobject.ofLE A B h.le)) (by
        rw [← Subobject.ofLE_arrow h.le, IsIso.inv_hom_id_assoc])
    exact absurd (le_antisymm h.le hBA) (ne_of_lt h)
  omega

/-! ## Chain conditions on the subobject lattice

Strict monotonicity of `clength` makes the strict order on `Subobject X` a subrelation of the
pullback of `<` on `ℕ`, hence well-founded: descending chains of subobjects stabilise. Ascending
chains stabilise too, because `clength` is additionally *bounded* (by the length of the underlying
object of `⊤`), so the non-decreasing `ℕ`-sequence `clength ∘ a` is eventually constant and strict
monotonicity then pins the chain itself. Both directions are what Fitting's lemma consumes:
the descending image chain `im (f^n)` and the ascending kernel chain `ker (f^n)`. -/


/-- Strict descent among subobjects is well-founded. -/
instance subobject_wellFoundedLT {X : C} : WellFoundedLT (Subobject X) :=
  ⟨Subrelation.wf (fun {_ _} h => objectLength_lt_of_subobject_lt h) (InvImage.wf _ wellFounded_lt)⟩


/-- A decreasing sequence of subobjects eventually stops changing. -/
theorem antitone_subobject_sequence_eventually_constant {X : C} {a : ℕ → Subobject X}
    (ha : Antitone a) : ∃ N, ∀ m ≥ N, a m = a N :=
  (WellFoundedLT.antitone_chain_condition ha).imp fun _ h m hm => (h m hm).symm


private theorem nat_eventually_constant_of_monotone_of_bddAbove {f : ℕ → ℕ}
    (hf : Monotone f) {B : ℕ} (hB : ∀ n, f n ≤ B) : ∃ N, ∀ m ≥ N, f m = f N := by
  have hne : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
  have hbdd : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem hne hbdd
  refine ⟨N, fun m hm => le_antisymm ?_ (hf hm)⟩
  rw [hN]; exact le_csSup hbdd ⟨m, rfl⟩


/-- An increasing sequence of subobjects eventually stops changing. -/
theorem monotone_subobject_sequence_eventually_constant {X : C} {a : ℕ → Subobject X}
    (ha : Monotone a) : ∃ N, ∀ m ≥ N, a m = a N := by
  obtain ⟨N, hN⟩ := nat_eventually_constant_of_monotone_of_bddAbove
    (f := fun n => objectLength (a n : C)) (fun _ _ h => objectLength_le_of_subobject_le (ha h))
    (B := objectLength ((⊤ : Subobject X) : C)) (fun _ => objectLength_le_of_subobject_le le_top)
  refine ⟨N, fun m hm => ?_⟩
  rcases (ha hm).lt_or_eq with hlt | heq
  · exact absurd (hN m hm) (by have := objectLength_lt_of_subobject_lt hlt; omega)
  · exact heq.symm

/-! ## Image and kernel chains of an endomorphism

The descending image chain `im (f^n)` and ascending kernel chain `ker (f^n)` of an endomorphism
`f : End X` both stabilise, directly from the chain conditions above. These are the finite-length
inputs that Fitting's lemma (`fitting_decomposition`) consumes. -/


/-- Images of increasing powers of an endomorphism form a decreasing subobject sequence. -/
theorem imageSubobject_pow_antitone {X : C} (f : End X) :
    Antitone (fun n => imageSubobject ((f : X ⟶ X) ^ n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hcomp : (f : X ⟶ X) ^ (n + 1) = (f : X ⟶ X) ≫ ((f : X ⟶ X) ^ n) := by rw [pow_succ]; rfl
  change imageSubobject ((f : X ⟶ X) ^ (n + 1)) ≤ imageSubobject ((f : X ⟶ X) ^ n)
  rw [hcomp]
  exact imageSubobject_comp_le _ _


/-- Kernels of increasing powers of an endomorphism form an increasing subobject sequence. -/
theorem kernelSubobject_pow_monotone {X : C} (f : End X) :
    Monotone (fun n => kernelSubobject ((f : X ⟶ X) ^ n)) := by
  apply monotone_nat_of_le_succ
  intro n
  have hcomp : (f : X ⟶ X) ^ (n + 1) = ((f : X ⟶ X) ^ n) ≫ (f : X ⟶ X) := by rw [pow_succ']; rfl
  change kernelSubobject ((f : X ⟶ X) ^ n) ≤ kernelSubobject ((f : X ⟶ X) ^ (n + 1))
  rw [hcomp]
  exact kernelSubobject_comp_le _ _


/-- The image subobjects of successive powers of an endomorphism eventually stabilize. -/
theorem imageSubobject_pow_eventually_constant {X : C} (f : End X) :
    ∃ N, ∀ m ≥ N, imageSubobject ((f : X ⟶ X) ^ m) = imageSubobject ((f : X ⟶ X) ^ N) :=
  antitone_subobject_sequence_eventually_constant (imageSubobject_pow_antitone f)


/-- The kernel subobjects of successive powers of an endomorphism eventually stabilize. -/
theorem kernelSubobject_pow_eventually_constant {X : C} (f : End X) :
    ∃ N, ∀ m ≥ N, kernelSubobject ((f : X ⟶ X) ^ m) = kernelSubobject ((f : X ⟶ X) ^ N) :=
  monotone_subobject_sequence_eventually_constant (kernelSubobject_pow_monotone f)


/-- Some positive power has both image and kernel subobjects unchanged after doubling its exponent. -/
theorem exists_pow_image_kernel_stabilization {X : C} (f : End X) :
    ∃ n, 0 < n ∧
      imageSubobject ((f : X ⟶ X) ^ n) = imageSubobject ((f : X ⟶ X) ^ (2 * n)) ∧
      kernelSubobject ((f : X ⟶ X) ^ n) = kernelSubobject ((f : X ⟶ X) ^ (2 * n)) := by
  obtain ⟨N₁, hN₁⟩ := imageSubobject_pow_eventually_constant f
  obtain ⟨N₂, hN₂⟩ := kernelSubobject_pow_eventually_constant f
  refine ⟨max N₁ N₂ + 1, Nat.succ_pos _, ?_, ?_⟩
  · rw [hN₁ (2 * (max N₁ N₂ + 1)) (by omega), hN₁ (max N₁ N₂ + 1) (by omega)]
  · rw [hN₂ (2 * (max N₁ N₂ + 1)) (by omega), hN₂ (max N₁ N₂ + 1) (by omega)]

/-! ## Fitting stabilisation of the image restriction

The combined image/kernel stabilisation upgrades to the statement Fitting's lemma actually consumes:
at the stabilising power `n`, the image restriction
`g' := image.ι (fⁿ) ≫ factorThruImage (fⁿ) : image (fⁿ) ⟶ image (fⁿ)` is an isomorphism. We argue
on pseudoelements: `g'` is injective because `im (fⁿ) = im (f^{2n})` and `ker (fⁿ) = ker (f^{2n})`
force any element killed by `g'` to vanish, and surjective because `im (fⁿ) = im (f^{2n})` lets every
element of `im (fⁿ)` be hit. -/


private theorem exact_kernelSubobject_arrow {Y Z : C} (g : Y ⟶ Z) :
    (ShortComplex.mk (kernelSubobject g).arrow g (kernelSubobject_arrow_comp g)).Exact := by
  rw [ShortComplex.exact_iff_image_eq_kernel]
  change imageSubobject (kernelSubobject g).arrow = kernelSubobject g
  rw [imageSubobject_mono, Subobject.mk_arrow]


/-- For some positive power, its image inclusion followed by its factor-through-image map is an isomorphism. -/
theorem exists_pow_image_inclusion_comp_factorThruImage_isIso {X : C} (f : End X) :
    ∃ n, 0 < n ∧ IsIso (Abelian.image.ι ((f : X ⟶ X) ^ n) ≫
      Abelian.factorThruImage ((f : X ⟶ X) ^ n)) := by
  obtain ⟨n, hn, him, hker⟩ := exists_pow_image_kernel_stabilization f
  refine ⟨n, hn, ?_⟩
  set g : X ⟶ X := (f : X ⟶ X) ^ n with hg
  set g2 : X ⟶ X := (f : X ⟶ X) ^ (2 * n) with hg2
  set i := Abelian.image.ι g with hi
  set p := Abelian.factorThruImage g with hp
  have hpi : p ≫ i = g := Abelian.image.fac g
  -- `i ∘ p` is the identity-up-to-`g`: `i (p y) = g y`.
  have hint : ∀ y : X, i (p y) = g y := fun y => by
    rw [← Abelian.Pseudoelement.comp_apply, hpi]
  -- `g ≫ g = g2`, i.e. `f^n ≫ f^n = f^{2n}`.
  have hsq : g ≫ g = g2 := by rw [hg, hg2, two_mul, pow_add, End.mul_def]
  -- KER stabilisation on pseudoelements: `g2 w = 0 → g w = 0`.
  have hKER : ∀ w : X, g2 w = 0 → g w = 0 := by
    intro w hw
    obtain ⟨a, ha⟩ := Abelian.Pseudoelement.pseudo_exact_of_exact
      (exact_kernelSubobject_arrow g2) w hw
    have hle : kernelSubobject g2 ≤ kernelSubobject g := hker.ge
    have harrow : (kernelSubobject g2).arrow ≫ g = 0 := by
      rw [← Subobject.ofLE_arrow hle, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    rw [← ha, ← Abelian.Pseudoelement.comp_apply, harrow, Abelian.Pseudoelement.zero_apply]
  -- IMAGE stabilisation on pseudoelements: `im g ⊆ im g2`.
  have hIM : ∀ x u : X, g u = x → ∃ z, g2 z = x := by
    intro x u hxu
    have hle : imageSubobject g ≤ imageSubobject g2 := him.le
    have hx2 : x = (imageSubobject g2).arrow
        (Subobject.ofLE _ _ hle (factorThruImageSubobject g u)) := by
      rw [← Abelian.Pseudoelement.comp_apply, Subobject.ofLE_arrow,
        ← Abelian.Pseudoelement.comp_apply, imageSubobject_arrow_comp]
      exact hxu.symm
    obtain ⟨z, hz⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi
      (factorThruImageSubobject g2)
      (Subobject.ofLE _ _ hle (factorThruImageSubobject g u))
    exact ⟨z, by rw [hx2, ← hz, ← Abelian.Pseudoelement.comp_apply, imageSubobject_arrow_comp]⟩
  -- `i ≫ p` is mono and epi, hence iso.
  haveI hmono : Mono (i ≫ p) := by
    apply Abelian.Pseudoelement.mono_of_zero_of_map_zero
    intro a ha
    obtain ⟨w, hw⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi p a
    have hia : i a = g w := by rw [← hw, hint]
    have hpia : p (i a) = 0 := by rw [← Abelian.Pseudoelement.comp_apply]; exact ha
    have hFn_ia : g (i a) = 0 := by
      rw [← hint (i a), hpia, Abelian.Pseudoelement.apply_zero]
    have hw2n : g2 w = 0 := by
      rw [← hsq, Abelian.Pseudoelement.comp_apply, ← hia, hFn_ia]
    have hia0 : i a = 0 := by rw [hia, hKER w hw2n]
    exact Abelian.Pseudoelement.zero_of_map_zero i
      (Abelian.Pseudoelement.pseudo_injective_of_mono i) a hia0
  haveI hepi : Epi (i ≫ p) := by
    apply Abelian.Pseudoelement.epi_of_pseudo_surjective
    intro a
    obtain ⟨w, hw⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi p a
    have hia : i a = g w := by rw [← hw, hint]
    obtain ⟨z, hz⟩ := hIM (i a) w hia.symm
    refine ⟨p z, ?_⟩
    apply Abelian.Pseudoelement.pseudo_injective_of_mono i
    rw [Abelian.Pseudoelement.comp_apply, hint, hint, ← Abelian.Pseudoelement.comp_apply, hsq, hz]
  exact isIso_of_mono_of_epi (i ≫ p)

end RepresentationTheory.CategoryTheory.Abelian.SubobjectLength

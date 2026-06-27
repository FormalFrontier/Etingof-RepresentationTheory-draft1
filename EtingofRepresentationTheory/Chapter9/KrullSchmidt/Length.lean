import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import EtingofRepresentationTheory.Chapter9.Introduction_9_6
import Mathlib.Order.KrullDimension
import Mathlib.Order.OrderIsoNat
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Composition length for finite abelian categories (Krull–Schmidt, link 1/5)

This file introduces a `ℕ`-valued **composition length** `Etingof.clength X` for objects of a
finite abelian category, together with the additivity property that every later Krull–Schmidt
step (existence of a decomposition into indecomposables, Fitting's lemma) uses as its
well-founded induction measure.

## Design

`clength X` is defined as the order-theoretic **height** of the top element of the subobject
lattice `CategoryTheory.Subobject X`:

```
clength X = (Order.height (⊤ : Subobject X)).toNat.
```

For a finite-length object this height is finite and equals the length of any composition
series, by the Jordan–Hölder theorem applied to the (modular) subobject lattice. The definition
above is *total* — it returns a real `ℕ` for every object — so it can serve as the carrier of the
API even before the finiteness/additivity content is in place. `Order.height` lives in `ℕ∞`, and
`.toNat` sends `⊤` (the not-finite-length case, which does not occur in a finite abelian category)
to `0`.

## Mathlib correspondence and the additivity crux

Mathlib develops Jordan–Hölder only abstractly (`Mathlib/Order/JordanHolder.lean`,
`CompositionSeries`, `CompositionSeries.jordan_holder`) and concretely for `Submodule R M`
(`JordanHolderModule.instJordanHolderLattice`). For the subobject lattice of an abelian category
it has **neither** a `JordanHolderLattice` instance, **nor** the `IsModularLattice (Subobject X)`
instance, **nor** the categorical second isomorphism theorem `(A ⊔ B)/A ≅ B/(A ⊓ B)` that such an
instance needs. The Stacks-project route (tag `0FCK`) for categorical Jordan–Hölder is flagged as
future work in `Mathlib/CategoryTheory/Noetherian.lean`.

Consequently the **additivity** of `clength` over short exact sequences,

```
clength S.X₂ = clength S.X₁ + clength S.X₃,
```

is the genuine categorical Jordan–Hölder content and is the hard part of this link. It is now
**proved** (`clength_additive`), sorry-free, as `le_antisymm` of the two one-sided bounds:
`clength_add_le` (the modularity-free lower bound, via the down-interval isomorphism
`height_mk_eq_height_top` and the epi-side inequality `height_top_le_coheight_kernel`) and
`clength_le_add` (the Schreier-refinement upper bound, via the order-reflecting embedding
`Subobject X₂ ↪ Subobject X₁ × Subobject X₃` of `Φ_reflecting` and the product-order height bound
`height_prod_le`). Finiteness of the height in a finite abelian category comes from the §9.6
standing assumption recorded as `FiniteDimensionalOrder (Subobject X)`. The
`clength_eq_zero` characterisation is likewise proved in both directions.

This top-down split lets the downstream consumers (existence-of-decomposition and Fitting's-lemma
sub-issues of #5153) build against the final `clength` API immediately.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof

variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C]

attribute [local instance] CategoryTheory.Abelian.Pseudoelement.objectToSort
  CategoryTheory.Abelian.Pseudoelement.homToFun CategoryTheory.Abelian.Pseudoelement.overToSort

/-- The **composition length** of an object `X` of a finite abelian category: the height of the
top element of the subobject lattice `Subobject X`. For a finite-length object this equals the
length of any composition series (well-defined by the Jordan–Hölder theorem). The definition is
total, returning `0` on the not-finite-length case (which does not occur in a finite abelian
category). -/
noncomputable def clength (X : C) : ℕ :=
  (Order.height (⊤ : Subobject X)).toNat

/-- A zero object has composition length `0`: its subobject lattice is a singleton, so the top
element is a minimum and has height `0`. -/
theorem clength_eq_zero_of_isZero {X : C} (h : IsZero X) : clength X = 0 := by
  have : Subsingleton (Subobject X) := Subobject.subsingleton_of_isZero h
  have hmin : IsMin (⊤ : Subobject X) := fun b _ => le_of_eq (Subsingleton.elim _ _)
  simp only [clength, Order.height_eq_zero.2 hmin, ENat.toNat_zero]

/-- A **simple** object has composition length `1`: its subobject lattice is a two-element chain
`⊥ < ⊤` (`IsSimpleOrder (Subobject X)`), so the top element covers the bottom and its height is `1`.
This is the length-`1` base case of the Jordan–Hölder count: the value `clength_additive` returns
on the simple quotients of a composition series. -/
theorem clength_simple {X : C} (h : Simple X) : clength X = 1 := by
  haveI : IsSimpleOrder (Subobject X) := (simple_iff_subobject_isSimpleOrder X).mp h
  have hheight : Order.height (⊤ : Subobject X) = 1 := by
    refine le_antisymm (Order.height_le_coe_iff.mpr ?_) ?_
    · intro y hy
      have hy0 : y = ⊥ := (IsSimpleOrder.eq_bot_or_eq_top y).resolve_right (ne_of_lt hy)
      subst hy0
      simp [Order.height_eq_zero.mpr isMin_bot]
    · have := Order.height_add_one_le (bot_lt_top : (⊥ : Subobject X) < ⊤)
      simpa [Order.height_eq_zero.mpr isMin_bot] using this
  simp [clength, hheight]

/-- The subobject lattice of a **zero object** is finite-dimensional as an order: it is a
singleton, hence `Unique`. This is the base case of the finite-length induction that routes the
§9.6 standing assumption ("every object has finite length") into the `clength` API. -/
theorem finiteDimensionalOrder_subobject_of_isZero {X : C} (h : IsZero X) :
    FiniteDimensionalOrder (Subobject X) := by
  haveI := Subobject.subsingleton_of_isZero h
  haveI : Nonempty (Subobject X) := ⟨⊤⟩
  haveI : Unique (Subobject X) := Unique.mk' _
  infer_instance

/-- The height of `⊤ : Subobject X` is finite whenever the subobject lattice is finite-dimensional
as an order (the order-theoretic form of "`X` has finite length"). Mirrors Mathlib's
`Order.coheight_lt_top`. -/
theorem height_top_lt_top {X : C} [FiniteDimensionalOrder (Subobject X)] :
    Order.height (⊤ : Subobject X) < ⊤ := by
  rw [← WithBot.coe_lt_coe]
  apply lt_of_le_of_lt (Order.height_le_krullDim (⊤ : Subobject X))
  simpa using (Order.krullDim_ne_top_of_finiteDimensionalOrder
    (α := Subobject X)).lt_top

/-- **`clength_eq_zero_iff`, discharged under the finite-length hypothesis.** When the subobject
lattice of `X` is finite-dimensional as an order — the order-theoretic form of the §9.6 standing
assumption that every object has finite length — composition length `0` characterises the zero
object in *both* directions. This is the honest content of the `→` direction of
`clength_eq_zero_iff`: it needs exactly that `Order.height (⊤ : Subobject X)` is finite (here
`height_top_lt_top`), so that `clength X = 0` forces `Order.height ⊤ = 0`, i.e. `⊤` is minimal and
`Subobject X` is a singleton. The unconditional `clength_eq_zero_iff` below then follows the moment
that finiteness is available from the ambient category; see #5324 for the wiring. -/
theorem clength_eq_zero_iff_of_finiteDimensionalOrder {X : C}
    [FiniteDimensionalOrder (Subobject X)] : clength X = 0 ↔ IsZero X := by
  refine ⟨fun h => ?_, clength_eq_zero_of_isZero⟩
  have h0 : Order.height (⊤ : Subobject X) = 0 := by
    rw [clength, ENat.toNat_eq_zero] at h
    exact h.resolve_right (ne_of_lt height_top_lt_top)
  have hmin : IsMin (⊤ : Subobject X) := Order.height_eq_zero.mp h0
  by_contra hX
  haveI := Subobject.nontrivial_of_not_isZero hX
  refine not_subsingleton (Subobject X) ⟨fun a b => ?_⟩
  rw [le_antisymm (le_top : a ≤ ⊤) (hmin le_top), le_antisymm (le_top : b ≤ ⊤) (hmin le_top)]

/-- An object has composition length `0` iff it is a zero object.

The `←` direction is `clength_eq_zero_of_isZero`. The `→` direction needs that the height of
`⊤ : Subobject X` is *finite* in a finite abelian category (`Order.height ... ≠ ⊤`); only then does
`(Order.height ⊤).toNat = 0` force `Order.height ⊤ = 0`, i.e. `X` zero (via
`Subobject.nontrivial_of_not_isZero`). That finiteness is the same categorical Jordan–Hölder input
as `clength_additive`; see the module doc.

**Finiteness routing (#5324).** This finiteness is *not* derivable from the bare data of an abelian
category with enough projectives and finitely many simples: that data does **not** force every
object to have finite length. (Concretely, the category of all modules over `k[x]/(x²)` has one
simple `k` and enough projectives yet has infinite-length objects, for which `clength = 0` while the
object is nonzero, falsifying the `→` direction.) The missing ingredient is the §9.6
finite-length standing assumption, which `Etingof.IsFiniteAbelianCategory` now records
order-theoretically as `FiniteDimensionalOrder (Subobject X)` for every object `X` (see
`Definition9_6_1.lean`). That instance is in scope here, so the unconditional statement follows
immediately from `clength_eq_zero_iff_of_finiteDimensionalOrder`, whose proof is the honest `→`
math. -/
theorem clength_eq_zero_iff {X : C} : clength X = 0 ↔ IsZero X :=
  clength_eq_zero_iff_of_finiteDimensionalOrder

/-- A nonzero object has positive composition length.

This is the contrapositive of `clength_eq_zero_iff`: `0 < clength X ↔ clength X ≠ 0 ↔ ¬ IsZero X`.
All of its finiteness content is therefore concentrated in `clength_eq_zero_iff`. -/
theorem clength_pos_of_not_isZero {X : C} (h : ¬ IsZero X) : 0 < clength X :=
  Nat.pos_of_ne_zero fun hz => h (clength_eq_zero_iff.mp hz)

/-- For a mono `f : X ⟶ Y` and a subobject `b ≤ Subobject.mk f`, applying `map f` to the pullback
of `b` along `f` recovers `b`. Together with `Subobject.pullback_map_self` this exhibits `map f`
and `pullback f` as mutually inverse between `Subobject X` and the down-set `{b | b ≤ mk f}` of
`Subobject Y`. -/
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

/-- **Down-interval isomorphism.** For a mono `f : X ⟶ Y`, the height of the subobject
`Subobject.mk f` of `Y` equals the height of `⊤ : Subobject X`. Indeed `map f` is a strict-monotone
order isomorphism of `Subobject X` onto the down-set `{b | b ≤ mk f}`, so it preserves heights
(`height_eq_of_strictMono`) and carries `⊤` to `mk f`. This is the `[⊥, mk f] ≅ Subobject X` half
of categorical additivity. -/
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

/-- In a finite-dimensional order with a top element, the height of any element plus its coheight is
bounded by the height of the top: concatenate (`RelSeries.smash`) a maximal strictly increasing
chain ending at `a` with one starting at `a`; the result is a chain ending below `⊤`. This needs
**no modularity** and is the order-theoretic input to the lower bound
`clength X₁ + clength X₃ ≤ clength X₂` for a short exact sequence (with `a` the image of `X₁`
inside `X₂`). -/
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

/-- **Product-order height bound.** In a product of preorders the height of a pair is at most the
sum of the heights of its coordinates. A strictly increasing chain ending at `(a, b)` grows by a
strict step in at least one coordinate at each link (`Prod.lt_iff`), so its length is bounded by the
heights of `a` and `b` together. This is the pure order-theoretic half of the categorical
Jordan–Hölder upper bound: composed with the order-reflecting embedding
`Subobject X₂ ↪ Subobject X₁ × Subobject X₃` it yields
`height ⊤(X₂) ≤ height ⊤(X₁) + height ⊤(X₃)`. -/
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

/-- Pulling the bottom subobject back along `g` recovers the kernel subobject: `g⁻¹(0) = ker g`.
The forward inclusion is `le_kernelSubobject` (the pullback arrow composes to `0`); the reverse
is the pullback universal property (`IsPullback.lift`) applied to the kernel inclusion and the zero
map into `⊥`. -/
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

/-- For an epimorphism `g` and a subobject `T` of the target, the image of the preimage `g⁻¹(T)`
under `g` is `T` again (`g(g⁻¹(T)) = T`). This is the section identity making `Subobject.pullback g`
injective. The pullback square `(pullback g T).arrow ≫ g = pullbackπ ≫ T.arrow` has `pullbackπ` epi
(`Abelian.epi_fst_of_isLimit`, pullback of the epi `g`), so the image of the composite equals the
image of the mono `T.arrow`, namely `T`. -/
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

/-- **Epi-side inequality for the lower bound.** For a short exact sequence
`0 → X₁ →ᶠ X₂ →ᵍ X₃ → 0`, the height of `⊤ : Subobject X₃` is at most the coheight of `ker g`
inside `X₂`. Indeed `Subobject.pullback g` is strictly monotone (injective by the section identity
`imageSubobject_pullback_arrow_comp`) and carries `⊥ : Subobject X₃` to `ker g`
(`pullback_bot_eq_kernelSubobject`), so a maximal chain rising from `⊥` in `Subobject X₃` transports
to one rising from `ker g` in `Subobject X₂`. -/
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

/-- **Lower bound (heights).** For a short exact sequence, the heights of the two ends sum to at
most the height of the middle: `height ⊤(X₁) + height ⊤(X₃) ≤ height ⊤(X₂)`. Combine the
down-interval isomorphism `height_mk_eq_height_top` (`height (mk f) = height ⊤(X₁)`, and
`mk f = ker g` by exactness), the epi-side inequality `height_top_le_coheight_kernel`
(`height ⊤(X₃) ≤ coheight (ker g)`), and the order lemma `height_add_coheight_le_height_top`. -/
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

/-- **Lower bound (lengths).** `clength X₁ + clength X₃ ≤ clength X₂` for a short exact sequence.
This is the `ℕ`-level form of `height_top_add_le`: the heights of all three subobject lattices are
finite (`height_top_lt_top`, from `FiniteDimensionalOrder`), so `ENat.toNat` is additive and
monotone across the inequality `height ⊤(X₁) + height ⊤(X₃) ≤ height ⊤(X₂)`. -/
private theorem clength_add_le {S : ShortComplex C} (hS : S.ShortExact) :
    clength S.X₁ + clength S.X₃ ≤ clength S.X₂ := by
  have h1 : Order.height (⊤ : Subobject S.X₁) ≠ ⊤ := height_top_lt_top.ne
  have h3 : Order.height (⊤ : Subobject S.X₃) ≠ ⊤ := height_top_lt_top.ne
  have h2 : Order.height (⊤ : Subobject S.X₂) ≠ ⊤ := height_top_lt_top.ne
  simp only [clength]
  rw [← ENat.toNat_add h1 h3]
  exact ENat.toNat_le_toNat (height_top_add_le hS) h2

/-- **Pseudoelement membership in a pullback subobject.** If a pseudoelement `x : X` and a
pseudoelement `b` of a subobject `y` of `Y` agree after pushing into `Y` (`y.arrow b = f x`), then
`x` comes from a pseudoelement of the preimage subobject `(pullback f).obj y`. This is the lift
across the pullback square `Subobject.isPullback f y`, transported to the concrete limit cone via
`IsPullback.isoPullback` so that `Abelian.Pseudoelement.pseudo_pullback` applies. -/
private theorem mem_pullback_obj {X Y : C} (f : X ⟶ Y) (y : Subobject Y) {x : X} {b : (y : C)}
    (h : y.arrow b = f x) :
    ∃ w : ((Subobject.pullback f).obj y : C), ((Subobject.pullback f).obj y).arrow w = x := by
  obtain ⟨s, _, hs2⟩ := Abelian.Pseudoelement.pseudo_pullback h
  refine ⟨(Subobject.isPullback f y).isoPullback.inv s, ?_⟩
  rw [← Abelian.Pseudoelement.comp_apply, IsPullback.isoPullback_inv_snd]
  exact hs2

/-- **Order-reflecting step of the Schreier embedding.** For a short exact sequence
`0 → X₁ →ᶠ X₂ →ᵍ X₃ → 0` and subobjects `A ≤ B` of `X₂`, if `A` and `B` have the same preimage along
`f` (`(pullback f).obj A = (pullback f).obj B`) and the same image along `g`
(`imageSubobject (A.arrow ≫ g) = imageSubobject (B.arrow ≫ g)`), then `B ≤ A`, hence `A = B`.

This is the genuine categorical (second-isomorphism-theorem) content. We show the inclusion
`ι := ofLE A B` is epi by a pseudoelement chase: a pseudoelement `b` of `B` has `g (B.arrow b)` in
the common image, so `g (A.arrow a₀) = g (B.arrow b)` for some `a₀` of `A`; the "difference"
`z` (`Abelian.Pseudoelement.sub_of_eq_image`) satisfies `g z = 0`, so `z ∈ im f = ker g`, and lies
in `B`; the preimage equality then forces `z ∈ A`, whence `B.arrow b ∈ A` and `ι` is surjective on
pseudoelements. Epi + mono = iso gives `B ≤ A`. -/
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

/-- **Upper bound (lengths)** — the genuine Schreier half of categorical Jordan–Hölder.
`clength X₂ ≤ clength X₁ + clength X₃` for a short exact sequence `0 → X₁ →ᶠ X₂ →ᵍ X₃ → 0`.

The map `Φ B = ((pullback f).obj B, imageSubobject (B.arrow ≫ g)) : Subobject X₂ → Subobject X₁ ×
Subobject X₃` is monotone in both coordinates and order-reflecting (`Φ_reflecting`), hence strictly
monotone. So `height ⊤(X₂) ≤ height (Φ ⊤)` (`height_le_height_apply_of_strictMono`), and the
product-order bound `height_prod_le` together with monotonicity of `height` gives
`height ⊤(X₂) ≤ height ⊤(X₁) + height ⊤(X₃)`; `ENat.toNat` transports this to `clength`. -/
private theorem clength_le_add {S : ShortComplex C} (hS : S.ShortExact) :
    clength S.X₂ ≤ clength S.X₁ + clength S.X₃ := by
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
  have h1 : Order.height (⊤ : Subobject S.X₁) ≠ ⊤ := height_top_lt_top.ne
  have h3 : Order.height (⊤ : Subobject S.X₃) ≠ ⊤ := height_top_lt_top.ne
  simp only [clength]
  rw [← ENat.toNat_add h1 h3]
  exact ENat.toNat_le_toNat hheight (WithTop.add_ne_top.mpr ⟨h1, h3⟩)

/-- **Additivity of composition length over short exact sequences** — the Krull–Schmidt crux.

For a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, the composition length is additive,
`clength X₂ = clength X₁ + clength X₃`. This is `le_antisymm` of the two one-sided bounds:

* `clength_add_le` (`clength X₁ + clength X₃ ≤ clength X₂`) — **proved**, modularity-free, from the
  down-interval isomorphism `height_mk_eq_height_top`, the epi-side inequality
  `height_top_le_coheight_kernel`, and the order lemma `height_add_coheight_le_height_top`.
* `clength_le_add` (`clength X₂ ≤ clength X₁ + clength X₃`) — the Schreier-refinement direction; see
  its docstring for the order-reflecting embedding `Subobject X₂ ↪ Subobject X₁ × Subobject X₃` that
  remains to be discharged.

Finiteness of all three lengths (needed both for the `le_antisymm` to make sense and for the
`ENat.toNat` arithmetic) comes from `FiniteDimensionalOrder (Subobject X)`, the order-theoretic form
of the §9.6 standing assumption; see the `clength_eq_zero_iff` docstring. -/
theorem clength_additive {S : ShortComplex C} (hS : S.ShortExact) :
    clength S.X₂ = clength S.X₁ + clength S.X₃ :=
  le_antisymm (clength_le_add hS) (clength_add_le hS)

/-- Composition length is additive over biproducts: `clength (Y ⊞ Z) = clength Y + clength Z`.

This follows from `clength_additive` applied to the canonical split short exact sequence
`0 → Y → Y ⊞ Z → Z → 0` built from `biprod.inl` and `biprod.snd`, whose section and retraction
are `biprod.inr` and `biprod.fst`. -/
theorem clength_biprod (Y Z : C) : clength (Y ⊞ Z) = clength Y + clength Z := by
  have spl :
      (ShortComplex.mk (biprod.inl : Y ⟶ Y ⊞ Z) (biprod.snd : Y ⊞ Z ⟶ Z) (by simp)).Splitting :=
    { r := biprod.fst, s := biprod.inr, f_r := by simp, s_g := by simp, id := biprod.total }
  exact clength_additive spl.shortExact

/-! ## Monotonicity of `clength` over the subobject lattice

For an inclusion of subobjects `A ≤ B` of a fixed `X`, the canonical short exact sequence
`0 → (A : C) → (B : C) → (B/A) → 0` (with `(A : C) → (B : C)` the inclusion `Subobject.ofLE`
and `B/A` its cokernel) together with `clength_additive` gives `clength (A : C) ≤ clength (B : C)`,
strictly so when `A < B` (then `B/A` is nonzero, so has positive length). This is the order-theoretic
input that turns `clength` into a well-founded induction measure on `Subobject X`. -/

/-- The composition-length identity attached to an inclusion `A ≤ B` of subobjects: the canonical
short exact sequence `0 → (A : C) → (B : C) → cokernel (ofLE A B h) → 0` is exact, so
`clength` is additive across it. -/
theorem clength_ofLE_add_cokernel {X : C} {A B : Subobject X} (h : A ≤ B) :
    clength (B : C) = clength (A : C) + clength (cokernel (Subobject.ofLE A B h)) := by
  have hSE : (ShortComplex.cokernelSequence (Subobject.ofLE A B h)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
      (inferInstanceAs (Mono (Subobject.ofLE A B h))) inferInstance
  have hadd := clength_additive hSE
  simpa using hadd

/-- **Monotonicity of composition length.** A subobject contained in another has length at most
that of the larger one. -/
theorem clength_mono {X : C} {A B : Subobject X} (h : A ≤ B) :
    clength (A : C) ≤ clength (B : C) := by
  rw [clength_ofLE_add_cokernel h]; exact Nat.le_add_right _ _

/-- **Strict monotonicity of composition length.** A proper subobject has strictly smaller length:
the quotient `B/A` is then nonzero, contributing positive length via `clength_pos_of_not_isZero`. -/
theorem clength_strictMono {X : C} {A B : Subobject X} (h : A < B) :
    clength (A : C) < clength (B : C) := by
  rw [clength_ofLE_add_cokernel h.le]
  have hpos : 0 < clength (cokernel (Subobject.ofLE A B h.le)) := by
    apply clength_pos_of_not_isZero
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

/-- The subobject lattice of any object satisfies the descending chain condition: `<` is
well-founded. This is the categorical descending chain condition, with `clength` as the
strictly-monotone `ℕ`-valued rank. -/
instance wellFoundedLT_subobject {X : C} : WellFoundedLT (Subobject X) :=
  ⟨Subrelation.wf (fun {_ _} h => clength_strictMono h) (InvImage.wf _ wellFounded_lt)⟩

/-- **Descending chain condition.** An antitone chain of subobjects of `X` is eventually constant. -/
theorem exists_eventually_constant_of_antitone {X : C} {a : ℕ → Subobject X}
    (ha : Antitone a) : ∃ N, ∀ m ≥ N, a m = a N :=
  (WellFoundedLT.antitone_chain_condition ha).imp fun _ h m hm => (h m hm).symm

/-- A non-decreasing `ℕ`-sequence bounded above is eventually constant (the value stabilises at the
index attaining its supremum). -/
private theorem nat_eventually_constant_of_monotone_of_bddAbove {f : ℕ → ℕ}
    (hf : Monotone f) {B : ℕ} (hB : ∀ n, f n ≤ B) : ∃ N, ∀ m ≥ N, f m = f N := by
  have hne : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
  have hbdd : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem hne hbdd
  refine ⟨N, fun m hm => le_antisymm ?_ (hf hm)⟩
  rw [hN]; exact le_csSup hbdd ⟨m, rfl⟩

/-- **Ascending chain condition.** A monotone chain of subobjects of `X` is eventually constant.
Unlike the descending case this uses that `clength` is bounded (every subobject lies below `⊤`),
so the non-decreasing length sequence is eventually constant; strict monotonicity then upgrades
constancy of the length to constancy of the chain. -/
theorem exists_eventually_constant_of_monotone {X : C} {a : ℕ → Subobject X}
    (ha : Monotone a) : ∃ N, ∀ m ≥ N, a m = a N := by
  obtain ⟨N, hN⟩ := nat_eventually_constant_of_monotone_of_bddAbove
    (f := fun n => clength (a n : C)) (fun _ _ h => clength_mono (ha h))
    (B := clength ((⊤ : Subobject X) : C)) (fun _ => clength_mono le_top)
  refine ⟨N, fun m hm => ?_⟩
  rcases (ha hm).lt_or_eq with hlt | heq
  · exact absurd (hN m hm) (by have := clength_strictMono hlt; omega)
  · exact heq.symm

/-! ## Image and kernel chains of an endomorphism

The descending image chain `im (f^n)` and ascending kernel chain `ker (f^n)` of an endomorphism
`f : End X` both stabilise, directly from the chain conditions above. These are the finite-length
inputs that Fitting's lemma (`fitting_decomposition`, link 3/5) consumes. -/

/-- The image chain `n ↦ im (f^n)` of an endomorphism is descending: `im (f^{n+1}) ≤ im (f^n)`,
because `f^{n+1} = f ≫ f^n` factors through `f^n`. -/
theorem imageSubobject_pow_antitone {X : C} (f : End X) :
    Antitone (fun n => imageSubobject ((f : X ⟶ X) ^ n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hcomp : (f : X ⟶ X) ^ (n + 1) = (f : X ⟶ X) ≫ ((f : X ⟶ X) ^ n) := by rw [pow_succ]; rfl
  change imageSubobject ((f : X ⟶ X) ^ (n + 1)) ≤ imageSubobject ((f : X ⟶ X) ^ n)
  rw [hcomp]
  exact imageSubobject_comp_le _ _

/-- The kernel chain `n ↦ ker (f^n)` of an endomorphism is ascending: `ker (f^n) ≤ ker (f^{n+1})`,
because `f^{n+1} = f^n ≫ f`. -/
theorem kernelSubobject_pow_monotone {X : C} (f : End X) :
    Monotone (fun n => kernelSubobject ((f : X ⟶ X) ^ n)) := by
  apply monotone_nat_of_le_succ
  intro n
  have hcomp : (f : X ⟶ X) ^ (n + 1) = ((f : X ⟶ X) ^ n) ≫ (f : X ⟶ X) := by rw [pow_succ']; rfl
  change kernelSubobject ((f : X ⟶ X) ^ n) ≤ kernelSubobject ((f : X ⟶ X) ^ (n + 1))
  rw [hcomp]
  exact kernelSubobject_comp_le _ _

/-- The descending image chain of an endomorphism stabilises. -/
theorem exists_imageSubobject_pow_stabilizes {X : C} (f : End X) :
    ∃ N, ∀ m ≥ N, imageSubobject ((f : X ⟶ X) ^ m) = imageSubobject ((f : X ⟶ X) ^ N) :=
  exists_eventually_constant_of_antitone (imageSubobject_pow_antitone f)

/-- The ascending kernel chain of an endomorphism stabilises. -/
theorem exists_kernelSubobject_pow_stabilizes {X : C} (f : End X) :
    ∃ N, ∀ m ≥ N, kernelSubobject ((f : X ⟶ X) ^ m) = kernelSubobject ((f : X ⟶ X) ^ N) :=
  exists_eventually_constant_of_monotone (kernelSubobject_pow_monotone f)

/-- Both the image and kernel chains of an endomorphism stabilise simultaneously: there is a single
positive `n` past which both have stabilised, witnessed by the equalities at `n` and `2 * n`.
This is the precise finite-length input of Fitting's lemma. -/
theorem exists_image_kernel_pow_stabilizes {X : C} (f : End X) :
    ∃ n, 0 < n ∧
      imageSubobject ((f : X ⟶ X) ^ n) = imageSubobject ((f : X ⟶ X) ^ (2 * n)) ∧
      kernelSubobject ((f : X ⟶ X) ^ n) = kernelSubobject ((f : X ⟶ X) ^ (2 * n)) := by
  obtain ⟨N₁, hN₁⟩ := exists_imageSubobject_pow_stabilizes f
  obtain ⟨N₂, hN₂⟩ := exists_kernelSubobject_pow_stabilizes f
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

/-- The kernel-subobject inclusion `ker g ↪ X → Y` is an exact short complex. -/
private theorem exact_kernelSubobject_arrow {Y Z : C} (g : Y ⟶ Z) :
    (ShortComplex.mk (kernelSubobject g).arrow g (kernelSubobject_arrow_comp g)).Exact := by
  rw [ShortComplex.exact_iff_image_eq_kernel]
  change imageSubobject (kernelSubobject g).arrow = kernelSubobject g
  rw [imageSubobject_mono, Subobject.mk_arrow]

/-- **Image restriction is an isomorphism at the stabilising power** — the precise finite-length
input Fitting's lemma (`fitting_decomposition`, link 3/5) consumes. For an endomorphism `f` there is
a positive `n` at which `image.ι (fⁿ) ≫ factorThruImage (fⁿ)` is an isomorphism. -/
theorem exists_pow_stabilizes {X : C} (f : End X) :
    ∃ n, 0 < n ∧ IsIso (Abelian.image.ι ((f : X ⟶ X) ^ n) ≫
      Abelian.factorThruImage ((f : X ⟶ X) ^ n)) := by
  obtain ⟨n, hn, him, hker⟩ := exists_image_kernel_pow_stabilizes f
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

end Etingof

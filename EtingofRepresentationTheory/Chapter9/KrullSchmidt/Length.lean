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

is the genuine categorical Jordan–Hölder content and is the hard part of this link. It is stated
here (top-down) and its proof — which requires either wiring `JordanHolderLattice` onto
`Subobject X` or a direct Schreier-refinement argument, together with finiteness of the height in a
finite abelian category — is left as a documented `sorry`, tracked as a follow-up issue. The
`clength_eq_zero` characterisation is proved in the (unconditional) "zero ⇒ length zero"
direction; its converse, and positivity for nonzero objects, both require the same finiteness
input and are likewise isolated.

This top-down split lets the downstream consumers (existence-of-decomposition and Fitting's-lemma
sub-issues of #5153) build against the final `clength` API immediately.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof

variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C]

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

/-- **Additivity of composition length over short exact sequences** — the Krull–Schmidt crux.

For a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, the composition length is additive. This is the
categorical Jordan–Hölder content: it follows from wiring `JordanHolderLattice` onto `Subobject X`
(supplying `IsModularLattice (Subobject X)` and the categorical second isomorphism theorem), neither
of which is in Mathlib. Tracked as a follow-up issue; see the module doc.

Like `clength_eq_zero_iff`, a complete proof also needs the finite-length condition (otherwise the
mixed case — `X₁` finite nonzero, `X₃` infinite length — fails: LHS `= 0` but RHS `≠ 0`), which
`IsFiniteAbelianCategory` does not currently supply; see the `clength_eq_zero_iff` docstring.

**Confirmed route (toward #5324/#5325).** The base cases of the Jordan–Hölder count are now in place
without further infrastructure: `clength_eq_zero_of_isZero` (length `0` on the zero object) and
`clength_simple` (length `1` on a simple object, via Mathlib's `IsSimpleOrder (Subobject X)` for
simple `X`). The remaining work is the *extension step*. The minimal categorical input is the
Schreier order-reflecting lemma for the short exact sequence `0 → X₁ →ᶠ X₂ →ᵍ X₃ → 0`: for
subobjects `A ≤ B` of `X₂`,
`(Subobject.pullback f).obj A = (Subobject.pullback f).obj B` together with
`imageSubobject (A.arrow ≫ g) = imageSubobject (B.arrow ≫ g)` forces `A = B`. This makes
`B ↦ ((pullback f).obj B, imageSubobject (B.arrow ≫ g))` order-reflecting into
`Subobject X₁ × Subobject X₃`, so every `LTSeries` in `Subobject X₂` has length
`≤ Order.height ⊤ (X₁) + Order.height ⊤ (X₃)`; with `Order.height_le_coe_iff` that bounds the height
of `⊤ : Subobject X₂`, giving finiteness (hence `clength_eq_zero_iff` via
`clength_eq_zero_iff_of_finiteDimensionalOrder`) and, refined to equality, the additivity here.

The Schreier lemma is the categorical second isomorphism content, and it is **reachable** with current
Mathlib (the earlier "missing helper" note was too pessimistic):
* the pseudoelement difference helper exists — `Abelian.Pseudoelement.sub_of_eq_image`
  (`f x = f y → ∃ z, f z = 0 ∧ ∀ g, g y = 0 → g z = g x`), used with
  `Abelian.Pseudoelement.pseudo_pullback` / `pseudo_exact_of_exact` exactly as in
  `exists_pow_stabilizes` below; or
* Mathlib's categorical snake lemma (`Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`) yields the
  second isomorphism theorem and hence the reflecting lemma directly.

Two residual gaps for the *equality* (not just the height bound): (1) Mathlib has no product-order
height lemma `height (a, b) = height a + height b`, so that arithmetic must be proved here; (2) the
reverse inequality needs splicing composition series of `X₁` and `X₃` (the embedding gives only `≤`).
The finiteness corollary alone already discharges `clength_eq_zero_iff` (see #5324). -/
theorem clength_additive {S : ShortComplex C} (hS : S.ShortExact) :
    clength S.X₂ = clength S.X₁ + clength S.X₃ := by
  sorry

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

attribute [local instance] CategoryTheory.Abelian.Pseudoelement.objectToSort
  CategoryTheory.Abelian.Pseudoelement.homToFun CategoryTheory.Abelian.Pseudoelement.overToSort

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

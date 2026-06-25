import EtingofRepresentationTheory.Chapter9.KrullSchmidt.Fitting
import EtingofRepresentationTheory.Chapter9.KrullSchmidt.Existence
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Exchange / uniqueness for indecomposable decompositions (Krull–Schmidt, link 4/5)

This file is the **uniqueness** half of the Krull–Schmidt theorem for a finite abelian category
`C`. Building on the local endomorphism rings of indecomposables (link 3/5,
`KrullSchmidt/Fitting.lean`) it proves the Azumaya exchange property:

* **`Etingof.indecomposable_summand_iso_factor`** — an indecomposable direct summand of a finite
  biproduct of indecomposables is isomorphic to one of the factors.

and bootstraps from it to full uniqueness of the multiset of factors:

* **`Etingof.krullSchmidt_unique`** — two finite biproducts of indecomposables that are isomorphic
  have the same factors up to a reindexing bijection.

## Proof of the exchange property

Suppose `X` is an indecomposable retract of `⨁ Y`, witnessed by `s : X ⟶ ⨁ Y`, `r : ⨁ Y ⟶ X`
with `s ≫ r = 𝟙 X`. The biproduct component identity `biproduct.total` expands the identity of `X`
into a finite sum over the index set:

```
𝟙 X = s ≫ r = s ≫ (∑ k, π k ≫ ι k) ≫ r = ∑ k, (s ≫ π k) ≫ (ι k ≫ r).
```

Each summand `a k := (s ≫ π k) ≫ (ι k ≫ r)` is an endomorphism of `X`, and their sum is the unit
`𝟙 X` of the ring `End X`. Because `End X` is **local** (`isLocalRing_End_of_indecomposable`, link
3/5) and the nonunits of a local ring are closed under addition, a finite sum that is a unit must
have a unit summand (`exists_isUnit_of_isUnit_sum`). So for some `k` the composite
`a k = α ≫ β` is an isomorphism, where `α := s ≫ π k : X ⟶ Y k` and `β := ι k ≫ r : Y k ⟶ X`.

Set `rr := β ≫ (α ≫ β)⁻¹`, so that `α ≫ rr = 𝟙 X`: `X` is a retract of `Y k` via `α`. The
endomorphism `rr ≫ α` of `Y k` is idempotent, and `End (Y k)` is local, so it is `0` or `𝟙`
(an idempotent in a local ring is trivial). It cannot be `0`: that would force
`𝟙 X = (α ≫ rr) ≫ (α ≫ rr) = α ≫ (rr ≫ α) ≫ rr = 0`, contradicting `X` nonzero. Hence
`rr ≫ α = 𝟙 (Y k)`, and together with `α ≫ rr = 𝟙 X` the map `α` is an isomorphism `X ≅ Y k`.

## Proof of uniqueness

Induct on the cardinality of the index set `κ`. With `κ` empty `⨁ Y` is a zero object, so `⨁ Z`
is zero, so `μ` is empty too (any `Z m` would be a nonzero summand of a zero object). With `κ`
nonempty, pick a point `k₀`; the inclusion/projection of `Y k₀` through the iso `e : ⨁ Y ≅ ⨁ Z`
exhibit `Y k₀` as an indecomposable retract of `⨁ Z`, so by the exchange property
`Y k₀ ≅ Z m₀` for some `m₀`. Cancelling the matched pair leaves an isomorphism of the biproducts
over `κ \ {k₀}` and `μ \ {m₀}`, to which the inductive hypothesis applies.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C]

/-- In a possibly noncommutative local ring, `IsUnit (a + b)` forces `IsUnit a ∨ IsUnit b`. Mathlib
only states this for `CommSemiring`, but the proof uses no commutativity: left-multiply by the
inverse unit to reduce to the defining property `isUnit_or_isUnit_of_add_one`. -/
private theorem isUnit_or_isUnit_of_isUnit_add' {R : Type*} [Ring R] [IsLocalRing R] {a b : R}
    (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one, mul_add] at hu
  refine (IsLocalRing.isUnit_or_isUnit_of_add_one hu).imp (fun ha => ?_) (fun hb => ?_)
  · have : a = ↑u * (↑u⁻¹ * a) := by rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact u.isUnit.mul ha
  · have : b = ↑u * (↑u⁻¹ * b) := by rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact u.isUnit.mul hb

/-- An idempotent unit is `1`: left-multiply `a * a = a` by the inverse unit. (Mathlib's
`IsIdempotentElem.iff_eq_one_of_isUnit` needs `IsDedekindFiniteMonoid`, which `End X` is not known
to satisfy; the direct argument below works in any monoid.) -/
private theorem idem_isUnit_eq_one {R : Type*} [Monoid R] {a : R}
    (h : IsIdempotentElem a) (hu : IsUnit a) : a = 1 := by
  obtain ⟨u, rfl⟩ := hu
  calc (↑u : R) = 1 * ↑u := (one_mul _).symm
    _ = (↑u⁻¹ * ↑u) * ↑u := by rw [Units.inv_mul]
    _ = ↑u⁻¹ * (↑u * ↑u) := by rw [mul_assoc]
    _ = ↑u⁻¹ * ↑u := by rw [h]
    _ = 1 := Units.inv_mul u

/-- An idempotent in a (possibly noncommutative) local ring is `0` or `1`. If `a` is a unit then
`a * a = a` forces `a = 1`; otherwise `1 - a` is a unit and the same argument on the (also
idempotent) `1 - a` forces it to be `1`, i.e. `a = 0`. -/
private theorem isIdempotentElem_eq_zero_or_one {R : Type*} [Ring R] [IsLocalRing R] {a : R}
    (h : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  have hor : IsUnit a ∨ IsUnit (1 - a) :=
    IsLocalRing.isUnit_or_isUnit_of_add_one (by abel : a + (1 - a) = 1)
  rcases hor with hu | hu
  · exact Or.inr (idem_isUnit_eq_one h hu)
  · refine Or.inl ?_
    have h1 : (1 : R) - a = 1 := idem_isUnit_eq_one h.one_sub hu
    exact sub_eq_self.mp h1

/-- In a (possibly noncommutative) local ring a finite sum that is a unit has a unit summand: the
nonunits are closed under addition (`isUnit_or_isUnit_of_isUnit_add'`) and contain `0`, so if every
summand were a nonunit the whole sum would be a nonunit. -/
private theorem exists_isUnit_of_isUnit_sum {R : Type*} [Ring R] [IsLocalRing R]
    {ι : Type*} (s : Finset ι) (g : ι → R) (h : IsUnit (∑ i ∈ s, g i)) :
    ∃ i ∈ s, IsUnit (g i) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ i ∈ s, g i ∈ nonunits R := fun i hi => mem_nonunits_iff.mpr (hcon i hi)
  have hsum : (∑ i ∈ s, g i) ∈ nonunits R :=
    Finset.sum_induction g (· ∈ nonunits R)
      (fun x y hx hy => by
        rw [mem_nonunits_iff] at hx hy ⊢
        exact fun hH => (isUnit_or_isUnit_of_isUnit_add' hH).elim hx hy)
      (zero_mem_nonunits.mpr zero_ne_one) hmem
  exact (mem_nonunits_iff.mp hsum) h

/-- An idempotent endomorphism of an indecomposable object is the zero morphism or the identity:
`End Z` is local, and an idempotent in a local ring is `0` or `1`. -/
private theorem endo_eq_zero_or_id {Z : C} (hZ : CategoryTheory.Indecomposable Z) {g : Z ⟶ Z}
    (hg : g ≫ g = g) : g = 0 ∨ g = 𝟙 Z := by
  haveI : IsLocalRing (End Z) := isLocalRing_End_of_indecomposable hZ
  have hidem : IsIdempotentElem (M := End Z) g := hg
  rcases isIdempotentElem_eq_zero_or_one hidem with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [← End.one_def]; exact h)

set_option linter.unusedFintypeInType false in
/-- **Azumaya exchange property.** An indecomposable direct summand `X` of a finite biproduct
`⨁ Y` of indecomposables is isomorphic to one of the factors `Y k`. -/
theorem indecomposable_summand_iso_factor {κ : Type} [Fintype κ] (Y : κ → C)
    (hY : ∀ k, CategoryTheory.Indecomposable (Y k))
    {X : C} (hX : CategoryTheory.Indecomposable X)
    (s : X ⟶ ⨁ Y) (r : ⨁ Y ⟶ X) (hsr : s ≫ r = 𝟙 X) :
    ∃ k, Nonempty (X ≅ Y k) := by
  -- Expand `𝟙 X` as a finite sum of endomorphisms `a k = (s ≫ π k) ≫ (ι k ≫ r)`.
  have key : (∑ k : κ, (s ≫ biproduct.π Y k) ≫ (biproduct.ι Y k ≫ r)) = 𝟙 X := by
    have e1 : ∀ k : κ, (s ≫ biproduct.π Y k) ≫ (biproduct.ι Y k ≫ r)
        = s ≫ (biproduct.π Y k ≫ biproduct.ι Y k) ≫ r := fun k => by simp only [Category.assoc]
    simp_rw [e1]
    rw [← Preadditive.comp_sum, ← Preadditive.sum_comp, biproduct.total, Category.id_comp, hsr]
  set a : κ → End X := fun k => (s ≫ biproduct.π Y k) ≫ (biproduct.ι Y k ≫ r) with ha
  have hsum : (∑ k, a k) = 𝟙 X := key
  -- The sum is the unit `𝟙 X = 1`, so some summand is a unit in the local ring `End X`.
  haveI : IsLocalRing (End X) := isLocalRing_End_of_indecomposable hX
  have hunit : IsUnit (∑ k, a k) := by rw [hsum, ← End.one_def]; exact isUnit_one
  obtain ⟨k, -, hk⟩ := exists_isUnit_of_isUnit_sum Finset.univ a hunit
  refine ⟨k, ?_⟩
  -- `a k = α ≫ β` is an iso, where `α : X ⟶ Y k`, `β : Y k ⟶ X`.
  set α : X ⟶ Y k := s ≫ biproduct.π Y k with hα
  set β : Y k ⟶ X := biproduct.ι Y k ≫ r with hβ
  have hak : (a k : X ⟶ X) = α ≫ β := rfl
  have hiso : IsIso (α ≫ β) := by
    rw [← hak]; exact (isUnit_iff_isIso (a k)).mp hk
  haveI := hiso
  -- `rr := β ≫ (α ≫ β)⁻¹` is a section of `α`.
  set rr : Y k ⟶ X := β ≫ inv (α ≫ β) with hrr
  have hαrr : α ≫ rr = 𝟙 X := by rw [hrr, ← Category.assoc, IsIso.hom_inv_id]
  -- `rr ≫ α` is an idempotent endomorphism of the indecomposable `Y k`, hence `0` or `𝟙`.
  have hcomp : (rr ≫ α) ≫ (rr ≫ α) = rr ≫ α := by
    rw [Category.assoc, ← Category.assoc α rr α, hαrr, Category.id_comp]
  rcases endo_eq_zero_or_id (hY k) hcomp with he0 | he1
  · -- `rr ≫ α = 0` forces `𝟙 X = 0`, impossible.
    exfalso
    apply hX.1
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 X = (α ≫ rr) ≫ (α ≫ rr) := by rw [hαrr, Category.comp_id]
      _ = α ≫ (rr ≫ α) ≫ rr := by simp only [Category.assoc]
      _ = α ≫ (0 : Y k ⟶ Y k) ≫ rr := by rw [he0]
      _ = 0 := by simp
  · -- `rr ≫ α = 𝟙 (Y k)`: with `α ≫ rr = 𝟙 X` this makes `α` an isomorphism.
    exact ⟨⟨α, rr, hαrr, he1⟩⟩

set_option linter.unusedFintypeInType false in
/-- **Uniqueness of the indecomposable decomposition.** Two finite biproducts of indecomposables
that are isomorphic have the same factors up to a reindexing bijection.

This is the recommended companion result that pins the §9.7 multiplicities. It bootstraps from the
exchange property `indecomposable_summand_iso_factor` by induction on `Fintype.card κ`:

* `κ` empty: `⨁ Y` is a zero object, so `⨁ Z` is zero, so `μ` is empty as well (any `Z m` would be
  a nonzero summand of a zero object); the empty equivalence `κ ≃ μ` works vacuously.
* `κ` nonempty: pick `k₀`. The inclusion `biproduct.ι Y k₀` and projection `biproduct.π Y k₀`
  composed through `e : ⨁ Y ≅ ⨁ Z` exhibit `Y k₀` as an indecomposable retract of `⨁ Z`, so by
  `indecomposable_summand_iso_factor` there is `m₀` with `Y k₀ ≅ Z m₀`. Cancelling the matched pair
  yields an isomorphism `⨁ (Y ∘ ι) ≅ ⨁ (Z ∘ ι')` of the biproducts over the complements
  `{k₀}ᶜ` and `{m₀}ᶜ`, to which the inductive hypothesis applies; extend the resulting bijection by
  `k₀ ↦ m₀`.

The cancellation step (peeling a matched indecomposable summand from both sides of an isomorphism of
biproducts) is the remaining categorical content; it is deferred here. -/
theorem krullSchmidt_unique {κ μ : Type} [Fintype κ] [Fintype μ] (Y : κ → C) (Z : μ → C)
    (hY : ∀ k, CategoryTheory.Indecomposable (Y k))
    (hZ : ∀ m, CategoryTheory.Indecomposable (Z m))
    (e : (⨁ Y) ≅ ⨁ Z) :
    ∃ σ : κ ≃ μ, ∀ k, Nonempty (Y k ≅ Z (σ k)) := by
  -- Induction on `Fintype.card κ`, peeling one matched indecomposable summand via the exchange
  -- property and cancelling it; see the module/strategy doc above.
  sorry

end Etingof

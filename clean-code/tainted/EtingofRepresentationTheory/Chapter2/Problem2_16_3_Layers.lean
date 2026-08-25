import EtingofRepresentationTheory.Chapter2.Problem2_16_3
import Mathlib.Tactic.FieldSimp


/-!
# Problem 2.16.3(b): the adjoint calculus for the layers of `𝔤₄`

`EtingofRepresentationTheory/Chapter2/Problem2_16_3.lean` sets up
`𝔤ₙ = ⟨x, y | ad(x)²y = ad(y)ⁿ⁺¹x = 0⟩` and computes the layers of `𝔤₄` of `t`-degree
`0, 1, 2` (dimensions `1, 5, 3`, matching the graded dimensions of the positive part `𝔫₊` of the
twisted affine algebra `A₂⁽²⁾`). This file develops the calculus for a general layer and carries
out the odd-to-even induction step.

## The calculus

Write `D = ad(ȳ)` (`dY` below, with `dY k j` for `Dʲ`) and `aᵢ = ad(ȳ)ⁱ(x̄)`, so `a₀ = x̄`. The
single Leibniz identity

`⁅aᵢ, ⁅ȳ, u⁆⁆ = ⁅ȳ, ⁅aᵢ, u⁆⁆ - ⁅aᵢ₊₁, u⁆`  (`lie_aElt_lie_yb`)

iterates to the binomial expansion `⁅aᵢ, Dʲ u⁆ = Σₗ (-1)ˡ (j choose l) Dʲ⁻ˡ ⁅aᵢ₊ₗ, u⁆`
(`lie_aElt_dY_two` … `lie_aElt_dY_five`), which converts every statement about `ad(x̄)` along an
`ad(ȳ)`-string into a statement about the five elements `⁅aᵢ, u⁆`, `i ≤ 4`. Since `a₅ = 0` the
`j = 5` case is a genuine relation (`serre_y`), and it is the only place the defining relation
`ad(y)⁵(x) = 0` enters.

## The layer invariants

A layer of odd `t`-degree is a five-term `D`-string with top `b`; one of even `t`-degree is a
three-term `D`-string with top `c`. `OddLayer b c` and `EvenLayer c` record the table of values
`⁅aᵢ, ·⁆` at the top of the string; by the expansions above this is equivalent to knowing
`⁅x̄, Dⁱ ·⁆` all the way along, which is what the closure principle
`span_eq_top_of_closed_under_ad` needs.

`EvenLayer.of_oddLayer` is the induction step, proved by:

* `⁅x̄, c⁆ = 0` — the *first* Serre relation `ad(x̄)²(ȳ) = 0` in the operator form `serre_x`,
  applied to `D²b`;
* `D³c = 0` — the *second* Serre relation `serre_y` applied to `D b`, which yields
  `10 · D³c = 0`; this is where the hypotheses `2 ≠ 0` and `5 ≠ 0` are needed, and it is what
  makes the even layers three-dimensional;
* `2⁅a₂, c⁆ = 3 D⁅a₁, c⁆` — `ad(a₂)` commutes with `ad(x̄)` (because `⁅a₀, a₂⁆ = 0`), giving
  `⁅a₂, c⁆ = -3⁅x̄, D²c⁆`; expanding `⁅x̄, D²c⁆` again turns this into `4⁅a₂, c⁆ = 6 D⁅a₁, c⁆`.

`oddLayer_xb` checks `OddLayer` for the layer of `t`-degree `1` (`b = x̄`), so the step is not
vacuous; `evenLayer_deg_two` is the resulting statement about the degree-`2` layer, whose top is
`-⁅a₀, a₃⁆`.

## The even-to-odd step

`oddTop c = -⁅a₁, c⁆` (equivalently `⁅x̄, D c⁆`) is the top of the next, odd, layer, and
`evenTop (oddTop c) = ⁅a₃, oddTop c⁆` the top of the one after that. From `EvenLayer c` **alone**
we obtain

* `EvenLayer.lie_zero_oddTop`, `lie_one_oddTop`, `lie_two_oddTop`, `dY_five_oddTop` — four of the
  six `OddLayer` fields (the fifth, `⁅a₃, b'⁆ = c''`, is a definition);
* `EvenLayer.step` — the whole of `EvenLayer (evenTop (oddTop c))`.

So the even-layer invariant propagates by itself, two `t`-degrees at a time
(`evenLayer_evenTower`), with no extra hypotheses beyond `2, 3, 5 ≠ 0`. The pair `(b, c)` does
*not* have to be carried: `⁅a₁, b'⁆ = 0` comes from `serre_x` applied to `D c`, not from
`⁅⁅a₁, a₄⁆, b⁆`.

## The defect, and what is still missing

The sixth odd-layer field, `⁅a₄, b'⁆ = 2 D c''`, does not follow from `EvenLayer c`. Its defect

`EvenLayer.defect c = ⁅a₄, b'⁆ - 2 D c''`

is annihilated by both `ad(x̄)` (`lie_zero_lie_four_oddTop`) and `ad(ȳ)`
(`dY_one_lie_four_oddTop`), hence is **central** in `𝔤₄` (`EvenLayer.central_defect`), and
`OddLayer.of_evenLayer_of_center` derives the full odd-layer invariant from the triviality of the
centre.

`EvenLayer.defect_eq` collapses the defect to a *single bracket*,

`EvenLayer.defect c = ⁅⁅a₁, a₃⁆, D c⁆`,

by writing `b' = ⁅x̄, D c⁆` and moving `a₄` across the outer bracket, using `⁅a₄, x̄⁆ = 2⁅a₁, a₃⁆`
(`lie_a4_a0`). Since `⁅a₁, a₃⁆ = D (evenTower k 0)` (`dY_one_evenTower_zero`), the defect at the
bottom of the tower is the bracket of an element with itself, so it vanishes
(`defect_evenTower_zero`) and the layer of `t`-degree `3` satisfies the full odd-layer invariant
unconditionally (`oddLayer_deg_three`).

The tower itself has a compact description: `c₀ = evenTower k 0` commutes with every even top
(`lie_evenTower_zero_evenTower`) and carries each one to the next,
`2⁅c₀, D c⁆ = c''` (`two_smul_lie_evenTower_zero_dY_one`), so the whole tower is the orbit of the
single operator `2 ad(c₀) ∘ D`.

Still missing: `⁅⁅a₁, a₃⁆, D (evenTower k m)⁆ = 0` for `m ≥ 1`, which by
`oddLayer_evenTower_of_lie_eq_zero` is all that stands between the even tower and the odd layer in
every degree. Both factors lie in the tower, so this is a statement about the bracket of two
explicit elements rather than about all central elements — but it is still equivalent to the
triviality of the centre of `𝔤₄` in that bidegree, and every Jacobi rearrangement of it is a
tautology, so it needs an input beyond the commutation relations.

## The spanning family

The last section assembles the calculus into the `LoopIdx`-indexed family `loopFam₄` — `ȳ` in
`t`-degree `0`, the five-term `ad(ȳ)`-string on `topOdd m` in degree `2m+1`, the three-term string
on `evenTower m` in degree `2m+2` — and feeds it to `span_eq_top_of_closed_under_ad`. All the
closure obligations follow from the calculus above except one: `⁅x̄, D⁴ (topOdd m)⁆` is
`-2 D (evenTower m)` only up to the defect `topDefect m`. So the family together with the defects
spans unconditionally (`span_loopSet_eq_top`), and the family alone spans as soon as the defects
vanish (`span_range_loopFam₄_eq_top`), in particular if the centre of `𝔤₄` is trivial
(`span_range_loopFam₄_eq_top_of_center`). The graded dimensions of the index type are
`1, 5, 3, 5, 3, …` (`card_loopIdx_deg_zero`, `card_loopIdx_deg_odd`, `card_loopIdx_deg_even`).
-/

namespace Etingof.Problem2_16_3

variable (k : Type*) [CommRing k]

/-! ## `ad(ȳ)` iterated -/

/-- `dY k j = ad(ȳ)ʲ`, as a function on `𝔤₄`; `aElt k 4 j = dY k j (x̄)`. -/
noncomputable def dY (j : ℕ) (u : g k 4) : g k 4 := (fun v => ⁅yb k 4, v⁆)^[j] u

/-- The adjoint-y iteration formula for `dY_zero_index`. -/
@[simp] theorem dY_zero_index (u : g k 4) : dY k 0 u = u := rfl

/-- The adjoint-y iteration formula for `dY_one`. -/
theorem dY_one (u : g k 4) : dY k 1 u = ⁅yb k 4, u⁆ := rfl

/-- The adjoint-y iteration formula for `dY_two_eq`. -/
theorem dY_two_eq (u : g k 4) : dY k 2 u = ⁅yb k 4, ⁅yb k 4, u⁆⁆ := rfl

/-- The adjoint-y iteration formula for `dY_three_eq`. -/
theorem dY_three_eq (u : g k 4) : dY k 3 u = ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, u⁆⁆⁆ := rfl

/-- The adjoint-y iteration formula for `dY_four_eq`. -/
theorem dY_four_eq (u : g k 4) :
    dY k 4 u = ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, u⁆⁆⁆⁆ := rfl

/-- The adjoint-y iteration formula for `dY_five_eq`. -/
theorem dY_five_eq (u : g k 4) :
    dY k 5 u = ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, u⁆⁆⁆⁆⁆ := rfl

/-- The adjoint-y iteration formula for `dY_succ`. -/
theorem dY_succ (j : ℕ) (u : g k 4) : dY k (j + 1) u = ⁅yb k 4, dY k j u⁆ :=
  Function.iterate_succ_apply' _ _ _

/-- The adjoint-y iteration formula for `dY_succ'`. -/
theorem dY_succ' (j : ℕ) (u : g k 4) : dY k (j + 1) u = dY k j ⁅yb k 4, u⁆ := rfl

/-- `Dⁱ (Dʲ u) = Dⁱ⁺ʲ u`. -/
theorem dY_add (i j : ℕ) (u : g k 4) : dY k (i + j) u = dY k i (dY k j u) :=
  Function.iterate_add_apply _ i j u

/-- `D (Dʲ u) = Dʲ⁺¹ u`. -/
theorem dY_one_dY (j : ℕ) (u : g k 4) : dY k 1 (dY k j u) = dY k (j + 1) u := by
  rw [dY_one, dY_succ]

/-- `Dʲ (D u) = Dʲ⁺¹ u`. -/
theorem dY_dY_one (j : ℕ) (u : g k 4) : dY k j (dY k 1 u) = dY k (j + 1) u := by
  rw [dY_one, dY_succ']

/-- The adjoint-y iteration formula for `dY_add_elt`. -/
@[simp] theorem dY_add_elt (j : ℕ) (u v : g k 4) : dY k j (u + v) = dY k j u + dY k j v := by
  induction j with
  | zero => rfl
  | succ j ih => rw [dY_succ, dY_succ, dY_succ, ih, lie_add]

/-- The adjoint-y iteration formula for `dY_zero_elt`. -/
@[simp] theorem dY_zero_elt (j : ℕ) : dY k j (0 : g k 4) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [dY_succ, ih, lie_zero]

/-- The adjoint-y iteration formula for `dY_neg_elt`. -/
@[simp] theorem dY_neg_elt (j : ℕ) (u : g k 4) : dY k j (-u) = -dY k j u := by
  induction j with
  | zero => rfl
  | succ j ih => rw [dY_succ, dY_succ, ih, lie_neg]

/-- The adjoint-y iteration formula for `dY_sub_elt`. -/
@[simp] theorem dY_sub_elt (j : ℕ) (u v : g k 4) : dY k j (u - v) = dY k j u - dY k j v := by
  rw [sub_eq_add_neg, dY_add_elt, dY_neg_elt, sub_eq_add_neg]

/-- The adjoint-y iteration formula for `dY_smul_elt`. -/
@[simp] theorem dY_smul_elt (j : ℕ) (a : k) (u : g k 4) : dY k j (a • u) = a • dY k j u := by
  induction j with
  | zero => rfl
  | succ j ih => rw [dY_succ, dY_succ, ih, lie_smul]

/-- The adjoint-y iteration formula for `dY_xb`. -/
theorem dY_xb (j : ℕ) : dY k j (xb k 4) = aElt k 4 j := rfl

/-! ## The Leibniz expansions -/

/-- **Leibniz.** `⁅aᵢ, ⁅ȳ, u⁆⁆ = ⁅ȳ, ⁅aᵢ, u⁆⁆ - ⁅aᵢ₊₁, u⁆`, from the Jacobi identity and
`aᵢ₊₁ = ⁅ȳ, aᵢ⁆`. Everything in this file is generated by this one identity. -/
theorem lie_aElt_lie_yb (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, ⁅yb k 4, u⁆⁆ = ⁅yb k 4, ⁅aElt k 4 i, u⁆⁆ - ⁅aElt k 4 (i + 1), u⁆ := by
  have h := leibniz_lie (yb k 4) (aElt k 4 i) u
  rw [← aElt_succ] at h
  rw [h]; abel

/-- The iterated adjoint-bracket expansion for `lie_aElt_dY_one`. -/
theorem lie_aElt_dY_one (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, dY k 1 u⁆ = dY k 1 ⁅aElt k 4 i, u⁆ - ⁅aElt k 4 (i + 1), u⁆ := by
  simp only [dY_one]; exact lie_aElt_lie_yb k i u

/-- The iterated adjoint-bracket expansion for `lie_aElt_dY_two`. -/
theorem lie_aElt_dY_two (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, dY k 2 u⁆
      = dY k 2 ⁅aElt k 4 i, u⁆ - (2 : k) • dY k 1 ⁅aElt k 4 (i + 1), u⁆
        + ⁅aElt k 4 (i + 2), u⁆ := by
  simp only [dY_two_eq, dY_one, lie_aElt_lie_yb, lie_sub, Nat.add_assoc, Nat.reduceAdd]
  module

/-- The iterated adjoint-bracket expansion for `lie_aElt_dY_three`. -/
theorem lie_aElt_dY_three (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, dY k 3 u⁆
      = dY k 3 ⁅aElt k 4 i, u⁆ - (3 : k) • dY k 2 ⁅aElt k 4 (i + 1), u⁆
        + (3 : k) • dY k 1 ⁅aElt k 4 (i + 2), u⁆ - ⁅aElt k 4 (i + 3), u⁆ := by
  simp only [dY_three_eq, dY_two_eq, dY_one, lie_aElt_lie_yb, lie_sub, Nat.add_assoc,
    Nat.reduceAdd]
  module

/-- The iterated adjoint-bracket expansion for `lie_aElt_dY_four`. -/
theorem lie_aElt_dY_four (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, dY k 4 u⁆
      = dY k 4 ⁅aElt k 4 i, u⁆ - (4 : k) • dY k 3 ⁅aElt k 4 (i + 1), u⁆
        + (6 : k) • dY k 2 ⁅aElt k 4 (i + 2), u⁆
        - (4 : k) • dY k 1 ⁅aElt k 4 (i + 3), u⁆ + ⁅aElt k 4 (i + 4), u⁆ := by
  simp only [dY_four_eq, dY_three_eq, dY_two_eq, dY_one, lie_aElt_lie_yb, lie_sub,
    Nat.add_assoc, Nat.reduceAdd]
  module

/-- The iterated adjoint-bracket expansion for `lie_aElt_dY_five`. -/
theorem lie_aElt_dY_five (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, dY k 5 u⁆
      = dY k 5 ⁅aElt k 4 i, u⁆ - (5 : k) • dY k 4 ⁅aElt k 4 (i + 1), u⁆
        + (10 : k) • dY k 3 ⁅aElt k 4 (i + 2), u⁆
        - (10 : k) • dY k 2 ⁅aElt k 4 (i + 3), u⁆
        + (5 : k) • dY k 1 ⁅aElt k 4 (i + 4), u⁆ - ⁅aElt k 4 (i + 5), u⁆ := by
  simp only [dY_five_eq, dY_four_eq, dY_three_eq, dY_two_eq, dY_one, lie_aElt_lie_yb,
    lie_sub, Nat.add_assoc, Nat.reduceAdd]
  module

/-- `⁅a₅, u⁆ = 0`: the defining relation `ad(y)⁵(x) = 0`. -/
@[simp] theorem lie_aElt_five (u : g k 4) : ⁅aElt k 4 5, u⁆ = 0 := by
  rw [aElt_five_eq_zero, zero_lie]

/-- **The second Serre relation, in the form used by the induction.** Specialising
`lie_aElt_dY_five` to `i = 0` and using `a₅ = 0`. -/
theorem serre_y (u : g k 4) :
    ⁅aElt k 4 0, dY k 5 u⁆
      = dY k 5 ⁅aElt k 4 0, u⁆ - (5 : k) • dY k 4 ⁅aElt k 4 1, u⁆
        + (10 : k) • dY k 3 ⁅aElt k 4 2, u⁆
        - (10 : k) • dY k 2 ⁅aElt k 4 3, u⁆
        + (5 : k) • dY k 1 ⁅aElt k 4 4, u⁆ := by
  have h := lie_aElt_dY_five k 0 u
  simp only [Nat.zero_add, lie_aElt_five, sub_zero] at h
  exact h

/-! ## Commutation -/

/-- If `⁅u, v⁆ = 0` then `ad u` and `ad v` commute. -/
theorem lie_comm_of_lie_eq_zero {u v : g k 4} (h : ⁅u, v⁆ = 0) (w : g k 4) :
    ⁅u, ⁅v, w⁆⁆ = ⁅v, ⁅u, w⁆⁆ := by
  rw [leibniz_lie, h, zero_lie, zero_add]

/-- `ad(a₁)` commutes with `ad(x̄)`, because `⁅a₀, a₁⁆ = 0` (the first Serre relation). -/
theorem lie_a1_lie_a0 (w : g k 4) :
    ⁅aElt k 4 1, ⁅aElt k 4 0, w⁆⁆ = ⁅aElt k 4 0, ⁅aElt k 4 1, w⁆⁆ :=
  lie_comm_of_lie_eq_zero k (by rw [← lie_skew, lie_a0_a1, neg_zero]) w

/-- `ad(a₂)` commutes with `ad(x̄)`, because `⁅a₀, a₂⁆ = 0`. -/
theorem lie_a2_lie_a0 (w : g k 4) :
    ⁅aElt k 4 2, ⁅aElt k 4 0, w⁆⁆ = ⁅aElt k 4 0, ⁅aElt k 4 2, w⁆⁆ :=
  lie_comm_of_lie_eq_zero k (by rw [← lie_skew, lie_a0_a2, neg_zero]) w

/-- **The first Serre relation, in operator form:**
`ad(x̄)² D = 2 ad(x̄) D ad(x̄) - D ad(x̄)²`. -/
theorem serre_x (w : g k 4) :
    ⁅aElt k 4 0, ⁅aElt k 4 0, dY k 1 w⁆⁆
      = (2 : k) • ⁅aElt k 4 0, dY k 1 ⁅aElt k 4 0, w⁆⁆
        - dY k 1 ⁅aElt k 4 0, ⁅aElt k 4 0, w⁆⁆ := by
  have h1 := lie_aElt_lie_yb k 0 w
  have h2 := lie_aElt_lie_yb k 0 ⁅aElt k 4 0, w⁆
  simp only [dY_one]
  rw [h1, lie_sub, h2, lie_a1_lie_a0]
  module

/-! ## The layer invariants -/

/-- The invariant carried by the top `b` of a layer of odd `t`-degree — a five-term
`ad(ȳ)`-string — together with the top `c` of the next (even) layer. -/
structure OddLayer (b c : g k 4) : Prop where
  /-- `⁅x̄, b⁆ = 0`. -/
  lie_zero : ⁅aElt k 4 0, b⁆ = 0
  /-- `⁅a₁, b⁆ = 0`. -/
  lie_one : ⁅aElt k 4 1, b⁆ = 0
  /-- `⁅a₂, b⁆ = 0`. -/
  lie_two : ⁅aElt k 4 2, b⁆ = 0
  /-- `⁅a₃, b⁆` is the top of the next layer. -/
  lie_three : ⁅aElt k 4 3, b⁆ = c
  /-- `⁅a₄, b⁆ = 2 D c`. -/
  lie_four : ⁅aElt k 4 4, b⁆ = (2 : k) • dY k 1 c
  /-- The string has length five. -/
  dY_top : dY k 5 b = 0

/-- The invariant carried by the top `c` of a layer of even `t`-degree — a three-term
`ad(ȳ)`-string. -/
structure EvenLayer (c : g k 4) : Prop where
  /-- `⁅x̄, c⁆ = 0`. -/
  lie_zero : ⁅aElt k 4 0, c⁆ = 0
  /-- The string has length three. -/
  dY_top : dY k 3 c = 0
  /-- `2⁅a₂, c⁆ = 3 D⁅a₁, c⁆`; over a field with `2 ≠ 0` this says `⁅a₂, c⁆ = (3/2) D⁅a₁, c⁆`. -/
  lie_two : (2 : k) • ⁅aElt k 4 2, c⁆ = (3 : k) • dY k 1 ⁅aElt k 4 1, c⁆

/-! ### The layer of `t`-degree `1`

`b = x̄` satisfies `OddLayer` with `c = -⁅a₀, a₃⁆`, so the induction step is not vacuous. -/

/-- `2 D⁅a₀, a₃⁆ = ⁅a₀, a₄⁆`. (Over a field with `2 ≠ 0`: `D⁅a₀, a₃⁆ = ½⁅a₀, a₄⁆`, the first
step of the `ad(ȳ)`-string of the degree-`2` layer.) -/
theorem two_smul_dY_lie_a0_a3 :
    (2 : k) • dY k 1 ⁅aElt k 4 0, aElt k 4 3⁆ = ⁅aElt k 4 0, aElt k 4 4⁆ := by
  have h : dY k 1 ⁅aElt k 4 0, aElt k 4 3⁆
      = ⁅aElt k 4 1, aElt k 4 3⁆ + ⁅aElt k 4 0, aElt k 4 4⁆ := by
    rw [dY_one]; exact lie_yb_lie_aElt k 4 0 3
  have h2 : (2 : k) • ⁅aElt k 4 1, aElt k 4 3⁆ = -⁅aElt k 4 0, aElt k 4 4⁆ := by
    rw [eq_neg_iff_add_eq_zero]; exact lie_a1_a3_add k
  rw [h, smul_add, h2]
  module

/-- The layer of `t`-degree `1` of `𝔤₄`, whose top is `x̄`, satisfies the odd-layer invariant;
the top of the next layer is `-⁅a₀, a₃⁆`. -/
theorem oddLayer_xb : OddLayer k (xb k 4) (-⁅aElt k 4 0, aElt k 4 3⁆) where
  lie_zero := lie_self _
  lie_one := by
    change ⁅aElt k 4 1, aElt k 4 0⁆ = 0
    rw [← lie_skew, lie_a0_a1, neg_zero]
  lie_two := by
    change ⁅aElt k 4 2, aElt k 4 0⁆ = 0
    rw [← lie_skew, lie_a0_a2, neg_zero]
  lie_three := by
    change ⁅aElt k 4 3, aElt k 4 0⁆ = _
    rw [← lie_skew]
  lie_four := by
    change ⁅aElt k 4 4, aElt k 4 0⁆ = _
    rw [← lie_skew, dY_neg_elt, smul_neg, two_smul_dY_lie_a0_a3]
  dY_top := by rw [dY_xb, aElt_five_eq_zero]

/-! ## The odd-to-even induction step -/

section Step

variable {k}

/-- `⁅x̄, D b⁆ = 0`. -/
theorem OddLayer.lie_zero_dY_one {b c : g k 4} (h : OddLayer k b c) :
    ⁅aElt k 4 0, dY k 1 b⁆ = 0 := by
  rw [lie_aElt_dY_one, h.lie_zero, h.lie_one]; simp

/-- `⁅a₁, D b⁆ = 0`. -/
theorem OddLayer.lie_one_dY_one {b c : g k 4} (h : OddLayer k b c) :
    ⁅aElt k 4 1, dY k 1 b⁆ = 0 := by
  rw [lie_aElt_dY_one, h.lie_one, h.lie_two]; simp

/-- `⁅a₂, D b⁆ = -c`. -/
theorem OddLayer.lie_two_dY_one {b c : g k 4} (h : OddLayer k b c) :
    ⁅aElt k 4 2, dY k 1 b⁆ = -c := by
  rw [lie_aElt_dY_one, h.lie_two, h.lie_three]; simp

/-- `⁅a₃, D b⁆ = -D c`. -/
theorem OddLayer.lie_three_dY_one {b c : g k 4} (h : OddLayer k b c) :
    ⁅aElt k 4 3, dY k 1 b⁆ = -dY k 1 c := by
  rw [lie_aElt_dY_one, h.lie_three, h.lie_four]; module

/-- `⁅a₄, D b⁆ = 2 D² c`. -/
theorem OddLayer.lie_four_dY_one {b c : g k 4} (h : OddLayer k b c) :
    ⁅aElt k 4 4, dY k 1 b⁆ = (2 : k) • dY k 2 c := by
  rw [lie_aElt_dY_one, h.lie_four, lie_aElt_five, sub_zero, dY_smul_elt, dY_one_dY]

/-- `D⁵ (D b) = 0`. -/
theorem OddLayer.dY_five_dY_one {b c : g k 4} (h : OddLayer k b c) :
    dY k 5 (dY k 1 b) = 0 := by
  rw [dY_dY_one, dY_succ, h.dY_top, _root_.lie_zero]

/-- `⁅x̄, D² b⁆ = 0`. -/
theorem OddLayer.lie_zero_dY_two {b c : g k 4} (h : OddLayer k b c) :
    ⁅aElt k 4 0, dY k 2 b⁆ = 0 := by
  rw [lie_aElt_dY_two, h.lie_zero, h.lie_one, h.lie_two]; simp

/-- `⁅x̄, D³ b⁆ = -c`. -/
theorem OddLayer.lie_zero_dY_three {b c : g k 4} (h : OddLayer k b c) :
    ⁅aElt k 4 0, dY k 3 b⁆ = -c := by
  rw [lie_aElt_dY_three, h.lie_zero, h.lie_one, h.lie_two, h.lie_three]; simp

/-- **`⁅x̄, c⁆ = 0`**, from the first Serre relation applied to `D² b`. -/
theorem OddLayer.lie_zero_top {b c : g k 4} (h : OddLayer k b c) :
    ⁅aElt k 4 0, c⁆ = 0 := by
  have hs := serre_x k (dY k 2 b)
  rw [dY_one_dY, h.lie_zero_dY_two, h.lie_zero_dY_three] at hs
  simp only [lie_neg, _root_.lie_zero, dY_zero_elt, smul_zero, sub_zero, neg_eq_zero] at hs
  exact hs

/-- `⁅a₂, D³ b⁆ = 3 D² c`: the input to the degree-`2` relation of the next layer. -/
theorem OddLayer.lie_two_dY_three {b c : g k 4} (h : OddLayer k b c) :
    ⁅aElt k 4 2, dY k 3 b⁆ = (3 : k) • dY k 2 c := by
  rw [lie_aElt_dY_three, h.lie_two, h.lie_three, h.lie_four, lie_aElt_five]
  simp only [dY_zero_elt, dY_smul_elt, dY_one_dY]
  module

/-- **`10 · D³c = 0`**, from the second Serre relation applied to `D b`. -/
theorem OddLayer.ten_smul_dY_three {b c : g k 4} (h : OddLayer k b c) :
    (10 : k) • dY k 3 c = 0 := by
  have hs := serre_y k (dY k 1 b)
  rw [h.dY_five_dY_one, h.lie_zero_dY_one, h.lie_one_dY_one, h.lie_two_dY_one,
    h.lie_three_dY_one, h.lie_four_dY_one] at hs
  simp only [_root_.lie_zero, dY_zero_elt, smul_zero, sub_zero, dY_neg_elt, dY_smul_elt,
    dY_one_dY, dY_dY_one, Nat.reduceAdd] at hs
  rw [hs]
  module

/-- **`4⁅a₂, c⁆ = 6 D⁅a₁, c⁆`**: `ad(a₂)` commutes with `ad(x̄)`, so `⁅a₂, c⁆ = -3⁅x̄, D²c⁆`,
and expanding `⁅x̄, D²c⁆` again gives the relation. -/
theorem OddLayer.four_smul_lie_two_top {b c : g k 4} (h : OddLayer k b c) :
    (4 : k) • ⁅aElt k 4 2, c⁆ = (6 : k) • dY k 1 ⁅aElt k 4 1, c⁆ := by
  have hc : c = -⁅aElt k 4 0, dY k 3 b⁆ := by rw [h.lie_zero_dY_three, neg_neg]
  have key : ⁅aElt k 4 2, c⁆ = -((3 : k) • ⁅aElt k 4 0, dY k 2 c⁆) := by
    conv_lhs => rw [hc]
    rw [lie_neg, lie_a2_lie_a0, h.lie_two_dY_three, lie_smul]
  have hexp : ⁅aElt k 4 0, dY k 2 c⁆
      = dY k 2 ⁅aElt k 4 0, c⁆ - (2 : k) • dY k 1 ⁅aElt k 4 1, c⁆ + ⁅aElt k 4 2, c⁆ :=
    lie_aElt_dY_two k 0 c
  rw [h.lie_zero_top, dY_zero_elt, zero_sub] at hexp
  rw [hexp] at key
  rw [← sub_eq_zero] at key ⊢
  rw [← key]
  module

/-! ### The two tops of the induction -/

/-- The top of the odd layer produced from the top `c` of an even layer. In the loop model
`oddTop c = ⁅x̄, D c⁆`; the form used here is the equivalent `-⁅a₁, c⁆`. -/
noncomputable def oddTop (c : g k 4) : g k 4 := -⁅aElt k 4 1, c⁆

/-- The top of the even layer produced from the top `b` of an odd layer. -/
noncomputable def evenTop (b : g k 4) : g k 4 := ⁅aElt k 4 3, b⁆

/-- The bracket identity for `lie_one_eq_neg_oddTop`. -/
theorem lie_one_eq_neg_oddTop (c : g k 4) : ⁅aElt k 4 1, c⁆ = -oddTop c := by
  rw [oddTop, neg_neg]

/-- Degree or layer formula for `oddTop_eq`. -/
theorem oddTop_eq (c : g k 4) : oddTop c = -⁅aElt k 4 1, c⁆ := rfl

/-- Degree or layer formula for `evenTop_eq`. -/
theorem evenTop_eq (b : g k 4) : evenTop b = ⁅aElt k 4 3, b⁆ := rfl

end Step

/-! ### The step, over a field -/

section Field

variable {k : Type*} [Field k]

/-- **The odd-to-even induction step.** From the invariant at the top of a layer of odd
`t`-degree, the top `c` of the next layer satisfies the even-layer invariant. -/
theorem EvenLayer.of_oddLayer (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0) {b c : g k 4}
    (h : OddLayer k b c) : EvenLayer k c where
  lie_zero := h.lie_zero_top
  dY_top := by
    have h10 : (10 : k) ≠ 0 := by
      have : (10 : k) = 2 * 5 := by norm_num
      rw [this]; exact mul_ne_zero h2 h5
    have := congrArg (fun v : g k 4 => (10 : k)⁻¹ • v) h.ten_smul_dY_three
    simpa [smul_smul, inv_mul_cancel₀ h10] using this
  lie_two := by
    have hkey := h.four_smul_lie_two_top
    have := congrArg (fun v : g k 4 => (2 : k)⁻¹ • v) hkey
    simp only [smul_smul] at this
    rw [show (2 : k)⁻¹ * 4 = 2 by field_simp; ring,
      show (2 : k)⁻¹ * 6 = 3 by field_simp; ring] at this
    exact this

/-- The layer of `t`-degree `2` of `𝔤₄`, with top `-⁅a₀, a₃⁆`, satisfies the even-layer
invariant. This is the odd-to-even step applied to the degree-`1` layer, and it reproves
`D³⁅a₀, a₃⁆ = 0` and `⁅x̄, ⁅a₀, a₃⁆⁆ = 0` from the general machinery. -/
theorem evenLayer_deg_two (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    EvenLayer k (-⁅aElt k 4 0, aElt k 4 3⁆) :=
  EvenLayer.of_oddLayer h2 h5 (oddLayer_xb k)

/-- **The `ad(ȳ)`-string of the degree-`2` layer has length three:** `D³⁅a₀, a₃⁆ = 0`.

This is the new content of `evenLayer_deg_two`. The degree-`2` layer is spanned by
`⁅a₀, a₃⁆, D⁅a₀, a₃⁆, D²⁅a₀, a₃⁆` (`= ⁅a₀,a₃⁆, ½⁅a₀,a₄⁆, ½⁅a₁,a₄⁆`, the three elements of
`lie_aElt_mem_layerTwo`), and the string stops there — matching `dim 𝔤₀ = 3` on the loop side
of `loopPos`. -/
theorem dY_three_lie_a0_a3 (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    dY k 3 ⁅aElt k 4 0, aElt k 4 3⁆ = 0 := by
  have h := (evenLayer_deg_two h2 h5).dY_top
  rw [dY_neg_elt, neg_eq_zero] at h
  exact h

/-- Consistency with `lie_a0_lie_a0_a3`: the invariant's `⁅x̄, c⁆ = 0` at the degree-`2` layer
is the already-known vanishing `⁅x̄, ⁅a₀, a₃⁆⁆ = 0`. -/
theorem lie_zero_deg_two (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    ⁅aElt k 4 0, ⁅aElt k 4 0, aElt k 4 3⁆⁆ = 0 := by
  have h := (evenLayer_deg_two h2 h5).lie_zero
  rw [lie_neg, neg_eq_zero] at h
  exact h

end Field

/-! ## The even-to-odd induction step

From `EvenLayer c` alone we recover *five* of the six fields of `OddLayer (oddTop c) (evenTop
(oddTop c))`, and the whole of `EvenLayer (evenTop (oddTop c))` — so the even-layer invariant
propagates by itself, two `t`-degrees at a time, with no extra hypotheses. Contrary to the design
sketched in the parent issue, the induction does **not** have to carry the previous odd top: the
vanishing `⁅a₁, b'⁆ = 0` follows from the *first* Serre relation applied to `D c`, not from
`⁅⁅a₁,a₄⁆, b⁆`.

The one field that does not follow is `⁅a₄, b'⁆ = 2 D c''`. What we can prove about the defect
`w := ⁅a₄, b'⁆ - 2 D c''` is that `D w = 0` and `⁅x̄, w⁆ = 0`, hence (`central_defect`) that `w`
is central in `𝔤₄`. So the missing sixth field is exactly the statement that `𝔤₄` has no central
element in that bidegree. -/

section EvenToOdd

variable {k : Type*} [Field k] {c : g k 4}

private theorem smul_cancel₀ {a : k} (ha : a ≠ 0) {v w : g k 4} (hvw : a • v = a • w) : v = w := by
  have h' := congrArg (fun z : g k 4 => a⁻¹ • z) hvw
  simpa [smul_smul, inv_mul_cancel₀ ha] using h'

private theorem eq_zero_of_smul₀ {a : k} (ha : a ≠ 0) {v : g k 4} (hv : a • v = 0) : v = 0 :=
  smul_cancel₀ ha (by rw [hv, smul_zero])

/-- `⁅a₄, x̄⁆ = 2⁅a₁, a₃⁆`. The right-hand side is `D` of the top of the degree-`2` layer
(`dY_one_evenTower_zero`), which is what makes `defect_eq` below possible. -/
theorem lie_a4_a0 : ⁅aElt k 4 4, aElt k 4 0⁆ = (2 : k) • ⁅aElt k 4 1, aElt k 4 3⁆ := by
  have h := lie_a1_a3_add k
  rw [(lie_skew (aElt k 4 4) (aElt k 4 0)).symm]
  linear_combination (norm := module) -h

namespace EvenLayer

/-! ### What the even-layer table says about `a₃` and `a₄` -/

/-- `2⁅a₃, c⁆ = 3 D²⁅a₁, c⁆`, from `⁅x̄, D³c⁆ = 0`. -/
theorem two_smul_lie_three (h : EvenLayer k c) :
    (2 : k) • ⁅aElt k 4 3, c⁆ = (3 : k) • dY k 2 ⁅aElt k 4 1, c⁆ := by
  have e := lie_aElt_dY_three k 0 c
  rw [h.dY_top, h.lie_zero] at e
  simp only [Nat.zero_add, _root_.lie_zero, dY_zero_elt] at e
  have hD : (2 : k) • dY k 1 ⁅aElt k 4 2, c⁆ = (3 : k) • dY k 2 ⁅aElt k 4 1, c⁆ := by
    rw [← dY_smul_elt, h.lie_two, dY_smul_elt, dY_one_dY]
  linear_combination (norm := module) (2 : k) • e + (3 : k) • hD

/-- `⁅a₄, c⁆ = D³⁅a₁, c⁆`, from `⁅a₁, D³c⁆ = 0`. -/
theorem lie_four (h2 : (2 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 4, c⁆ = dY k 3 ⁅aElt k 4 1, c⁆ := by
  have e := lie_aElt_dY_three k 1 c
  rw [h.dY_top] at e
  simp only [Nat.reduceAdd, _root_.lie_zero] at e
  have hD2 : (2 : k) • dY k 2 ⁅aElt k 4 2, c⁆ = (3 : k) • dY k 3 ⁅aElt k 4 1, c⁆ := by
    rw [← dY_smul_elt, h.lie_two, dY_smul_elt, dY_dY_one]
  have hD3 : (2 : k) • dY k 1 ⁅aElt k 4 3, c⁆ = (3 : k) • dY k 3 ⁅aElt k 4 1, c⁆ := by
    rw [← dY_smul_elt, h.two_smul_lie_three, dY_smul_elt, dY_one_dY]
  refine smul_cancel₀ h2 ?_
  linear_combination (norm := module) (2 : k) • e - (3 : k) • hD2 + (3 : k) • hD3

/-! ### The first four fields of the odd layer -/

/-- `⁅x̄, b'⁆ = 0`. -/
theorem lie_zero_oddTop (h : EvenLayer k c) : ⁅aElt k 4 0, oddTop c⁆ = 0 := by
  rw [oddTop_eq, lie_neg, ← lie_a1_lie_a0, h.lie_zero, _root_.lie_zero, neg_zero]

/-- `⁅x̄, D c⁆ = b'`: the odd top really is the one the loop model predicts. -/
theorem lie_zero_dY_one (h : EvenLayer k c) : ⁅aElt k 4 0, dY k 1 c⁆ = oddTop c := by
  rw [lie_aElt_dY_one, h.lie_zero, dY_zero_elt, zero_sub, oddTop_eq]

/-- `2⁅x̄, D²c⁆ = D b'`. -/
theorem two_smul_lie_zero_dY_two (h : EvenLayer k c) :
    (2 : k) • ⁅aElt k 4 0, dY k 2 c⁆ = dY k 1 (oddTop c) := by
  have e := lie_aElt_dY_two k 0 c
  rw [h.lie_zero] at e
  simp only [Nat.zero_add, dY_zero_elt, zero_sub] at e
  have hb : dY k 1 (oddTop c) = -dY k 1 ⁅aElt k 4 1, c⁆ := by
    rw [oddTop_eq, dY_neg_elt]
  linear_combination (norm := module) (2 : k) • e - hb + h.lie_two

/-- `⁅x̄, D b'⁆ = -⁅a₁, b'⁆`. -/
theorem lie_zero_dY_one_oddTop (h : EvenLayer k c) :
    ⁅aElt k 4 0, dY k 1 (oddTop c)⁆ = -⁅aElt k 4 1, oddTop c⁆ := by
  rw [lie_aElt_dY_one, h.lie_zero_oddTop, dY_zero_elt, zero_sub]

/-- **`⁅a₁, b'⁆ = 0`**, from the first Serre relation applied to `D c`. This is where `3 ≠ 0`
first enters, and it needs nothing but `EvenLayer c`. -/
theorem lie_one_oddTop (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 1, oddTop c⁆ = 0 := by
  have hs := serre_x k (dY k 1 c)
  rw [dY_one_dY, h.lie_zero_dY_one, h.lie_zero_oddTop, h.lie_zero_dY_one_oddTop] at hs
  simp only [dY_zero_elt, sub_zero, smul_neg] at hs
  have hL : (2 : k) • ⁅aElt k 4 0, ⁅aElt k 4 0, dY k 2 c⁆⁆ = -⁅aElt k 4 1, oddTop c⁆ := by
    rw [← lie_smul, h.two_smul_lie_zero_dY_two, h.lie_zero_dY_one_oddTop]
  refine eq_zero_of_smul₀ h3 ?_
  linear_combination (norm := module) (2 : k) • hs - hL

/-- `⁅x̄, D²b'⁆ = ⁅a₂, b'⁆`. -/
theorem lie_zero_dY_two_oddTop (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 0, dY k 2 (oddTop c)⁆ = ⁅aElt k 4 2, oddTop c⁆ := by
  have e := lie_aElt_dY_two k 0 (oddTop c)
  rw [h.lie_zero_oddTop, h.lie_one_oddTop h3] at e
  simpa using e

/-- **`⁅a₂, b'⁆ = 0`**, from the first Serre relation applied to `D²c`. -/
theorem lie_two_oddTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 2, oddTop c⁆ = 0 := by
  have hs := serre_x k (dY k 2 c)
  rw [dY_one_dY, h.dY_top] at hs
  simp only [_root_.lie_zero] at hs
  have hP : (2 : k) • ⁅aElt k 4 0, dY k 1 ⁅aElt k 4 0, dY k 2 c⁆⁆
      = ⁅aElt k 4 2, oddTop c⁆ := by
    rw [← lie_smul, ← dY_smul_elt, h.two_smul_lie_zero_dY_two, dY_one_dY,
      h.lie_zero_dY_two_oddTop h3]
  have hQ : (2 : k) • dY k 1 ⁅aElt k 4 0, ⁅aElt k 4 0, dY k 2 c⁆⁆ = 0 := by
    rw [← dY_smul_elt, ← lie_smul, h.two_smul_lie_zero_dY_two, h.lie_zero_dY_one_oddTop,
      h.lie_one_oddTop h3, neg_zero, dY_zero_elt]
  refine eq_zero_of_smul₀ h2 ?_
  linear_combination (norm := module) (-2 : k) • hs - (2 : k) • hP + hQ

/-- **`D⁵ b' = 0`**, from the second Serre relation applied to `D c`: the odd string produced by
an even layer has length five. -/
theorem dY_five_oddTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    dY k 5 (oddTop c) = 0 := by
  have hsix : dY k 6 c = 0 := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, dY_add, h.dY_top, dY_zero_elt]
  have hs := serre_y k (dY k 1 c)
  rw [dY_dY_one, hsix] at hs
  simp only [_root_.lie_zero] at hs
  have e0 : dY k 5 ⁅aElt k 4 0, dY k 1 c⁆ = dY k 5 (oddTop c) := by
    rw [h.lie_zero_dY_one]
  have e1 : (2 : k) • dY k 4 ⁅aElt k 4 1, dY k 1 c⁆ = dY k 5 (oddTop c) := by
    have h1 : (2 : k) • ⁅aElt k 4 1, dY k 1 c⁆ = dY k 1 (oddTop c) := by
      have e := lie_aElt_dY_one k 1 c
      have hb : dY k 1 (oddTop c) = -dY k 1 ⁅aElt k 4 1, c⁆ := by rw [oddTop_eq, dY_neg_elt]
      linear_combination (norm := module) (2 : k) • e - hb - h.lie_two
    rw [← dY_smul_elt, h1, dY_dY_one]
  have e2 : dY k 3 ⁅aElt k 4 2, dY k 1 c⁆ = 0 := by
    have h2' : (2 : k) • ⁅aElt k 4 2, dY k 1 c⁆ = 0 := by
      have e := lie_aElt_dY_one k 2 c
      have hD : dY k 1 ((2 : k) • ⁅aElt k 4 2, c⁆) = (3 : k) • dY k 2 ⁅aElt k 4 1, c⁆ := by
        rw [h.lie_two, dY_smul_elt, dY_one_dY]
      rw [dY_smul_elt] at hD
      linear_combination (norm := module) (2 : k) • e + hD - h.two_smul_lie_three
    rw [eq_zero_of_smul₀ h2 h2', dY_zero_elt]
  have e3 : (2 : k) • dY k 2 ⁅aElt k 4 3, dY k 1 c⁆ = -dY k 5 (oddTop c) := by
    have h3' : (2 : k) • ⁅aElt k 4 3, dY k 1 c⁆ = -dY k 3 (oddTop c) := by
      have e := lie_aElt_dY_one k 3 c
      have hD : dY k 1 ((2 : k) • ⁅aElt k 4 3, c⁆) = (3 : k) • dY k 3 ⁅aElt k 4 1, c⁆ := by
        rw [h.two_smul_lie_three, dY_smul_elt, dY_one_dY]
      rw [dY_smul_elt] at hD
      have hb : dY k 3 (oddTop c) = -dY k 3 ⁅aElt k 4 1, c⁆ := by rw [oddTop_eq, dY_neg_elt]
      simp only [Nat.reduceAdd] at e
      linear_combination (norm := module) (2 : k) • e + hD - (2 : k) • h.lie_four h2 + hb
    rw [← dY_smul_elt, h3', dY_neg_elt, show (5 : ℕ) = 2 + 3 from rfl, dY_add]
  have e4 : dY k 1 ⁅aElt k 4 4, dY k 1 c⁆ = -dY k 5 (oddTop c) := by
    have h4 : ⁅aElt k 4 4, dY k 1 c⁆ = -dY k 4 (oddTop c) := by
      have e := lie_aElt_dY_one k 4 c
      have hb : dY k 4 (oddTop c) = -dY k 4 ⁅aElt k 4 1, c⁆ := by rw [oddTop_eq, dY_neg_elt]
      have hD : dY k 1 ⁅aElt k 4 4, c⁆ = dY k 4 ⁅aElt k 4 1, c⁆ := by
        rw [h.lie_four h2, dY_one_dY]
      simp only [Nat.reduceAdd, lie_aElt_five] at e
      linear_combination (norm := module) e + hD + hb
    rw [h4, dY_neg_elt, dY_one_dY]
  refine eq_zero_of_smul₀ h3 ?_
  linear_combination (norm := module) (2 : k) • hs + (2 : k) • e0 - (5 : k) • e1
    + (20 : k) • e2 - (10 : k) • e3 + (10 : k) • e4

/-! ### Back to an even layer -/

/-- `⁅x̄, D³ b'⁆ = -c''`. -/
theorem lie_zero_dY_three_oddTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 0, dY k 3 (oddTop c)⁆ = -evenTop (oddTop c) := by
  have e := lie_aElt_dY_three k 0 (oddTop c)
  rw [h.lie_zero_oddTop, h.lie_one_oddTop h3, h.lie_two_oddTop h2 h3] at e
  simpa [evenTop_eq] using e

/-- `⁅x̄, D⁴ b'⁆ = -4 D c'' + ⁅a₄, b'⁆`. -/
theorem lie_zero_dY_four_oddTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 0, dY k 4 (oddTop c)⁆
      = -((4 : k) • dY k 1 (evenTop (oddTop c))) + ⁅aElt k 4 4, oddTop c⁆ := by
  have e := lie_aElt_dY_four k 0 (oddTop c)
  rw [h.lie_zero_oddTop, h.lie_one_oddTop h3, h.lie_two_oddTop h2 h3] at e
  simpa [evenTop_eq] using e

/-- **`⁅x̄, c''⁆ = 0`**, the first even-layer field for the next even top. -/
theorem lie_zero_evenTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 0, evenTop (oddTop c)⁆ = 0 := by
  have hs := serre_x k (dY k 2 (oddTop c))
  rw [dY_one_dY, h.lie_zero_dY_two_oddTop h3, h.lie_two_oddTop h2 h3,
    h.lie_zero_dY_three_oddTop h2 h3] at hs
  simp only [dY_zero_elt, _root_.lie_zero, smul_zero, sub_zero, lie_neg, neg_eq_zero] at hs
  exact hs

/-- `⁅x̄, D c''⁆ = -⁅a₁, c''⁆`. -/
theorem lie_zero_dY_one_evenTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 0, dY k 1 (evenTop (oddTop c))⁆ = -⁅aElt k 4 1, evenTop (oddTop c)⁆ := by
  rw [lie_aElt_dY_one, h.lie_zero_evenTop h2 h3, dY_zero_elt, zero_sub]

/-- **`D⁅a₄, b'⁆ = 2 D² c''`**: the sixth odd-layer field holds after applying `D`. -/
theorem dY_one_lie_four_oddTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : EvenLayer k c) :
    dY k 1 ⁅aElt k 4 4, oddTop c⁆ = (2 : k) • dY k 2 (evenTop (oddTop c)) := by
  have hs := serre_y k (oddTop c)
  rw [h.dY_five_oddTop h2 h3, h.lie_zero_oddTop, h.lie_one_oddTop h3,
    h.lie_two_oddTop h2 h3] at hs
  simp only [_root_.lie_zero, dY_zero_elt, smul_zero, sub_zero, zero_sub, add_zero] at hs
  rw [← evenTop_eq] at hs
  refine smul_cancel₀ h5 ?_
  linear_combination (norm := module) -hs

/-- **`⁅x̄, ⁅a₄, b'⁆⁆ = -2⁅a₁, c''⁆`**: the sixth odd-layer field also holds after applying
`ad(x̄)`. Together with `dY_one_lie_four_oddTop` this says the defect is central. -/
theorem lie_zero_lie_four_oddTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 0, ⁅aElt k 4 4, oddTop c⁆⁆ = -((2 : k) • ⁅aElt k 4 1, evenTop (oddTop c)⁆) := by
  have hs := serre_x k (dY k 3 (oddTop c))
  rw [dY_one_dY, h.lie_zero_dY_three_oddTop h2 h3, h.lie_zero_dY_four_oddTop h2 h3] at hs
  simp only [lie_neg, h.lie_zero_evenTop h2 h3, neg_zero, dY_zero_elt, sub_zero, lie_add,
    lie_neg, lie_smul, smul_neg, dY_neg_elt] at hs
  rw [h.lie_zero_dY_one_evenTop h2 h3] at hs
  linear_combination (norm := module) hs

/-- `D²⁅a₄, b'⁆ = 2 D³ c''`. -/
theorem dY_two_lie_four_oddTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : EvenLayer k c) :
    dY k 2 ⁅aElt k 4 4, oddTop c⁆ = (2 : k) • dY k 3 (evenTop (oddTop c)) := by
  have e := congrArg (fun v : g k 4 => dY k 1 v) (h.dY_one_lie_four_oddTop h2 h3 h5)
  simpa [dY_one_dY] using e

/-- **`D³ c'' = 0`**: the string of the next even layer again has length three. -/
theorem dY_three_evenTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : EvenLayer k c) : dY k 3 (evenTop (oddTop c)) = 0 := by
  have h10 : (10 : k) ≠ 0 := by
    have h' : (10 : k) = 2 * 5 := by norm_num
    rw [h']; exact mul_ne_zero h2 h5
  have hs := serre_y k (dY k 1 (oddTop c))
  rw [dY_dY_one, ← dY_one_dY, h.dY_five_oddTop h2 h3] at hs
  simp only [dY_zero_elt, _root_.lie_zero] at hs
  have g0 : ⁅aElt k 4 0, dY k 1 (oddTop c)⁆ = 0 := by
    have e := lie_aElt_dY_one k 0 (oddTop c)
    simp only [Nat.zero_add] at e
    rw [e, h.lie_zero_oddTop, h.lie_one_oddTop h3]; simp
  have g1 : ⁅aElt k 4 1, dY k 1 (oddTop c)⁆ = 0 := by
    have e := lie_aElt_dY_one k 1 (oddTop c)
    simp only [Nat.reduceAdd] at e
    rw [e, h.lie_one_oddTop h3, h.lie_two_oddTop h2 h3]; simp
  have g2 : ⁅aElt k 4 2, dY k 1 (oddTop c)⁆ = -evenTop (oddTop c) := by
    have e := lie_aElt_dY_one k 2 (oddTop c)
    simp only [Nat.reduceAdd] at e
    rw [e, h.lie_two_oddTop h2 h3, ← evenTop_eq]; simp
  have g3 : ⁅aElt k 4 3, dY k 1 (oddTop c)⁆
      = dY k 1 (evenTop (oddTop c)) - ⁅aElt k 4 4, oddTop c⁆ := by
    have e := lie_aElt_dY_one k 3 (oddTop c)
    simp only [Nat.reduceAdd] at e
    rw [e, ← evenTop_eq]
  have g4 : ⁅aElt k 4 4, dY k 1 (oddTop c)⁆ = dY k 1 ⁅aElt k 4 4, oddTop c⁆ := by
    have e := lie_aElt_dY_one k 4 (oddTop c)
    simp only [Nat.reduceAdd, lie_aElt_five, sub_zero] at e
    exact e
  rw [g0, g1, g2, g3, g4] at hs
  simp only [dY_zero_elt, smul_zero, dY_neg_elt, dY_sub_elt, dY_dY_one] at hs
  refine eq_zero_of_smul₀ h10 ?_
  linear_combination (norm := module) -hs - (15 : k) • h.dY_two_lie_four_oddTop h2 h3 h5

/-- **`2⁅a₂, c''⁆ = 3 D⁅a₁, c''⁆`**: the third even-layer field for the next even top. -/
theorem two_smul_lie_two_evenTop (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : EvenLayer k c) :
    (2 : k) • ⁅aElt k 4 2, evenTop (oddTop c)⁆
      = (3 : k) • dY k 1 ⁅aElt k 4 1, evenTop (oddTop c)⁆ := by
  have hs := serre_x k (dY k 4 (oddTop c))
  rw [dY_one_dY, h.dY_five_oddTop h2 h3, h.lie_zero_dY_four_oddTop h2 h3] at hs
  simp only [_root_.lie_zero] at hs
  have hP : ⁅aElt k 4 0, -((4 : k) • dY k 1 (evenTop (oddTop c))) + ⁅aElt k 4 4, oddTop c⁆⁆
      = (2 : k) • ⁅aElt k 4 1, evenTop (oddTop c)⁆ := by
    rw [lie_add, lie_neg, lie_smul, h.lie_zero_dY_one_evenTop h2 h3,
      h.lie_zero_lie_four_oddTop h2 h3]
    module
  have hQ : dY k 1 (-((4 : k) • dY k 1 (evenTop (oddTop c))) + ⁅aElt k 4 4, oddTop c⁆)
      = -((2 : k) • dY k 2 (evenTop (oddTop c))) := by
    rw [dY_add_elt, dY_neg_elt, dY_smul_elt, dY_one_dY, h.dY_one_lie_four_oddTop h2 h3 h5]
    module
  rw [hP, hQ] at hs
  have hexp := lie_aElt_dY_two k 0 (evenTop (oddTop c))
  rw [h.lie_zero_evenTop h2 h3] at hexp
  simp only [Nat.zero_add, dY_zero_elt, zero_sub] at hexp
  rw [lie_neg, lie_smul, dY_smul_elt] at hs
  refine smul_cancel₀ h2 ?_
  linear_combination (norm := module) hs - (4 : k) • hexp

/-- **The even-to-odd-to-even step.** The even-layer invariant propagates on its own, two
`t`-degrees at a time: no odd-layer data is needed. -/
theorem step (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (h : EvenLayer k c) :
    EvenLayer k (evenTop (oddTop c)) where
  lie_zero := h.lie_zero_evenTop h2 h3
  dY_top := h.dY_three_evenTop h2 h3 h5
  lie_two := h.two_smul_lie_two_evenTop h2 h3 h5

/-! ### The one missing field is a central element -/

/-- The defect of the sixth odd-layer field, `w = ⁅a₄, b'⁆ - 2 D c''`. -/
noncomputable def defect (c : g k 4) : g k 4 :=
  ⁅aElt k 4 4, oddTop c⁆ - (2 : k) • dY k 1 (evenTop (oddTop c))

/-- **The defect is central in `𝔤₄`.** Both `⁅x̄, w⁆ = 0` and `⁅ȳ, w⁆ = 0`, and the elements
killing `w` form a Lie subalgebra, so the closure principle applies. Consequently the missing
sixth field of the odd layer is *exactly* the statement that `𝔤₄` has no central element in this
bidegree. -/
theorem central_defect (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : EvenLayer k c) (v : g k 4) : ⁅v, defect c⁆ = 0 := by
  have hx : ⁅xb k 4, defect c⁆ = 0 := by
    rw [defect, ← aElt_zero k 4, lie_sub, lie_smul, h.lie_zero_lie_four_oddTop h2 h3,
      h.lie_zero_dY_one_evenTop h2 h3]
    module
  have hy : ⁅yb k 4, defect c⁆ = 0 := by
    rw [defect, ← dY_one, dY_sub_elt, dY_smul_elt, dY_one_dY,
      h.dY_one_lie_four_oddTop h2 h3 h5]
    module
  let M : Submodule k (g k 4) :=
    { carrier := {u | ⁅u, defect c⁆ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [add_lie, ha, hb, add_zero]
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_lie]
      smul_mem' := fun a u hu => by
        simp only [Set.mem_setOf_eq] at hu ⊢; rw [smul_lie, hu, smul_zero] }
  have hM : M = ⊤ := by
    refine eq_top_of_closed_under_ad k 4 M hx hy ?_ ?_
    · intro m hm
      have hm' : ⁅m, defect c⁆ = 0 := hm
      change ⁅⁅xb k 4, m⁆, defect c⁆ = 0
      rw [lie_lie, hm', hx]; simp
    · intro m hm
      have hm' : ⁅m, defect c⁆ = 0 := hm
      change ⁅⁅yb k 4, m⁆, defect c⁆ = 0
      rw [lie_lie, hm', hy]; simp
  have : v ∈ M := by rw [hM]; trivial
  exact this

/-! ### The tower is the orbit of `2 ad(c₀) ∘ D`

The top of the degree-`2` layer, `c₀ = -⁅a₀, a₃⁆`, commutes with every even top and carries each
even top to the next one. -/

/-- `2⁅a₃, D c⁆ = -D³ b'`. -/
theorem two_smul_lie_three_dY_one (h2 : (2 : k) ≠ 0) (h : EvenLayer k c) :
    (2 : k) • ⁅aElt k 4 3, dY k 1 c⁆ = -dY k 3 (oddTop c) := by
  have e := lie_aElt_dY_one k 3 c
  simp only [Nat.reduceAdd] at e
  have hD : dY k 1 ((2 : k) • ⁅aElt k 4 3, c⁆) = (3 : k) • dY k 3 ⁅aElt k 4 1, c⁆ := by
    rw [h.two_smul_lie_three, dY_smul_elt, dY_one_dY]
  rw [dY_smul_elt] at hD
  have hb : dY k 3 (oddTop c) = -dY k 3 ⁅aElt k 4 1, c⁆ := by rw [oddTop_eq, dY_neg_elt]
  linear_combination (norm := module) (2 : k) • e + hD - (2 : k) • h.lie_four h2 + hb

/-- **`⁅c₀, c⁆ = 0`**: the top of the degree-`2` layer commutes with every even top. Both
`⁅x̄, c⁆ = 0` and `⁅a₂, b'⁆ = 0` go into this. -/
theorem lie_lie_a0_a3_self (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅⁅aElt k 4 0, aElt k 4 3⁆, c⁆ = 0 := by
  have hjac : ⁅⁅aElt k 4 0, aElt k 4 3⁆, c⁆
      = ⁅aElt k 4 0, ⁅aElt k 4 3, c⁆⁆ - ⁅aElt k 4 3, ⁅aElt k 4 0, c⁆⁆ := lie_lie _ _ _
  rw [h.lie_zero, _root_.lie_zero, sub_zero] at hjac
  refine eq_zero_of_smul₀ h2 ?_
  rw [hjac, ← lie_smul, h.two_smul_lie_three, lie_smul, lie_one_eq_neg_oddTop, dY_neg_elt,
    lie_neg, h.lie_zero_dY_two_oddTop h3, h.lie_two_oddTop h2 h3]
  module

/-- **`2⁅c₀, D c⁆ = c''`**: bracketing with `c₀` after one `D` sends each even top to the next.
Stated with `⁅a₀, a₃⁆ = -c₀`, so the sign is on the right. -/
theorem two_smul_lie_a0_a3_dY_one (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    (2 : k) • ⁅⁅aElt k 4 0, aElt k 4 3⁆, dY k 1 c⁆ = -evenTop (oddTop c) := by
  have hjac : ⁅aElt k 4 3, oddTop c⁆
      = ⁅⁅aElt k 4 3, aElt k 4 0⁆, dY k 1 c⁆
        + ⁅aElt k 4 0, ⁅aElt k 4 3, dY k 1 c⁆⁆ := by
    rw [← h.lie_zero_dY_one]; exact leibniz_lie _ _ _
  have ha30 : ⁅aElt k 4 3, aElt k 4 0⁆ = -⁅aElt k 4 0, aElt k 4 3⁆ :=
    (lie_skew (aElt k 4 3) (aElt k 4 0)).symm
  have h2s : (2 : k) • ⁅aElt k 4 0, ⁅aElt k 4 3, dY k 1 c⁆⁆ = evenTop (oddTop c) := by
    rw [← lie_smul, h.two_smul_lie_three_dY_one h2, lie_neg,
      h.lie_zero_dY_three_oddTop h2 h3, neg_neg]
  rw [ha30, neg_lie, ← evenTop_eq] at hjac
  linear_combination (norm := module) (2 : k) • hjac + h2s

/-! ### The defect is a single bracket

The three-term expansion of `⁅a₄, b'⁆` obtained by writing `b' = ⁅x̄, D c⁆` and moving `a₄` past
`x̄` collapses the defect to one bracket against the *fixed* degree-`2` element `⁅a₁, a₃⁆`. -/

/-- `⁅a₄, D c⁆ = -D⁴ b'`. -/
theorem lie_four_dY_one (h2 : (2 : k) ≠ 0) (h : EvenLayer k c) :
    ⁅aElt k 4 4, dY k 1 c⁆ = -dY k 4 (oddTop c) := by
  have e := lie_aElt_dY_one k 4 c
  simp only [Nat.reduceAdd, lie_aElt_five, sub_zero] at e
  rw [e, h.lie_four h2, dY_one_dY, lie_one_eq_neg_oddTop, dY_neg_elt]

/-- **The defect is a single bracket:** `defect c = ⁅⁅a₁, a₃⁆, D c⁆`.

Write `b' = ⁅x̄, D c⁆` (`lie_zero_dY_one`) and move `a₄` across the outer bracket:
`⁅a₄, b'⁆ = ⁅⁅a₄, x̄⁆, D c⁆ + ⁅x̄, ⁅a₄, D c⁆⁆`. The first term is `2⁅⁅a₁, a₃⁆, D c⁆` by
`lie_a4_a0`, and the second is `-⁅x̄, D⁴ b'⁆ = 4 D c'' - ⁅a₄, b'⁆` by
`lie_zero_dY_four_oddTop`; solving for `⁅a₄, b'⁆` gives `⁅a₄, b'⁆ = ⁅⁅a₁,a₃⁆, D c⁆ + 2 D c''`. -/
theorem defect_eq (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : EvenLayer k c) :
    defect c = ⁅⁅aElt k 4 1, aElt k 4 3⁆, dY k 1 c⁆ := by
  have hjac : ⁅aElt k 4 4, oddTop c⁆
      = ⁅⁅aElt k 4 4, aElt k 4 0⁆, dY k 1 c⁆
        + ⁅aElt k 4 0, ⁅aElt k 4 4, dY k 1 c⁆⁆ := by
    rw [← h.lie_zero_dY_one]; exact leibniz_lie _ _ _
  rw [lie_a4_a0, smul_lie, h.lie_four_dY_one h2, lie_neg,
    h.lie_zero_dY_four_oddTop h2 h3] at hjac
  rw [defect]
  refine smul_cancel₀ h2 ?_
  linear_combination (norm := module) hjac

end EvenLayer

/-! ### The odd layer, modulo the defect -/

/-- **The even-to-odd step**, given the one field that does not follow from `EvenLayer c`. -/
theorem OddLayer.of_evenLayer (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h : EvenLayer k c) (hgap : EvenLayer.defect c = 0) :
    OddLayer k (oddTop c) (evenTop (oddTop c)) where
  lie_zero := h.lie_zero_oddTop
  lie_one := h.lie_one_oddTop h3
  lie_two := h.lie_two_oddTop h2 h3
  lie_three := rfl
  lie_four := by rwa [EvenLayer.defect, sub_eq_zero] at hgap
  dY_top := h.dY_five_oddTop h2 h3

/-- **The even-to-odd step, from the triviality of the centre.** `𝔤₄` has trivial centre (it is
the positive part of `A₂⁽²⁾`), so this hypothesis is expected to hold; proving it is the one
remaining gap in the layer induction. -/
theorem OddLayer.of_evenLayer_of_center (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : EvenLayer k c) (hZ : ∀ w : g k 4, (∀ v : g k 4, ⁅v, w⁆ = 0) → w = 0) :
    OddLayer k (oddTop c) (evenTop (oddTop c)) :=
  OddLayer.of_evenLayer h2 h3 h (hZ _ (h.central_defect h2 h3 h5))

/-! ### The tower of even layers

Iterating `step` from the degree-`2` layer gives the even-layer invariant in every even
`t`-degree, unconditionally. -/

/-- `evenTower k m` is the top of the layer of `t`-degree `2m + 2`. -/
noncomputable def evenTower (K : Type*) [CommRing K] : ℕ → g K 4
  | 0 => -⁅aElt K 4 0, aElt K 4 3⁆
  | m + 1 => evenTop (oddTop (evenTower K m))

/-- The even-layer tower formula for `evenTower_zero`. -/
@[simp] theorem evenTower_zero (K : Type*) [CommRing K] :
    evenTower K 0 = -⁅aElt K 4 0, aElt K 4 3⁆ := rfl

/-- The even-layer tower formula for `evenTower_succ`. -/
@[simp] theorem evenTower_succ (K : Type*) [CommRing K] (m : ℕ) :
    evenTower K (m + 1) = evenTop (oddTop (evenTower K m)) := rfl

/-- **Every even layer satisfies the even-layer invariant.** No hypothesis beyond
`2, 3, 5 ≠ 0`; in particular `D³` kills the top of every even layer. -/
theorem evenLayer_evenTower (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    EvenLayer k (evenTower k m) := by
  induction m with
  | zero => exact evenLayer_deg_two h2 h5
  | succ m ih => exact ih.step h2 h3 h5

/-- Non-vacuity of the step at the first new degree: the layer of `t`-degree `4`. -/
theorem evenLayer_deg_four (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    EvenLayer k (evenTop (oddTop (-⁅aElt k 4 0, aElt k 4 3⁆))) :=
  evenLayer_evenTower h2 h3 h5 1

/-- **The even tower is the orbit of `2 ad(c₀) ∘ D`.** Every even top is obtained from the
previous one by applying `D` and bracketing with the degree-`2` top `c₀ = evenTower k 0`. -/
theorem two_smul_lie_evenTower_zero_dY_one (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (m : ℕ) :
    (2 : k) • ⁅evenTower k 0, dY k 1 (evenTower k m)⁆ = evenTower k (m + 1) := by
  have h := (evenLayer_evenTower h2 h3 h5 m).two_smul_lie_a0_a3_dY_one h2 h3
  rw [evenTower_zero, evenTower_succ, neg_lie, smul_neg, h, neg_neg]

/-- **`c₀` commutes with the whole even tower.** -/
theorem lie_evenTower_zero_evenTower (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : ⁅evenTower k 0, evenTower k m⁆ = 0 := by
  rw [evenTower_zero, neg_lie,
    (evenLayer_evenTower h2 h3 h5 m).lie_lie_a0_a3_self h2 h3, neg_zero]

/-! ### The odd layer of `t`-degree `3`

`D (evenTower k 0) = ⁅a₁, a₃⁆` is exactly the element the defect brackets against, so at the
bottom of the tower the defect is `⁅⁅a₁, a₃⁆, ⁅a₁, a₃⁆⁆ = 0` and the even-to-odd step goes
through with no hypothesis on the centre. -/

/-- `D(evenTower 0) = ⁅a₁, a₃⁆`: applying `D` to `-⁅a₀, a₃⁆` gives `-⁅a₁,a₃⁆ - ⁅a₀,a₄⁆`, and
`⁅a₀, a₄⁆ = -2⁅a₁, a₃⁆`. -/
theorem dY_one_evenTower_zero : dY k 1 (evenTower k 0) = ⁅aElt k 4 1, aElt k 4 3⁆ := by
  have h := lie_a1_a3_add k
  rw [evenTower_zero, dY_neg_elt, dY_one, lie_yb_lie_aElt]
  linear_combination (norm := module) -h

/-- **The defect vanishes at the bottom of the tower.** `defect (evenTower k 0)` is the bracket
of `⁅a₁, a₃⁆` with itself. -/
theorem defect_evenTower_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    EvenLayer.defect (evenTower k 0) = 0 := by
  rw [(evenLayer_evenTower h2 h3 h5 0).defect_eq h2 h3, dY_one_evenTower_zero, lie_self]

/-- **The layer of `t`-degree `3` satisfies the odd-layer invariant**, unconditionally: the
even-to-odd step is not vacuous, and in particular `⁅a₄, b'⁆ = 2 D c''` really does hold there.
Here `b' = oddTop (evenTower k 0)` is the top of the `t`-degree-`3` layer and
`evenTop b' = evenTower k 1` the top of the `t`-degree-`4` one. -/
theorem oddLayer_deg_three (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    OddLayer k (oddTop (evenTower k 0)) (evenTop (oddTop (evenTower k 0))) :=
  OddLayer.of_evenLayer h2 h3 (evenLayer_evenTower h2 h3 h5 0)
    (defect_evenTower_zero h2 h3 h5)

/-- The remaining gap in the layer induction, in its reduced form: the odd layer above
`evenTower k m` follows from the single vanishing `⁅⁅a₁, a₃⁆, D (evenTower k m)⁆ = 0`.

By `EvenLayer.defect_eq` this is equivalent to the vanishing of the defect, and by
`EvenLayer.central_defect` the bracket is central in `𝔤₄`, so the triviality of the centre of
`𝔤₄` still suffices; but the statement to be proved is now a single bracket of two explicit
elements of the tower rather than a statement about all central elements. -/
theorem oddLayer_evenTower_of_lie_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) (hgap : ⁅⁅aElt k 4 1, aElt k 4 3⁆, dY k 1 (evenTower k m)⁆ = 0) :
    OddLayer k (oddTop (evenTower k m)) (evenTop (oddTop (evenTower k m))) :=
  OddLayer.of_evenLayer h2 h3 (evenLayer_evenTower h2 h3 h5 m)
    (by rw [(evenLayer_evenTower h2 h3 h5 m).defect_eq h2 h3, hgap])

end EvenToOdd

/-!
## The `LoopIdx`-indexed spanning family

`loopFam₄` is the upper-bound counterpart of the graded basis `loopFam` of `𝔫₊`: the same index
type `LoopIdx`, with `1` element in `t`-degree `0`, `5` in each odd degree and `3` in each even
degree `≥ 2`. Together with `range_matHom₄_eq_loopPos` (the matching lower bound) it is the input
needed to turn `matHom₄` into an isomorphism `𝔤₄ ≃ 𝔫₊`.
-/

section Spanning

variable {k : Type*} [Field k]

/-- The top of the layer of `t`-degree `2m+1`: `x̄` at the bottom, and `oddTop` of the previous
even top afterwards. -/
noncomputable def topOdd (K : Type*) [CommRing K] : ℕ → g K 4
  | 0 => xb K 4
  | m + 1 => oddTop (evenTower K m)

/-- The odd-layer top formula for `topOdd_zero`. -/
@[simp] theorem topOdd_zero (K : Type*) [CommRing K] : topOdd K 0 = xb K 4 := rfl

/-- The odd-layer top formula for `topOdd_succ`. -/
@[simp] theorem topOdd_succ (K : Type*) [CommRing K] (m : ℕ) :
    topOdd K (m + 1) = oddTop (evenTower K m) := rfl

/-- The defect of the sixth odd-layer field at the top of `t`-degree `2m+1`:
`w_m = ⁅a₄, topOdd m⁆ - 2 D (evenTower m)`. It vanishes for `m = 0` and `m = 1`, and is always
central; whether it vanishes in general is the triviality of the centre of `𝔤₄`. -/
noncomputable def topDefect (K : Type*) [CommRing K] (m : ℕ) : g K 4 :=
  ⁅aElt K 4 4, topOdd K m⁆ - (2 : K) • dY K 1 (evenTower K m)

/-- The top-defect formula for `topDefect_succ`. -/
theorem topDefect_succ (m : ℕ) : topDefect k (m + 1) = EvenLayer.defect (evenTower k m) := rfl

/-- The defect vanishes at the bottom: `⁅a₄, x̄⁆ = 2⁅a₁, a₃⁆ = 2 D (evenTower 0)`. -/
@[simp] theorem topDefect_zero_eq : topDefect k 0 = 0 := by
  rw [topDefect, topOdd_zero, ← aElt_zero k 4, lie_a4_a0, dY_one_evenTower_zero, sub_self]

/-- The top-defect formula for `topDefect_one`. -/
theorem topDefect_one (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    topDefect k 1 = 0 :=
  defect_evenTower_zero h2 h3 h5

/-- **Every defect is central in `𝔤₄`.** -/
theorem central_topDefect (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ)
    (v : g k 4) : ⁅v, topDefect k m⁆ = 0 := by
  cases m with
  | zero => rw [topDefect_zero_eq, _root_.lie_zero]
  | succ m =>
      rw [topDefect_succ]
      exact (evenLayer_evenTower h2 h3 h5 m).central_defect h2 h3 h5 v

/-- **The odd-layer invariant in every degree**, given the vanishing of the defects. -/
theorem oddLayer_topOdd (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (hgap : ∀ m : ℕ, topDefect k m = 0) (m : ℕ) : OddLayer k (topOdd k m) (evenTower k m) := by
  cases m with
  | zero => exact oddLayer_xb k
  | succ m =>
      exact OddLayer.of_evenLayer h2 h3 (evenLayer_evenTower h2 h3 h5 m) (hgap (m + 1))

/-! ### The family -/

/-- The `LoopIdx`-indexed family in `𝔤₄`: `ȳ` in `t`-degree `0`, the `ad(ȳ)`-string on
`topOdd m` in degree `2m+1`, the `ad(ȳ)`-string on `evenTower m` in degree `2m+2`. -/
noncomputable def loopFam₄ (K : Type*) [CommRing K] : LoopIdx → g K 4
  | .base => yb K 4
  | .odd m i => dY K i (topOdd K m)
  | .even m i => dY K i (evenTower K m)

/-- The rank-four loop-family formula for `loopFam₄_base`. -/
@[simp] theorem loopFam₄_base (K : Type*) [CommRing K] : loopFam₄ K .base = yb K 4 := rfl

/-- The rank-four loop-family formula for `loopFam₄_odd`. -/
@[simp] theorem loopFam₄_odd (K : Type*) [CommRing K] (m : ℕ) (i : Fin 5) :
    loopFam₄ K (.odd m i) = dY K i (topOdd K m) := rfl

/-- The rank-four loop-family formula for `loopFam₄_even`. -/
@[simp] theorem loopFam₄_even (K : Type*) [CommRing K] (m : ℕ) (i : Fin 3) :
    loopFam₄ K (.even m i) = dY K i (evenTower K m) := rfl

/-- The family together with the defects. -/
noncomputable def loopSet (K : Type*) [CommRing K] : Set (g K 4) :=
  Set.range (loopFam₄ K) ∪ Set.range (topDefect K)

/-- The rank-four loop-family formula for `loopFam₄_mem_loopSet`. -/
theorem loopFam₄_mem_loopSet (I : LoopIdx) : loopFam₄ k I ∈ loopSet k := Or.inl ⟨I, rfl⟩

/-- The top-defect formula for `topDefect_mem_loopSet`. -/
theorem topDefect_mem_loopSet (m : ℕ) : topDefect k m ∈ loopSet k := Or.inr ⟨m, rfl⟩

/-- The loop set consists exactly of the distinguished loop-family vectors. -/
theorem mem_loopSet {v : g k 4} (h : v ∈ loopSet k) :
    (∃ I, loopFam₄ k I = v) ∨ ∃ m, topDefect k m = v := h

/-! ### The `ad(ȳ)`-strings have the right lengths -/

/-- The adjoint-y iteration formula for `dY_five_topOdd`. -/
theorem dY_five_topOdd (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    dY k 5 (topOdd k m) = 0 := by
  cases m with
  | zero => rw [topOdd_zero, dY_xb, aElt_five_eq_zero]
  | succ m => exact (evenLayer_evenTower h2 h3 h5 m).dY_five_oddTop h2 h3

/-- The adjoint-y iteration formula for `dY_three_evenTower`. -/
theorem dY_three_evenTower (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    dY k 3 (evenTower k m) = 0 :=
  (evenLayer_evenTower h2 h3 h5 m).dY_top

/-! ### The `ad(x̄)` table along the strings -/

/-- The bracket identity for `lie_zero_topOdd`. -/
theorem lie_zero_topOdd (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    ⁅aElt k 4 0, topOdd k m⁆ = 0 := by
  cases m with
  | zero => rw [topOdd_zero, ← aElt_zero k 4, lie_self]
  | succ m => exact (evenLayer_evenTower h2 h3 h5 m).lie_zero_oddTop

/-- The bracket identity for `lie_zero_dY_one_topOdd`. -/
theorem lie_zero_dY_one_topOdd (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    ⁅aElt k 4 0, dY k 1 (topOdd k m)⁆ = 0 := by
  cases m with
  | zero => rw [topOdd_zero, dY_xb, lie_a0_a1]
  | succ m =>
      have h := evenLayer_evenTower h2 h3 h5 m
      rw [topOdd_succ, h.lie_zero_dY_one_oddTop, h.lie_one_oddTop h3, neg_zero]

/-- The bracket identity for `lie_zero_dY_two_topOdd`. -/
theorem lie_zero_dY_two_topOdd (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    ⁅aElt k 4 0, dY k 2 (topOdd k m)⁆ = 0 := by
  cases m with
  | zero => rw [topOdd_zero, dY_xb, lie_a0_a2]
  | succ m =>
      have h := evenLayer_evenTower h2 h3 h5 m
      rw [topOdd_succ, h.lie_zero_dY_two_oddTop h3, h.lie_two_oddTop h2 h3]

/-- `⁅x̄, D³ (topOdd m)⁆ = -evenTower m`: the third step of the string reaches the next even top. -/
theorem lie_zero_dY_three_topOdd (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : ⁅aElt k 4 0, dY k 3 (topOdd k m)⁆ = -evenTower k m := by
  cases m with
  | zero => rw [topOdd_zero, dY_xb, evenTower_zero, neg_neg]
  | succ m => exact (evenLayer_evenTower h2 h3 h5 m).lie_zero_dY_three_oddTop h2 h3

/-- `⁅x̄, D⁴ (topOdd m)⁆ = -2 D (evenTower m) + w_m`: the only place where the defect appears. -/
theorem lie_zero_dY_four_topOdd (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : ⁅aElt k 4 0, dY k 4 (topOdd k m)⁆
      = -((2 : k) • dY k 1 (evenTower k m)) + topDefect k m := by
  have key : ⁅aElt k 4 0, dY k 4 (topOdd k m)⁆
      = -((4 : k) • dY k 1 (evenTower k m)) + ⁅aElt k 4 4, topOdd k m⁆ := by
    cases m with
    | zero =>
        have hd : dY k 1 (evenTower k 0) = ⁅aElt k 4 1, aElt k 4 3⁆ := dY_one_evenTower_zero
        have h04 : ⁅aElt k 4 0, aElt k 4 4⁆ = -((2 : k) • ⁅aElt k 4 1, aElt k 4 3⁆) := by
          rw [← two_smul_dY_lie_a0_a3]
          have hneg : dY k 1 ⁅aElt k 4 0, aElt k 4 3⁆ = -dY k 1 (evenTower k 0) := by
            rw [evenTower_zero, dY_neg_elt, neg_neg]
          rw [hneg, hd, smul_neg]
        rw [topOdd_zero, dY_xb, ← aElt_zero k 4, lie_a4_a0, hd, h04]
        module
    | succ m => exact (evenLayer_evenTower h2 h3 h5 m).lie_zero_dY_four_oddTop h2 h3
  rw [key, topDefect]
  module

/-- The bracket identity for `lie_zero_evenTower`. -/
theorem lie_zero_evenTower (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    ⁅aElt k 4 0, evenTower k m⁆ = 0 :=
  (evenLayer_evenTower h2 h3 h5 m).lie_zero

/-- `⁅x̄, D (evenTower m)⁆` is the top of the next odd layer. -/
theorem lie_zero_dY_one_evenTower (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : ⁅aElt k 4 0, dY k 1 (evenTower k m)⁆ = topOdd k (m + 1) :=
  (evenLayer_evenTower h2 h3 h5 m).lie_zero_dY_one

/-- The even-tower bracket identity after two adjoint-y steps. -/
theorem two_smul_lie_zero_dY_two_evenTower (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : (2 : k) • ⁅aElt k 4 0, dY k 2 (evenTower k m)⁆ = dY k 1 (topOdd k (m + 1)) :=
  (evenLayer_evenTower h2 h3 h5 m).two_smul_lie_zero_dY_two

/-! ### The spanning theorems -/

/-- **The family together with the defects spans `𝔤₄`**, unconditionally.

Every closure obligation of `span_eq_top_of_closed_under_ad` is a line of the layer calculus:
`ad(ȳ)` walks along each string and falls off its end (`dY_five_topOdd`, `dY_three_evenTower`),
while `ad(x̄)` kills the first three entries of an odd string, produces the next even top at the
fourth (`lie_zero_dY_three_topOdd`) and its `ad(ȳ)`-image at the fifth up to the defect
(`lie_zero_dY_four_topOdd`), and climbs back from an even string to the next odd top
(`lie_zero_dY_one_evenTower`). -/
theorem span_loopSet_eq_top (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    Submodule.span k (loopSet k) = ⊤ := by
  have hF : ∀ I : LoopIdx, loopFam₄ k I ∈ Submodule.span k (loopSet k) := fun I =>
    Submodule.subset_span (loopFam₄_mem_loopSet I)
  have hW : ∀ m : ℕ, topDefect k m ∈ Submodule.span k (loopSet k) := fun m =>
    Submodule.subset_span (topDefect_mem_loopSet m)
  refine span_eq_top_of_closed_under_ad k 4 (loopSet k)
    (loopFam₄_mem_loopSet (LoopIdx.odd 0 0)) (loopFam₄_mem_loopSet LoopIdx.base) ?_ ?_
  · rintro s hs
    rcases mem_loopSet hs with ⟨I, rfl⟩ | ⟨m, rfl⟩
    · cases I with
      | base =>
          change ⁅aElt k 4 0, yb k 4⁆ ∈ Submodule.span k (loopSet k)
          have hb : ⁅aElt k 4 0, yb k 4⁆ = -dY k 1 (topOdd k 0) := by
            rw [topOdd_zero, dY_one, aElt_zero, ← lie_skew]
          rw [hb]
          exact neg_mem (hF (LoopIdx.odd 0 1))
      | odd m i =>
          fin_cases i
          · change ⁅aElt k 4 0, topOdd k m⁆ ∈ Submodule.span k (loopSet k)
            rw [lie_zero_topOdd h2 h3 h5 m]
            exact Submodule.zero_mem _
          · change ⁅aElt k 4 0, dY k 1 (topOdd k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [lie_zero_dY_one_topOdd h2 h3 h5 m]
            exact Submodule.zero_mem _
          · change ⁅aElt k 4 0, dY k 2 (topOdd k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [lie_zero_dY_two_topOdd h2 h3 h5 m]
            exact Submodule.zero_mem _
          · change ⁅aElt k 4 0, dY k 3 (topOdd k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [lie_zero_dY_three_topOdd h2 h3 h5 m]
            exact neg_mem (hF (LoopIdx.even m 0))
          · change ⁅aElt k 4 0, dY k 4 (topOdd k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [lie_zero_dY_four_topOdd h2 h3 h5 m]
            exact add_mem (neg_mem (Submodule.smul_mem _ _ (hF (LoopIdx.even m 1)))) (hW m)
      | even m i =>
          fin_cases i
          · change ⁅aElt k 4 0, evenTower k m⁆ ∈ Submodule.span k (loopSet k)
            rw [lie_zero_evenTower h2 h3 h5 m]
            exact Submodule.zero_mem _
          · change ⁅aElt k 4 0, dY k 1 (evenTower k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [lie_zero_dY_one_evenTower h2 h3 h5 m]
            exact hF (LoopIdx.odd (m + 1) 0)
          · change ⁅aElt k 4 0, dY k 2 (evenTower k m)⁆ ∈ Submodule.span k (loopSet k)
            have hhalf : ⁅aElt k 4 0, dY k 2 (evenTower k m)⁆
                = (2 : k)⁻¹ • dY k 1 (topOdd k (m + 1)) := by
              rw [← two_smul_lie_zero_dY_two_evenTower h2 h3 h5 m, smul_smul,
                inv_mul_cancel₀ h2, one_smul]
            rw [hhalf]
            exact Submodule.smul_mem _ _ (hF (LoopIdx.odd (m + 1) 1))
    · change ⁅xb k 4, topDefect k m⁆ ∈ Submodule.span k (loopSet k)
      rw [central_topDefect h2 h3 h5 m]
      exact Submodule.zero_mem _
  · rintro s hs
    rcases mem_loopSet hs with ⟨I, rfl⟩ | ⟨m, rfl⟩
    · cases I with
      | base =>
          change ⁅yb k 4, yb k 4⁆ ∈ Submodule.span k (loopSet k)
          rw [lie_self]
          exact Submodule.zero_mem _
      | odd m i =>
          fin_cases i
          · change ⁅yb k 4, dY k 0 (topOdd k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [← dY_succ]
            exact hF (LoopIdx.odd m 1)
          · change ⁅yb k 4, dY k 1 (topOdd k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [← dY_succ]
            exact hF (LoopIdx.odd m 2)
          · change ⁅yb k 4, dY k 2 (topOdd k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [← dY_succ]
            exact hF (LoopIdx.odd m 3)
          · change ⁅yb k 4, dY k 3 (topOdd k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [← dY_succ]
            exact hF (LoopIdx.odd m 4)
          · change ⁅yb k 4, dY k 4 (topOdd k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [← dY_succ]
            rw [show dY k (4 + 1) (topOdd k m) = dY k 5 (topOdd k m) from rfl,
              dY_five_topOdd h2 h3 h5 m]
            exact Submodule.zero_mem _
      | even m i =>
          fin_cases i
          · change ⁅yb k 4, dY k 0 (evenTower k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [← dY_succ]
            exact hF (LoopIdx.even m 1)
          · change ⁅yb k 4, dY k 1 (evenTower k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [← dY_succ]
            exact hF (LoopIdx.even m 2)
          · change ⁅yb k 4, dY k 2 (evenTower k m)⁆ ∈ Submodule.span k (loopSet k)
            rw [← dY_succ]
            rw [show dY k (2 + 1) (evenTower k m) = dY k 3 (evenTower k m) from rfl,
              dY_three_evenTower h2 h3 h5 m]
            exact Submodule.zero_mem _
    · change ⁅yb k 4, topDefect k m⁆ ∈ Submodule.span k (loopSet k)
      rw [central_topDefect h2 h3 h5 m]
      exact Submodule.zero_mem _

/-- **The `LoopIdx`-indexed family spans `𝔤₄`**, once the defects vanish. This is the upper bound
of Problem 2.16.3(b): `𝔤₄` is spanned by `1` element in `t`-degree `0`, `5` in each odd degree and
`3` in each even degree `≥ 2`, matching the graded basis of `𝔫₊ ⊆ A₂⁽²⁾`. -/
theorem span_range_loopFam₄_eq_top (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (hgap : ∀ m : ℕ, topDefect k m = 0) :
    Submodule.span k (Set.range (loopFam₄ k)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← span_loopSet_eq_top h2 h3 h5, Submodule.span_le]
  intro v hv
  rcases mem_loopSet hv with ⟨I, rfl⟩ | ⟨m, rfl⟩
  · exact Submodule.subset_span ⟨I, rfl⟩
  · rw [hgap m]
    exact Submodule.zero_mem _

/-- **The family spans as soon as `𝔤₄` has trivial centre**, since every defect is central. -/
theorem span_range_loopFam₄_eq_top_of_center (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (hZ : ∀ w : g k 4, (∀ v : g k 4, ⁅v, w⁆ = 0) → w = 0) :
    Submodule.span k (Set.range (loopFam₄ k)) = ⊤ :=
  span_range_loopFam₄_eq_top h2 h3 h5 fun m => hZ _ (central_topDefect h2 h3 h5 m)

/-! ### The graded dimensions `1, 5, 3, 5, 3, …` -/

/-- Only the base index sits in `t`-degree `0`. -/
theorem card_loopIdx_deg_zero : Nat.card {I : LoopIdx // I.deg = 0} = 1 := by
  have hbij : Function.Bijective
      (fun _ : Unit => (⟨LoopIdx.base, rfl⟩ : {I : LoopIdx // I.deg = 0})) := by
    refine ⟨fun a b _ => Subsingleton.elim a b, ?_⟩
    rintro ⟨I, hI⟩
    cases I with
    | base => exact ⟨(), rfl⟩
    | odd m i => rw [LoopIdx.deg] at hI; omega
    | even m i => rw [LoopIdx.deg] at hI; omega
  simpa using (Nat.card_eq_of_bijective _ hbij).symm

/-- Five indices in each odd `t`-degree `2m+1`. -/
theorem card_loopIdx_deg_odd (m : ℕ) : Nat.card {I : LoopIdx // I.deg = 2 * m + 1} = 5 := by
  have hbij : Function.Bijective
      (fun i : Fin 5 => (⟨LoopIdx.odd m i, rfl⟩ : {I : LoopIdx // I.deg = 2 * m + 1})) := by
    refine ⟨fun i j hij => by simpa using hij, ?_⟩
    rintro ⟨I, hI⟩
    cases I with
    | base => rw [LoopIdx.deg] at hI; omega
    | odd m' i =>
        have hm : m' = m := by rw [LoopIdx.deg] at hI; omega
        subst hm
        exact ⟨i, rfl⟩
    | even m' i => rw [LoopIdx.deg] at hI; omega
  simpa using (Nat.card_eq_of_bijective _ hbij).symm

/-- Three indices in each even `t`-degree `2m+2`. -/
theorem card_loopIdx_deg_even (m : ℕ) : Nat.card {I : LoopIdx // I.deg = 2 * m + 2} = 3 := by
  have hbij : Function.Bijective
      (fun i : Fin 3 => (⟨LoopIdx.even m i, rfl⟩ : {I : LoopIdx // I.deg = 2 * m + 2})) := by
    refine ⟨fun i j hij => by simpa using hij, ?_⟩
    rintro ⟨I, hI⟩
    cases I with
    | base => rw [LoopIdx.deg] at hI; omega
    | odd m' i => rw [LoopIdx.deg] at hI; omega
    | even m' i =>
        have hm : m' = m := by rw [LoopIdx.deg] at hI; omega
        subst hm
        exact ⟨i, rfl⟩
  simpa using (Nat.card_eq_of_bijective _ hbij).symm

end Spanning

end Etingof.Problem2_16_3

-- The source-numbered exercise namespace and established API contain intentional underscores.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_16_3.dY
  Etingof.Problem2_16_3.oddTop
  Etingof.Problem2_16_3.evenTop
  Etingof.Problem2_16_3.EvenLayer.defect
  Etingof.Problem2_16_3.evenTower
  Etingof.Problem2_16_3.topOdd
  Etingof.Problem2_16_3.topDefect
  Etingof.Problem2_16_3.loopFam₄
  Etingof.Problem2_16_3.loopSet

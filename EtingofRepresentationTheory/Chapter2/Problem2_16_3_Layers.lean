import EtingofRepresentationTheory.Chapter2.Problem2_16_3

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

## What is still missing

The even-to-odd step (from `EvenLayer c` back to `OddLayer (-⁅a₁, c⁆) _`) and the assembly of the
spanning family indexed by `LoopIdx`. Note that the even-to-odd step needs more than `EvenLayer c`
alone: the vanishing `⁅a₁, ⁅a₁, c⁆⁆ = 0` is not a formal consequence of the commutation relations
and the even-layer table, and has to be derived using the *previous* odd top `b` as well
(through `⁅⁅a₁, a₄⁆, b⁆`), so the induction has to carry the pair `(b, c)`.
-/

namespace Etingof.Problem2_16_3

variable (k : Type*) [CommRing k]

/-! ## `ad(ȳ)` iterated -/

/-- `dY k j = ad(ȳ)ʲ`, as a function on `𝔤₄`; `aElt k 4 j = dY k j (x̄)`. -/
noncomputable def dY (j : ℕ) (u : g k 4) : g k 4 := (fun v => ⁅yb k 4, v⁆)^[j] u

@[simp] theorem dY_zero_index (u : g k 4) : dY k 0 u = u := rfl

theorem dY_one (u : g k 4) : dY k 1 u = ⁅yb k 4, u⁆ := rfl

theorem dY_two_eq (u : g k 4) : dY k 2 u = ⁅yb k 4, ⁅yb k 4, u⁆⁆ := rfl

theorem dY_three_eq (u : g k 4) : dY k 3 u = ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, u⁆⁆⁆ := rfl

theorem dY_four_eq (u : g k 4) :
    dY k 4 u = ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, u⁆⁆⁆⁆ := rfl

theorem dY_five_eq (u : g k 4) :
    dY k 5 u = ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, ⁅yb k 4, u⁆⁆⁆⁆⁆ := rfl

theorem dY_succ (j : ℕ) (u : g k 4) : dY k (j + 1) u = ⁅yb k 4, dY k j u⁆ :=
  Function.iterate_succ_apply' _ _ _

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

@[simp] theorem dY_add_elt (j : ℕ) (u v : g k 4) : dY k j (u + v) = dY k j u + dY k j v := by
  induction j with
  | zero => rfl
  | succ j ih => rw [dY_succ, dY_succ, dY_succ, ih, lie_add]

@[simp] theorem dY_zero_elt (j : ℕ) : dY k j (0 : g k 4) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [dY_succ, ih, lie_zero]

@[simp] theorem dY_neg_elt (j : ℕ) (u : g k 4) : dY k j (-u) = -dY k j u := by
  induction j with
  | zero => rfl
  | succ j ih => rw [dY_succ, dY_succ, ih, lie_neg]

@[simp] theorem dY_sub_elt (j : ℕ) (u v : g k 4) : dY k j (u - v) = dY k j u - dY k j v := by
  rw [sub_eq_add_neg, dY_add_elt, dY_neg_elt, sub_eq_add_neg]

@[simp] theorem dY_smul_elt (j : ℕ) (a : k) (u : g k 4) : dY k j (a • u) = a • dY k j u := by
  induction j with
  | zero => rfl
  | succ j ih => rw [dY_succ, dY_succ, ih, lie_smul]

theorem dY_xb (j : ℕ) : dY k j (xb k 4) = aElt k 4 j := rfl

/-! ## The Leibniz expansions -/

/-- **Leibniz.** `⁅aᵢ, ⁅ȳ, u⁆⁆ = ⁅ȳ, ⁅aᵢ, u⁆⁆ - ⁅aᵢ₊₁, u⁆`, from the Jacobi identity and
`aᵢ₊₁ = ⁅ȳ, aᵢ⁆`. Everything in this file is generated by this one identity. -/
theorem lie_aElt_lie_yb (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, ⁅yb k 4, u⁆⁆ = ⁅yb k 4, ⁅aElt k 4 i, u⁆⁆ - ⁅aElt k 4 (i + 1), u⁆ := by
  have h := leibniz_lie (yb k 4) (aElt k 4 i) u
  rw [← aElt_succ] at h
  rw [h]; abel

theorem lie_aElt_dY_one (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, dY k 1 u⁆ = dY k 1 ⁅aElt k 4 i, u⁆ - ⁅aElt k 4 (i + 1), u⁆ := by
  simp only [dY_one]; exact lie_aElt_lie_yb k i u

theorem lie_aElt_dY_two (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, dY k 2 u⁆
      = dY k 2 ⁅aElt k 4 i, u⁆ - (2 : k) • dY k 1 ⁅aElt k 4 (i + 1), u⁆
        + ⁅aElt k 4 (i + 2), u⁆ := by
  simp only [dY_two_eq, dY_one, lie_aElt_lie_yb, lie_sub, Nat.add_assoc, Nat.reduceAdd]
  module

theorem lie_aElt_dY_three (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, dY k 3 u⁆
      = dY k 3 ⁅aElt k 4 i, u⁆ - (3 : k) • dY k 2 ⁅aElt k 4 (i + 1), u⁆
        + (3 : k) • dY k 1 ⁅aElt k 4 (i + 2), u⁆ - ⁅aElt k 4 (i + 3), u⁆ := by
  simp only [dY_three_eq, dY_two_eq, dY_one, lie_aElt_lie_yb, lie_sub, Nat.add_assoc,
    Nat.reduceAdd]
  module

theorem lie_aElt_dY_four (i : ℕ) (u : g k 4) :
    ⁅aElt k 4 i, dY k 4 u⁆
      = dY k 4 ⁅aElt k 4 i, u⁆ - (4 : k) • dY k 3 ⁅aElt k 4 (i + 1), u⁆
        + (6 : k) • dY k 2 ⁅aElt k 4 (i + 2), u⁆
        - (4 : k) • dY k 1 ⁅aElt k 4 (i + 3), u⁆ + ⁅aElt k 4 (i + 4), u⁆ := by
  simp only [dY_four_eq, dY_three_eq, dY_two_eq, dY_one, lie_aElt_lie_yb, lie_sub,
    Nat.add_assoc, Nat.reduceAdd]
  module

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

theorem lie_one_eq_neg_oddTop (c : g k 4) : ⁅aElt k 4 1, c⁆ = -oddTop c := by
  rw [oddTop, neg_neg]

theorem oddTop_eq (c : g k 4) : oddTop c = -⁅aElt k 4 1, c⁆ := rfl

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
  simp only [_root_.lie_zero, dY_zero_elt, smul_zero, sub_zero, zero_sub, add_zero,
    zero_add, neg_zero] at hs
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

end EvenLayer

end EvenToOdd

end Etingof.Problem2_16_3

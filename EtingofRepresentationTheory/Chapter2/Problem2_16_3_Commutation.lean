import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Bidegree


/-!
# The commutation table of the tower of `𝔤₄`, forced by the bidegree grading

`EtingofRepresentationTheory/Chapter2/Problem2_16_3_Bidegree.lean` shows that the bidegrees
occupied by `𝔤₄` are exactly the ones carrying a member of the spanning family `loopFam₄`
(together with the imaginary ray, where the layer defect also sits). Read contrapositively that
is a *vanishing* theorem: any bracket whose bidegree misses the family is zero, with no
computation at all.

This file collects the two shapes in which the vanishing is used —
`gDeg_even_eq_bot` for bidegrees `(2M+2, r)` with `r ∉ [4M+3, 4M+5]`, and `gDeg_odd_eq_bot` for
`(2M+1, r)` with `r ∉ [4M, 4M+4]` — and cashes them in on the tower:

* `lie_evenTower_evenTower` — **every pair of even tops commutes**, `⁅cᵢ, cⱼ⁆ = 0`. This
  generalises `lie_evenTower_zero_evenTower` (the case `i = 0`) from the layer calculus to all
  pairs, and it needs no layer data: the bracket simply has nowhere to live.
* `lie_dY_two_evenTower_dY_two_evenTower` — `⁅D²cᵢ, D²cⱼ⁆ = 0`, likewise.
* `lie_dY_topOdd_dY_topOdd` — `⁅Dᵃ bₚ, Dᵇ b_q⁆ = 0` for the odd tops whenever `a + b ∉ [3, 5]`.

Applying the Leibniz rule for `D = ad(ȳ)` (`dY_one_lie`, `dY_two_lie`, `dY_three_lie`) to
`⁅cᵢ, cⱼ⁆ = 0` then turns these free vanishings into identities on the imaginary ray:

* `lie_dY_one_dY_two_evenTower_comm` — `⁅Dcᵢ, D²cⱼ⁆` is **symmetric** in `i, j` (from `D³`);
* `two_smul_lie_dY_one_evenTower` — `2⁅Dcᵢ, Dcⱼ⁆ = ⁅cⱼ, D²cᵢ⁆ - ⁅cᵢ, D²cⱼ⁆` (from `D²`).

Since `topDefect k (m+1) = ⁅Dc₀, Dc_m⁆` (`topDefect_succ_eq_lie`), the second identity is a new
closed form for the layer defect,

`2 · topDefect k (m+1) = ⁅c_m, D²c₀⁆ - ⁅c₀, D²c_m⁆`  (`two_smul_topDefect_succ`),

while the same Leibniz expansion of the tower recursion `c_{m+1} = 2⁅c₀, Dc_m⁆` gives the *sum*

`D c_{m+1} = ⁅c_m, D²c₀⁆ + ⁅c₀, D²c_m⁆`  (`dY_one_evenTower_succ_eq`).

So the whole remaining gap in Problem 2.16.3(b) is the statement that the pairing
`(i, j) ↦ ⁅cᵢ, D²cⱼ⁆` is symmetric at `(0, m)` — `topDefect_eq_zero_iff_lie_dY_two_comm`. Its
antisymmetric part is the defect and its symmetric part is `D c_{m+1}`, which is the sharpest
form the gap has taken so far: one scalar per imaginary bidegree, not a bracket identity.

Note that `⁅Dcᵢ, D²cⱼ⁆` *is* symmetric (first bullet), and that the analogous
`⁅D²cᵢ, D²cⱼ⁆` vanishes outright; it is exactly one rung lower on the `D`-string that the
symmetry fails to be forced. -/

namespace Etingof.Problem2_16_3

section Leibniz

variable (k : Type*) [CommRing k]

/-- **`D = ad(ȳ)` is a derivation.** -/
theorem dY_one_lie (u v : g k 4) : dY k 1 ⁅u, v⁆ = ⁅dY k 1 u, v⁆ + ⁅u, dY k 1 v⁆ := by
  simp only [dY_one]
  exact leibniz_lie _ _ _

/-- The `D²` Leibniz rule. -/
theorem dY_two_lie (u v : g k 4) :
    dY k 2 ⁅u, v⁆ = ⁅dY k 2 u, v⁆ + (2 : k) • ⁅dY k 1 u, dY k 1 v⁆ + ⁅u, dY k 2 v⁆ := by
  have e : dY k 1 (dY k 1 ⁅u, v⁆) = dY k 2 ⁅u, v⁆ := dY_one_dY k 1 _
  have eu : dY k 1 (dY k 1 u) = dY k 2 u := dY_one_dY k 1 _
  have ev : dY k 1 (dY k 1 v) = dY k 2 v := dY_one_dY k 1 _
  rw [← e, dY_one_lie, dY_add_elt, dY_one_lie, dY_one_lie, eu, ev]
  module

/-- The `D³` Leibniz rule. -/
theorem dY_three_lie (u v : g k 4) :
    dY k 3 ⁅u, v⁆ = ⁅dY k 3 u, v⁆ + (3 : k) • ⁅dY k 2 u, dY k 1 v⁆
      + (3 : k) • ⁅dY k 1 u, dY k 2 v⁆ + ⁅u, dY k 3 v⁆ := by
  have e : dY k 1 (dY k 2 ⁅u, v⁆) = dY k 3 ⁅u, v⁆ := dY_one_dY k 2 _
  have eu : dY k 1 (dY k 2 u) = dY k 3 u := dY_one_dY k 2 _
  have ev : dY k 1 (dY k 2 v) = dY k 3 v := dY_one_dY k 2 _
  have eu1 : dY k 1 (dY k 1 u) = dY k 2 u := dY_one_dY k 1 _
  have ev1 : dY k 1 (dY k 1 v) = dY k 2 v := dY_one_dY k 1 _
  rw [← e, dY_two_lie, dY_add_elt, dY_add_elt, dY_smul_elt, dY_one_lie, dY_one_lie, dY_one_lie,
    eu, ev, eu1, ev1]
  module

end Leibniz

/-! ## Bidegrees the algebra misses

`gDeg_eq_bot` says `𝔤₄` vanishes in every bidegree that neither `loopFam₄` nor a defect occupies.
Along a fixed `t`-degree the occupied `y`-degrees form a short interval, so the criterion becomes
an arithmetic side condition. -/

section Bot

variable {k : Type*} [Field k]

/-- An element of a trivial homogeneous component is zero. -/
theorem eq_zero_of_gDeg_eq_bot {p : ℕ × ℕ} {u : g k 4} (h : gDeg k 4 p = ⊥)
    (hu : u ∈ gDeg k 4 p) : u = 0 := by
  rw [h] at hu
  simpa using hu

/-- **In `t`-degree `2M+2` the algebra lives only in `y`-degrees `4M+3, 4M+4, 4M+5`.** -/
theorem gDeg_even_eq_bot (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (M r : ℕ)
    (hr : r < 4 * M + 3 ∨ 4 * M + 5 < r) : gDeg k 4 (2 * M + 2, r) = ⊥ := by
  refine gDeg_eq_bot h2 h3 h5 _ ?_ ?_
  · rintro (_ | ⟨m, i⟩ | ⟨m, i⟩) h
    · rw [bideg_base, Prod.mk.injEq] at h; omega
    · rw [bideg_odd, Prod.mk.injEq] at h; omega
    · rw [bideg_even, Prod.mk.injEq] at h
      have := i.isLt
      omega
  · intro m h
    rw [Prod.mk.injEq] at h
    omega

/-- **In `t`-degree `2M+1` the algebra lives only in `y`-degrees `4M, …, 4M+4`.** -/
theorem gDeg_odd_eq_bot (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (M r : ℕ)
    (hr : r < 4 * M ∨ 4 * M + 4 < r) : gDeg k 4 (2 * M + 1, r) = ⊥ := by
  refine gDeg_eq_bot h2 h3 h5 _ ?_ ?_
  · rintro (_ | ⟨m, i⟩ | ⟨m, i⟩) h
    · rw [bideg_base, Prod.mk.injEq] at h; omega
    · rw [bideg_odd, Prod.mk.injEq] at h
      have := i.isLt
      omega
    · rw [bideg_even, Prod.mk.injEq] at h; omega
  · intro m h
    rw [Prod.mk.injEq] at h
    omega

end Bot

/-! ## The free part of the commutation table -/

section Table

variable {k : Type*} [Field k]

/-- **Every pair of even tops commutes.** `⁅cᵢ, cⱼ⁆` would have bidegree `(2(i+j+1)+2,
4(i+j+1)+2)`, one rung *below* the bottom `4(i+j+1)+3` of the layer in that `t`-degree, so it is
zero for grading reasons alone. This generalises `lie_evenTower_zero_evenTower`. -/
theorem lie_evenTower_evenTower (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (i j : ℕ) : ⁅evenTower k i, evenTower k j⁆ = 0 := by
  have hmem := lie_mem_gDeg k (evenTower_mem_gDeg k i) (evenTower_mem_gDeg k j)
  rw [show ((2 * i + 2, 4 * i + 3) + (2 * j + 2, 4 * j + 3) : ℕ × ℕ)
      = (2 * (i + j + 1) + 2, 4 * i + 4 * j + 6) by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega] at hmem
  exact eq_zero_of_gDeg_eq_bot (gDeg_even_eq_bot h2 h3 h5 _ _ (Or.inl (by omega))) hmem

/-- **The tops of the `D`-strings of two even layers commute.** `⁅D²cᵢ, D²cⱼ⁆` would sit one rung
*above* the top of the layer in its `t`-degree. -/
theorem lie_dY_two_evenTower_dY_two_evenTower (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (i j : ℕ) :
    ⁅dY k 2 (evenTower k i), dY k 2 (evenTower k j)⁆ = 0 := by
  have hmem := lie_mem_gDeg k (dY_mem_gDeg k 2 (evenTower_mem_gDeg k i))
    (dY_mem_gDeg k 2 (evenTower_mem_gDeg k j))
  rw [show ((2 * i + 2, 4 * i + 3 + 2) + (2 * j + 2, 4 * j + 3 + 2) : ℕ × ℕ)
      = (2 * (i + j + 1) + 2, 4 * i + 4 * j + 10) by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega] at hmem
  exact eq_zero_of_gDeg_eq_bot (gDeg_even_eq_bot h2 h3 h5 _ _ (Or.inr (by omega))) hmem

/-- **Brackets of two odd `D`-strings vanish off the middle three rungs.** `⁅Dᵃ bₚ, Dᵇ b_q⁆` lands
in `t`-degree `2(p+q)+2`, whose layer occupies `y`-degrees `4(p+q)+3, 4(p+q)+4, 4(p+q)+5`; the
bracket has `y`-degree `4(p+q)+a+b`, so everything with `a + b ∉ [3, 5]` is zero. -/
theorem lie_dY_topOdd_dY_topOdd (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (p q a b : ℕ) (hab : a + b < 3 ∨ 5 < a + b) :
    ⁅dY k a (topOdd k p), dY k b (topOdd k q)⁆ = 0 := by
  have hmem := lie_mem_gDeg k (dY_mem_gDeg k a (topOdd_mem_gDeg k p))
    (dY_mem_gDeg k b (topOdd_mem_gDeg k q))
  rw [show ((2 * p + 1, 4 * p + a) + (2 * q + 1, 4 * q + b) : ℕ × ℕ)
      = (2 * (p + q) + 2, 4 * p + 4 * q + (a + b)) by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega] at hmem
  refine eq_zero_of_gDeg_eq_bot (gDeg_even_eq_bot h2 h3 h5 _ _ ?_) hmem
  rcases hab with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end Table

/-! ## What the Leibniz rule extracts from the free vanishings

`⁅cᵢ, cⱼ⁆ = 0` holds for grading reasons; differentiating it with `D` produces genuine identities
one and two rungs up the imaginary ray, because `D³cᵢ = 0` truncates the expansion. -/

section Imaginary

variable {k : Type*} [Field k]

/-- **`⁅Dcᵢ, D²cⱼ⁆` is symmetric in `i` and `j`.** Apply `D³` to `⁅cᵢ, cⱼ⁆ = 0`: the two outer
terms die because the even `D`-strings have length three, leaving `3(⁅D²cᵢ, Dcⱼ⁆ + ⁅Dcᵢ, D²cⱼ⁆)
= 0`. -/
theorem lie_dY_one_dY_two_evenTower_comm (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (i j : ℕ) :
    ⁅dY k 1 (evenTower k i), dY k 2 (evenTower k j)⁆
      = ⁅dY k 1 (evenTower k j), dY k 2 (evenTower k i)⁆ := by
  have h := dY_three_lie k (evenTower k i) (evenTower k j)
  rw [lie_evenTower_evenTower h2 h3 h5 i j, dY_zero_elt,
    (evenLayer_evenTower h2 h3 h5 i).dY_top, (evenLayer_evenTower h2 h3 h5 j).dY_top] at h
  simp only [zero_lie, _root_.lie_zero, zero_add, add_zero] at h
  have hskew : ⁅dY k 2 (evenTower k i), dY k 1 (evenTower k j)⁆
      = -⁅dY k 1 (evenTower k j), dY k 2 (evenTower k i)⁆ := by
    rw [← lie_skew]
  rw [hskew] at h
  have h3' : (3 : k) • (⁅dY k 1 (evenTower k i), dY k 2 (evenTower k j)⁆
      - ⁅dY k 1 (evenTower k j), dY k 2 (evenTower k i)⁆) = 0 := by
    linear_combination (norm := module) -h
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3').resolve_left h3)

/-- **The imaginary bracket is the antisymmetric part of the pairing `(i, j) ↦ ⁅cᵢ, D²cⱼ⁆`.**
Apply `D²` to `⁅cᵢ, cⱼ⁆ = 0`. -/
theorem two_smul_lie_dY_one_evenTower (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (i j : ℕ) :
    (2 : k) • ⁅dY k 1 (evenTower k i), dY k 1 (evenTower k j)⁆
      = ⁅evenTower k j, dY k 2 (evenTower k i)⁆ - ⁅evenTower k i, dY k 2 (evenTower k j)⁆ := by
  have h := dY_two_lie k (evenTower k i) (evenTower k j)
  rw [lie_evenTower_evenTower h2 h3 h5 i j, dY_zero_elt] at h
  have hskew : ⁅dY k 2 (evenTower k i), evenTower k j⁆
      = -⁅evenTower k j, dY k 2 (evenTower k i)⁆ := by
    rw [← lie_skew]
  rw [hskew] at h
  linear_combination (norm := module) -h

/-- **The defect is the bracket of two consecutive imaginary vectors**, `topDefect k (m+1) =
⁅Dc₀, Dc_m⁆`. This is `EvenLayer.defect_eq` with `⁅a₁, a₃⁆` rewritten as `Dc₀`. -/
theorem topDefect_succ_eq_lie (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    topDefect k (m + 1) = ⁅dY k 1 (evenTower k 0), dY k 1 (evenTower k m)⁆ := by
  rw [topDefect_succ, (evenLayer_evenTower h2 h3 h5 m).defect_eq h2 h3, dY_one_evenTower_zero]

/-- **A closed form for the layer defect**: `2 · topDefect k (m+1) = ⁅c_m, D²c₀⁆ - ⁅c₀, D²c_m⁆`.
The defect is precisely the failure of the pairing `(i, j) ↦ ⁅cᵢ, D²cⱼ⁆` to be symmetric at
`(0, m)`. -/
theorem two_smul_topDefect_succ (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    (2 : k) • topDefect k (m + 1)
      = ⁅evenTower k m, dY k 2 (evenTower k 0)⁆ - ⁅evenTower k 0, dY k 2 (evenTower k m)⁆ := by
  rw [topDefect_succ_eq_lie h2 h3 h5 m, two_smul_lie_dY_one_evenTower h2 h3 h5 0 m]

/-- **The next imaginary vector is the symmetric part of the same pairing.** Differentiating the
tower recursion `c_{m+1} = 2⁅c₀, Dc_m⁆` once gives `Dc_{m+1} = 2 topDefect(m+1) + 2⁅c₀, D²c_m⁆`;
substituting the closed form of the defect turns it into
`Dc_{m+1} = ⁅c_m, D²c₀⁆ + ⁅c₀, D²c_m⁆`. -/
theorem dY_one_evenTower_succ (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    dY k 1 (evenTower k (m + 1))
      = (2 : k) • topDefect k (m + 1) + (2 : k) • ⁅evenTower k 0, dY k 2 (evenTower k m)⁆ := by
  have e := congrArg (dY k 1) (two_smul_lie_evenTower_zero_dY_one h2 h3 h5 m)
  rw [dY_smul_elt, dY_one_lie, dY_one_dY] at e
  rw [← e, topDefect_succ_eq_lie h2 h3 h5 m]
  module

/-- `Dc_{m+1} = ⁅c_m, D²c₀⁆ + ⁅c₀, D²c_m⁆`. -/
theorem dY_one_evenTower_succ_eq (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) :
    dY k 1 (evenTower k (m + 1))
      = ⁅evenTower k m, dY k 2 (evenTower k 0)⁆ + ⁅evenTower k 0, dY k 2 (evenTower k m)⁆ := by
  have h := dY_one_evenTower_succ h2 h3 h5 m
  have hd := two_smul_topDefect_succ h2 h3 h5 m
  rw [h]
  linear_combination (norm := module) hd

/-- **The remaining gap in Problem 2.16.3(b), as the symmetry of a single pairing.**

`topDefect k (m+1)` vanishes exactly when `⁅c_m, D²c₀⁆ = ⁅c₀, D²c_m⁆`. Both sides lie in the
imaginary component of bidegree `(2m+4, 4m+8)`; their sum is `Dc_{m+1}`
(`dY_one_evenTower_succ_eq`) and their difference is twice the defect
(`two_smul_topDefect_succ`). Compare `lie_dY_one_dY_two_evenTower_comm`, where the same pairing
one rung higher up the `D`-string *is* forced to be symmetric. -/
theorem topDefect_eq_zero_iff_lie_dY_two_comm (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (m : ℕ) :
    topDefect k (m + 1) = 0 ↔
      ⁅evenTower k m, dY k 2 (evenTower k 0)⁆ = ⁅evenTower k 0, dY k 2 (evenTower k m)⁆ := by
  rw [← sub_eq_zero (a := ⁅evenTower k m, dY k 2 (evenTower k 0)⁆),
    ← two_smul_topDefect_succ h2 h3 h5 m, smul_eq_zero]
  simp [h2]

end Imaginary

end Etingof.Problem2_16_3

import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Grading
import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Layers

/-!
# Bidegrees of the Chapter 2 vocabulary for `𝔤₄`

`EtingofRepresentationTheory/Chapter2/Problem2_16_3_Grading.lean` puts the `ℕ²`-bidegree
grading `gDeg` on `𝔤ₙ`. This file records the bidegree of every element the layer analysis
of `𝔤₄` in `EtingofRepresentationTheory/Chapter2/Problem2_16_3_Layers.lean` manipulates:

* `dY k j` = `ad(ȳ)ʲ` raises the `y`-degree by `j` (`dY_mem_gDeg`);
* `oddTop` raises the bidegree by `(1, 1)` and `evenTop` by `(1, 3)`
  (`oddTop_mem_gDeg`, `evenTop_mem_gDeg`), since `a₁` and `a₃` have those bidegrees;
* consequently the tower of even layers sits in the imaginary-root bidegrees:
  `evenTower k m ∈ gDeg k 4 (2 * m + 2, 4 * m + 3)` (`evenTower_mem_gDeg`).

The last one is the point: `evenTower k m` has bidegree `(m + 1) • (2, 4) + (0, -1)`, so the
whole tower lives on the single ray of imaginary roots of `A₂⁽²⁾` that the layer induction
walks up.
-/

namespace Etingof.Problem2_16_3

variable (k : Type*) [CommRing k]

/-- `ad(ȳ)` raises the `y`-degree by one. -/
theorem dY_one_mem_gDeg {a b : ℕ} {u : g k 4} (hu : u ∈ gDeg k 4 (a, b)) :
    dY k 1 u ∈ gDeg k 4 (a, b + 1) := by
  rw [dY_one]
  have := lie_mem_gDeg k (yb_mem_gDeg k 4) hu
  rwa [show ((0, 1) + (a, b) : ℕ × ℕ) = (a, b + 1) by simp [Nat.add_comm]] at this

/-- The iterated form: `ad(ȳ)ʲ` raises the `y`-degree by `j`. -/
theorem dY_mem_gDeg {a b : ℕ} (j : ℕ) {u : g k 4} (hu : u ∈ gDeg k 4 (a, b)) :
    dY k j u ∈ gDeg k 4 (a, b + j) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      rw [dY_succ, ← Nat.add_assoc]
      have := dY_one_mem_gDeg k ih
      rwa [dY_one] at this

/-- `oddTop c = -⁅a₁, c⁆` raises the bidegree by `(1, 1)`. -/
theorem oddTop_mem_gDeg {a b : ℕ} {c : g k 4} (hc : c ∈ gDeg k 4 (a, b)) :
    oddTop c ∈ gDeg k 4 (a + 1, b + 1) := by
  rw [oddTop]
  refine neg_mem ?_
  have := lie_mem_gDeg k (aElt_mem_gDeg k 4 1) hc
  rwa [show ((1, 1) + (a, b) : ℕ × ℕ) = (a + 1, b + 1) by
    simp [Nat.add_comm]] at this

/-- `evenTop b = ⁅a₃, b⁆` raises the bidegree by `(1, 3)`. -/
theorem evenTop_mem_gDeg {a b : ℕ} {c : g k 4} (hc : c ∈ gDeg k 4 (a, b)) :
    evenTop c ∈ gDeg k 4 (a + 1, b + 3) := by
  rw [evenTop]
  have := lie_mem_gDeg k (aElt_mem_gDeg k 4 3) hc
  rwa [show ((1, 3) + (a, b) : ℕ × ℕ) = (a + 1, b + 3) by
    simp [Nat.add_comm]] at this

/-- **The tower of even layers lives on the imaginary-root ray.** `evenTower k m` — the top of
the even layer of `t`-degree `2m + 2` — has bidegree `(2m + 2, 4m + 3)`. -/
theorem evenTower_mem_gDeg (m : ℕ) : evenTower k m ∈ gDeg k 4 (2 * m + 2, 4 * m + 3) := by
  induction m with
  | zero =>
      rw [evenTower_zero]
      refine neg_mem ?_
      have := lie_mem_gDeg k (aElt_mem_gDeg k 4 0) (aElt_mem_gDeg k 4 3)
      rwa [show ((1, 0) + (1, 3) : ℕ × ℕ) = (2 * 0 + 2, 4 * 0 + 3) by norm_num] at this
  | succ m ih =>
      rw [evenTower_succ]
      have h := evenTop_mem_gDeg k (oddTop_mem_gDeg k ih)
      rwa [show (2 * m + 2 + 1 + 1, 4 * m + 3 + 1 + 3) = (2 * (m + 1) + 2, 4 * (m + 1) + 3) by
        simp [Prod.ext_iff]; omega] at h

end Etingof.Problem2_16_3

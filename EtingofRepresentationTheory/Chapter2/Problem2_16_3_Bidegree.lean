import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Grading
import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Tower


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

The second half of the file cashes the grading in. `span_loopSet_eq_top` spans `𝔤₄`
unconditionally by `loopFam₄` together with the layer defects; every member of that spanning set
is bihomogeneous, and the bidegree assignment on `LoopIdx` is injective
(`LoopIdx.bideg_injective`). Projecting the spanning statement onto a single bidegree therefore
gives:

* `gDeg_eq_bot` — `𝔤₄` vanishes in every bidegree the spanning set misses;
* `gDeg_le_span_singleton` — `𝔤₄` is at most **one**-dimensional off the imaginary ray;
* `gDeg_imaginary_le` — on the imaginary ray `(2m+2, 4m+4)` the unconditional bound is **two**,
  `span {D (evenTower k m), topDefect k m}`, because the defect collides there with
  `loopFam₄ (.even m 1)`.

That single collision is the whole remaining gap in Problem 2.16.3(b):
`topDefect_eq_zero_of_gDeg_le` and `gDeg_le_span_singleton_of_topDefect_eq_zero` show that
sharpening the imaginary bound from two generators to one is *equivalent* to the vanishing of
the layer defect, i.e. to the Gabber–Kac statement `mult((m+1)δ) = 1` for `A₂⁽²⁾`.
-/

namespace Etingof.Problem2_16_3

section Degrees

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

/-- **The tower of odd tops.** `topOdd k m` — the top of the odd layer of `t`-degree `2m + 1` —
has bidegree `(2m + 1, 4m)`. -/
theorem topOdd_mem_gDeg (m : ℕ) : topOdd k m ∈ gDeg k 4 (2 * m + 1, 4 * m) := by
  cases m with
  | zero =>
      rw [topOdd_zero]
      simpa using xb_mem_gDeg k 4
  | succ m =>
      rw [topOdd_succ]
      have h := oddTop_mem_gDeg k (evenTower_mem_gDeg k m)
      rwa [show (2 * m + 2 + 1, 4 * m + 3 + 1) = (2 * (m + 1) + 1, 4 * (m + 1)) by
        simp [Prod.ext_iff]; omega] at h

/-! ## The bidegrees of the spanning set

`span_loopSet_eq_top` spans `𝔤₄` by the `LoopIdx`-indexed family `loopFam₄` together with the
layer defects `topDefect`. Every member of that set is bihomogeneous, and the assignment of
bidegrees is *injective* on `LoopIdx` — the only collision in the whole spanning set is between
`topDefect m` and `loopFam₄ (.even m 1) = D (evenTower m)`, both of bidegree `(2m+2, 4m+4)`.
That single collision is exactly the remaining gap in Problem 2.16.3(b). -/

/-- The bidegree of the spanning-family member at a given `LoopIdx`. -/
def LoopIdx.bideg : LoopIdx → ℕ × ℕ
  | .base => (0, 1)
  | .odd m i => (2 * m + 1, 4 * m + i)
  | .even m i => (2 * m + 2, 4 * m + 3 + i)

/-- The bidegree formula for `bideg_base`. -/
@[simp] theorem bideg_base : LoopIdx.base.bideg = (0, 1) := rfl

/-- The bidegree formula for `bideg_odd`. -/
@[simp] theorem bideg_odd (m : ℕ) (i : Fin 5) :
    (LoopIdx.odd m i).bideg = (2 * m + 1, 4 * m + i) := rfl

/-- The bidegree formula for `bideg_even`. -/
@[simp] theorem bideg_even (m : ℕ) (i : Fin 3) :
    (LoopIdx.even m i).bideg = (2 * m + 2, 4 * m + 3 + i) := rfl

/-- The bidegree of the one index that collides with a defect. -/
theorem bideg_even_one (m : ℕ) :
    (LoopIdx.even m (1 : Fin 3)).bideg = (2 * m + 2, 4 * m + 4) := by
  have h : ((1 : Fin 3) : ℕ) = 1 := rfl
  rw [bideg_even, h, Prod.mk.injEq]
  omega

/-- **Distinct indices of the spanning family have distinct bidegrees.** The `t`-parity separates
the odd strings from the even ones, the first coordinate recovers the string, and the second
recovers the position along it. -/
theorem LoopIdx.bideg_injective : Function.Injective LoopIdx.bideg := by
  rintro (_ | ⟨m, i⟩ | ⟨m, i⟩) (_ | ⟨m', i'⟩ | ⟨m', i'⟩) h <;>
    simp only [bideg_base, bideg_odd, bideg_even, Prod.mk.injEq] at h
  · rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · obtain rfl : m = m' := by omega
    obtain rfl : i = i' := Fin.ext (by omega)
    rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · obtain rfl : m = m' := by omega
    obtain rfl : i = i' := Fin.ext (by omega)
    rfl

/-- Every member of the `LoopIdx`-indexed family is bihomogeneous, of the recorded bidegree. -/
theorem loopFam₄_mem_gDeg (I : LoopIdx) : loopFam₄ k I ∈ gDeg k 4 I.bideg := by
  cases I with
  | base => simpa using yb_mem_gDeg k 4
  | odd m i =>
      rw [loopFam₄_odd, bideg_odd]
      exact dY_mem_gDeg k (i : ℕ) (topOdd_mem_gDeg k m)
  | even m i =>
      rw [loopFam₄_even, bideg_even]
      exact dY_mem_gDeg k (i : ℕ) (evenTower_mem_gDeg k m)

/-- **The defect is bihomogeneous of imaginary bidegree.** `topDefect k m` sits in bidegree
`(2m+2, 4m+4) = (m+1) • (2, 4) + (0, 0)`, the same bidegree as `D (evenTower k m)`. -/
theorem topDefect_mem_gDeg (m : ℕ) : topDefect k m ∈ gDeg k 4 (2 * m + 2, 4 * m + 4) := by
  rw [topDefect]
  refine sub_mem ?_ (Submodule.smul_mem _ _ ?_)
  · have h := lie_mem_gDeg k (aElt_mem_gDeg k 4 4) (topOdd_mem_gDeg k m)
    rwa [show ((1, 4) + (2 * m + 1, 4 * m) : ℕ × ℕ) = (2 * m + 2, 4 * m + 4) by
      simp [Prod.ext_iff]; omega] at h
  · have h := dY_mem_gDeg k 1 (evenTower_mem_gDeg k m)
    rwa [show (2 * m + 2, 4 * m + 3 + 1) = (2 * m + 2, 4 * m + 4) by simp] at h

end Degrees

/-! ## Bidegree-wise upper bounds on `𝔤₄`

Projecting the unconditional spanning theorem `span_loopSet_eq_top` onto a single bidegree turns
it into an upper bound on that component: since every member of the spanning set is
bihomogeneous, only the members of bidegree `p` survive the projection `gProj p`.

The count is then read off `LoopIdx.bideg_injective`: every bidegree carries **at most one**
member of `loopFam₄`, and the defects contribute one extra generator on the imaginary ray. So
`𝔤₄` is one-dimensional in every bidegree it occupies, except possibly in the bidegrees
`(2m+2, 4m+4)`, where the recorded upper bound is two.

Closing Problem 2.16.3(b) is exactly the statement that the upper bound `2` on the imaginary ray
is really `1` — this is `topDefect_eq_zero_of_gDeg_le` below, whose converse
`gDeg_le_span_singleton_of_topDefect_eq_zero` shows nothing weaker will do. -/

section Imaginary

variable {k : Type*} [Field k]

/-- **Bidegree-wise upper bound from the global spanning theorem.** To bound `gDeg k 4 p` by the
span of a set `T` it suffices to place in `T` the members of the spanning set that actually have
bidegree `p`. -/
theorem gDeg_le_span (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (p : ℕ × ℕ)
    (T : Set (g k 4)) (hfam : ∀ I : LoopIdx, I.bideg = p → loopFam₄ k I ∈ Submodule.span k T)
    (hdef : ∀ m : ℕ, (2 * m + 2, 4 * m + 4) = p → topDefect k m ∈ Submodule.span k T) :
    gDeg k 4 p ≤ Submodule.span k T := by
  rw [gDeg_eq_span_image k p (span_loopSet_eq_top h2 h3 h5), Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  rcases mem_loopSet hv with ⟨I, rfl⟩ | ⟨m, rfl⟩
  · by_cases hI : I.bideg = p
    · rw [gProj_self_of_mem k (hI ▸ loopFam₄_mem_gDeg k I)]
      exact hfam I hI
    · rw [gProj_eq_zero_of_mem k (loopFam₄_mem_gDeg k I) hI]
      exact Submodule.zero_mem _
  · by_cases hm : (2 * m + 2, 4 * m + 4) = p
    · rw [gProj_self_of_mem k (hm ▸ topDefect_mem_gDeg k m)]
      exact hdef m hm
    · rw [gProj_eq_zero_of_mem k (topDefect_mem_gDeg k m) hm]
      exact Submodule.zero_mem _

/-- **`𝔤₄` vanishes in every bidegree the spanning set misses.** -/
theorem gDeg_eq_bot (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (p : ℕ × ℕ)
    (hI : ∀ I : LoopIdx, I.bideg ≠ p) (hm : ∀ m : ℕ, (2 * m + 2, 4 * m + 4) ≠ p) :
    gDeg k 4 p = ⊥ := by
  refine le_antisymm ?_ bot_le
  have h := gDeg_le_span h2 h3 h5 p (∅ : Set (g k 4)) (fun I hIp => absurd hIp (hI I))
    (fun m hmp => absurd hmp (hm m))
  simpa using h

/-- **`𝔤₄` is at most one-dimensional off the imaginary ray.** -/
theorem gDeg_le_span_singleton (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (I : LoopIdx) (hI : ∀ m : ℕ, (2 * m + 2, 4 * m + 4) ≠ I.bideg) :
    gDeg k 4 I.bideg ≤ Submodule.span k {loopFam₄ k I} := by
  refine gDeg_le_span h2 h3 h5 _ _ (fun J hJ => ?_) (fun m hm => absurd hm (hI m))
  rw [LoopIdx.bideg_injective hJ]
  exact Submodule.mem_span_singleton_self _

/-- **`𝔤₄` is at most two-dimensional on the imaginary ray**, spanned by `D (evenTower m)` and
the defect. This is the unconditional half of Problem 2.16.3(b). -/
theorem gDeg_imaginary_le (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    gDeg k 4 (2 * m + 2, 4 * m + 4)
      ≤ Submodule.span k {dY k 1 (evenTower k m), topDefect k m} := by
  refine gDeg_le_span h2 h3 h5 _ _ (fun J hJ => ?_) (fun m' hm' => ?_)
  · obtain rfl : J = LoopIdx.even m 1 :=
      LoopIdx.bideg_injective (by rw [hJ, bideg_even_one])
    rw [loopFam₄_even]
    exact Submodule.subset_span (by simp)
  · rw [Prod.mk.injEq] at hm'
    obtain rfl : m' = m := by omega
    exact Submodule.subset_span (by simp)

/-- The defect vanishing is *equivalent* to the imaginary component being one-dimensional: this
is the easy direction. -/
theorem gDeg_le_span_singleton_of_topDefect_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (m : ℕ) (h : topDefect k m = 0) :
    gDeg k 4 (2 * m + 2, 4 * m + 4) ≤ Submodule.span k {dY k 1 (evenTower k m)} := by
  refine gDeg_le_span h2 h3 h5 _ _ (fun J hJ => ?_) (fun m' hm' => ?_)
  · obtain rfl : J = LoopIdx.even m 1 :=
      LoopIdx.bideg_injective (by rw [hJ, bideg_even_one])
    rw [loopFam₄_even]
    exact Submodule.mem_span_singleton_self _
  · rw [Prod.mk.injEq] at hm'
    obtain rfl : m' = m := by omega
    rw [h]
    exact Submodule.zero_mem _

/-- **The remaining gap in Problem 2.16.3(b), as a bidegree-wise dimension bound.**

If the imaginary bidegree component `(2m+2, 4m+4)` of `𝔤₄` is spanned by `D (evenTower k m)`
alone, then the layer defect at `m` vanishes: the defect lies in that component, so it is a
multiple `λ • D (evenTower k m)`; bracketing with `x̄` sends the defect to `0` (it is central)
and `D (evenTower k m)` to the next odd top, which is nonzero by `topOdd_ne_zero`, so `λ = 0`.

Together with `gDeg_le_span_singleton_of_topDefect_eq_zero` this identifies the Gabber–Kac
statement for `A₂⁽²⁾` with the sharpening of the unconditional bound `gDeg_imaginary_le` from
two generators to one. -/
theorem topDefect_eq_zero_of_gDeg_le (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) (hdim : gDeg k 4 (2 * m + 2, 4 * m + 4) ≤ Submodule.span k {dY k 1 (evenTower k m)}) :
    topDefect k m = 0 := by
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.1 (hdim (topDefect_mem_gDeg k m))
  have h0 : ⁅aElt k 4 0, topDefect k m⁆ = 0 := central_topDefect h2 h3 h5 m _
  rw [← hlam, lie_smul, lie_zero_dY_one_evenTower h2 h3 h5 m] at h0
  rcases smul_eq_zero.1 h0 with hz | hz
  · rw [← hlam, hz, zero_smul]
  · exact absurd hz (topOdd_ne_zero h2 h3 (m + 1))

end Imaginary

end Etingof.Problem2_16_3

-- The source-numbered exercise namespace and established API contain intentional underscores.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_16_3.LoopIdx.bideg

import EtingofRepresentationTheory.Chapter2.Problem2_15_1_l

/-!
# The nullity sequence of a block-diagonal sum of Jordan shifts (Problem 2.15.1(l), uniqueness)

The *uniqueness* half of Etingof Problem 2.15.1(l) recovers the `sl(2)`-isomorphism
type of a finite-dimensional module from its raising operator `E = ρ(e)`. The key
numerical invariant is the **nullity sequence** `k ↦ dim ker (Eᵏ)`.

This file supplies the two mechanical, self-contained pieces of that program that do
not require the structure theory of `sl(2)`-modules:

* **Block-sum nullity** (`piMap_pow_ker_finrank`): for a finite family of endomorphisms
  `f i` on finite-dimensional spaces `W i`, the nullity of a power of the block-diagonal
  operator `LinearMap.piMap f` splits as a sum over the factors,
  `dim ker ((piMap f)ᵏ) = ∑ i, dim ker (f iᵏ)`. Specialised to the standard Jordan
  shifts (`piShift_pow_ker_finrank`, using `jordanShift_pow_ker_finrank`), the nullity
  sequence of `⨁ᵢ J_{0,nᵢ}` is `k ↦ ∑ i, min k (n i)`.

* **Multiset inversion** (`nullitySeq_injective`): the map sending a multiset `s` of
  positive integers to its nullity function `k ↦ ∑_{a ∈ s} min k a` is injective. The
  first difference `d(k) = null(k) − null(k−1) = #{a ∈ s : a ≥ k}` recovers, for every
  `k`, the number of blocks of size `≥ k`, hence the multiset of block sizes.

Together these show that the nullity sequence is a *complete* invariant of the multiset
of Jordan block sizes: two block-diagonal sums of standard shifts with equal nullity
sequences have the same multiset of block sizes. This is the arithmetic heart of the
uniqueness statement `sl2Rep_iso_of_e_jordanType_eq`; the remaining structural pieces
(realising an arbitrary module as such a block sum via complete reducibility, and the
final reindexing) are tracked as follow-up work.
-/

open Etingof Etingof.Sl2Irrep

namespace Etingof.Sl2Irrep

/-! ## Block-sum nullity -/

section PiMap

variable {ι : Type*} {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- `piMap` turns composition of endomorphisms into componentwise composition:
`piMap f ∘ piMap g = piMap (fun i => f i ∘ g i)`. -/
theorem piMap_mul (f g : ∀ i, Module.End ℂ (W i)) :
    LinearMap.piMap f * LinearMap.piMap g
      = LinearMap.piMap (fun i => f i * g i) := by
  apply LinearMap.ext; intro v; funext j
  simp only [Module.End.mul_apply, LinearMap.coe_piMap, Pi.map_apply]

/-- A power of a block-diagonal operator is the block-diagonal operator of the powers. -/
theorem piMap_pow (f : ∀ i, Module.End ℂ (W i)) (k : ℕ) :
    LinearMap.piMap f ^ k = LinearMap.piMap (fun i => f i ^ k) := by
  induction k with
  | zero =>
    apply LinearMap.ext; intro v; funext j
    simp only [pow_zero, Module.End.one_apply, LinearMap.coe_piMap, Pi.map_apply]
  | succ k ih =>
    rw [pow_succ, ih, piMap_mul]
    simp only [pow_succ]

/-- The kernel of a block-diagonal operator is the product of the componentwise kernels. -/
noncomputable def kerPiMapEquiv (g : ∀ i, Module.End ℂ (W i)) :
    ↥(LinearMap.ker (LinearMap.piMap g)) ≃ₗ[ℂ] (∀ i, ↥(LinearMap.ker (g i))) where
  toFun v i := ⟨v.1 i, by
    have hv := v.2
    rw [LinearMap.mem_ker] at hv
    rw [LinearMap.mem_ker]
    have := congrFun hv i
    rwa [LinearMap.coe_piMap, Pi.map_apply, Pi.zero_apply] at this⟩
  map_add' u v := rfl
  map_smul' c v := rfl
  invFun w := ⟨fun i => (w i).1, by
    rw [LinearMap.mem_ker]
    funext i
    rw [LinearMap.coe_piMap, Pi.map_apply, Pi.zero_apply]
    exact (w i).2⟩
  left_inv v := rfl
  right_inv w := rfl

/-- **Block-sum nullity.** For a finite family of endomorphisms on finite-dimensional
spaces, the nullity of the block-diagonal operator splits as the sum of the componentwise
nullities: `dim ker (piMap g) = ∑ i, dim ker (g i)`. -/
theorem piMap_ker_finrank [Fintype ι] [∀ i, FiniteDimensional ℂ (W i)]
    (g : ∀ i, Module.End ℂ (W i)) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.piMap g))
      = ∑ i, Module.finrank ℂ (LinearMap.ker (g i)) := by
  rw [(kerPiMapEquiv g).finrank_eq, Module.finrank_pi_fintype]

/-- **Block-sum nullity of a power.** The nullity of the `k`-th power of a block-diagonal
operator splits over the factors: `dim ker ((piMap f)ᵏ) = ∑ i, dim ker (f iᵏ)`. -/
theorem piMap_pow_ker_finrank [Fintype ι] [∀ i, FiniteDimensional ℂ (W i)]
    (f : ∀ i, Module.End ℂ (W i)) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.piMap f ^ k))
      = ∑ i, Module.finrank ℂ (LinearMap.ker (f i ^ k)) := by
  rw [piMap_pow, piMap_ker_finrank]

end PiMap

/-- **The nullity sequence of a block-diagonal sum of standard Jordan shifts.** For a
finite family of block sizes `n : ι → ℕ`, the block-diagonal operator
`⨁ᵢ J_{0,nᵢ} = piMap (fun i => jordanShift (n i))` has nullity sequence
`k ↦ ∑ i, min k (n i)`. This is the raising operator of the assembled representation
`sl2Pi (fun i => sl2RepOfBlock (n i))` (see `sl2Pi_e`, `sl2RepOfBlock_e`). -/
theorem piShift_pow_ker_finrank {ι : Type*} [Fintype ι] (n : ι → ℕ) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.piMap (fun i => jordanShift (n i)) ^ k))
      = ∑ i, min k (n i) := by
  rw [piMap_pow_ker_finrank]
  exact Finset.sum_congr rfl fun i _ => jordanShift_pow_ker_finrank (n i) k

/-! ## Multiset inversion

The nullity sequence `k ↦ ∑_{a ∈ s} min k a` of a multiset `s` of positive integers
determines `s`. The lever is the first difference: `null(k+1) − null(k)` equals the
number of parts of size `≥ k+1`, and that count function determines the multiset.
-/

namespace NullitySeq

/-- The number of parts of `s` of size `≥ k`. -/
def geCount (s : Multiset ℕ) (k : ℕ) : ℕ := (s.filter (fun a => k ≤ a)).card

/-- The nullity value `∑_{a ∈ s} min k a`. -/
def nullity (s : Multiset ℕ) (k : ℕ) : ℕ := (s.map (fun a => min k a)).sum

/-- Cons rule for the nullity value. -/
theorem nullity_cons (a : ℕ) (s : Multiset ℕ) (m : ℕ) :
    nullity (a ::ₘ s) m = min m a + nullity s m := by
  simp only [nullity, Multiset.map_cons, Multiset.sum_cons]

/-- Cons rule for the `geCount` function. -/
theorem geCount_cons (a : ℕ) (s : Multiset ℕ) (k : ℕ) :
    geCount (a ::ₘ s) k = (if k ≤ a then 1 else 0) + geCount s k := by
  simp only [geCount, Multiset.filter_cons, Multiset.card_add]
  congr 1
  by_cases h : k ≤ a <;> simp [h]

/-- **First difference of the nullity sequence.** Passing from `k` to `k+1` increases the
nullity by exactly the number of parts of size `≥ k+1`:
`null(k+1) = null(k) + geCount(k+1)`. -/
theorem nullity_succ (s : Multiset ℕ) (k : ℕ) :
    nullity s (k + 1) = nullity s k + geCount s (k + 1) := by
  induction s using Multiset.induction_on with
  | empty => simp [nullity, geCount]
  | cons a s ih =>
    rw [nullity_cons, nullity_cons, geCount_cons, ih]
    have hmin : min (k + 1) a = min k a + (if k + 1 ≤ a then 1 else 0) := by
      split <;> omega
    rw [hmin]; ring

/-- **Recovering the count from the `geCount` function.** The multiplicity of `v` in `s`
is the drop `geCount(v) − geCount(v+1)` (parts `≥ v` that are not `≥ v+1`):
`geCount(v) = count v s + geCount(v+1)`. -/
theorem geCount_eq_count_add (s : Multiset ℕ) (v : ℕ) :
    geCount s v = Multiset.count v s + geCount s (v + 1) := by
  induction s using Multiset.induction_on with
  | empty => simp [geCount]
  | cons a s ih =>
    rw [geCount_cons, geCount_cons, Multiset.count_cons, ih]
    have hsplit : (if v ≤ a then (1 : ℕ) else 0)
        = (if v = a then 1 else 0) + (if v + 1 ≤ a then 1 else 0) := by
      split_ifs <;> omega
    rw [hsplit]; ring

end NullitySeq

/-- **The nullity sequence is a complete invariant of the multiset of block sizes
(Problem 2.15.1(l), multiset inversion).** Two multisets of positive integers with the same
nullity sequence `k ↦ ∑_{a ∈ s} min k a` are equal. Equivalently, the multiset of Jordan
block sizes of a nilpotent operator is recovered from its nullity sequence. -/
theorem nullitySeq_injective {s t : Multiset ℕ} (hs : 0 ∉ s) (ht : 0 ∉ t)
    (h : ∀ k, NullitySeq.nullity s k = NullitySeq.nullity t k) : s = t := by
  -- The `geCount` functions agree from the first differences of the nullity sequences.
  have hge : ∀ j, NullitySeq.geCount s (j + 1) = NullitySeq.geCount t (j + 1) := by
    intro j
    have hs' := NullitySeq.nullity_succ s j
    have ht' := NullitySeq.nullity_succ t j
    rw [h j, h (j + 1)] at hs'
    rw [ht'] at hs'
    exact (Nat.add_left_cancel hs').symm
  -- Hence the multiplicity functions agree, so the multisets are equal.
  refine Multiset.ext.mpr fun v => ?_
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [Multiset.count_eq_zero.mpr hs, Multiset.count_eq_zero.mpr ht]
  · obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v ≠ 0)
    have e1 := NullitySeq.geCount_eq_count_add s (w + 1)
    have e2 := NullitySeq.geCount_eq_count_add t (w + 1)
    rw [hge w, hge (w + 1), e2] at e1
    exact (Nat.add_right_cancel e1).symm

end Etingof.Sl2Irrep

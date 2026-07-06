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

end Etingof.Sl2Irrep

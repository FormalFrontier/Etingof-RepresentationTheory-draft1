import EtingofRepresentationTheory.Chapter8.KoszulAugmentation
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The monomial/subset basis of the Koszul complex

`Chapter8/KoszulDifferential.lean` builds the Koszul complex `Cᵢ = SV ⊗ ⋀ⁱ V` of
Problem 8.2.10 and `Chapter8/KoszulAugmentation.lean` supplies its augmentation and the
freeness of its terms. What is still missing is exactness, and every known
characteristic-free proof of exactness is combinatorial: it needs the differential written
out on an explicit `k`-basis of `Cᵢ`.

This file supplies that. Fix a finite basis `b : Module.Basis κ k V` on a linearly ordered
index type `κ`. Then

* `SV` has the monomial `k`-basis `b.symmetricAlgebra`, indexed by `κ →₀ ℕ`;
* `⋀ⁱ V` has the `k`-basis `b.exteriorPower i`, indexed by the `i`-element subsets of `κ`;

so `Cᵢ = SV ⊗[k] ⋀ⁱ V` has the `k`-basis `Etingof.koszulKBasis b i`, indexed by pairs
`(α, s)` of a monomial exponent and an `i`-element subset. Writing `x^α ⊗ e_s` for that
basis vector, the main result `Etingof.koszulD_koszulKBasis` is the book's differential in
coordinates:

`d (x^α ⊗ e_s) = ∑_{a ∈ s} (-1)^(pos(a, s) + 1) x^(α + eₐ) ⊗ e_(s \ {a})`,

where `pos(a, s) = #{c ∈ s : c < a}` is the position of `a` in the increasing listing of
`s`. The sign is exactly the book's `(-1)ʲ` from
`ιᵤ(v₁ ∧ ⋯ ∧ vᵢ) = ∑ⱼ (-1)ʲ u(vⱼ) v₁ ∧ ⋯ v̂ⱼ ⋯ ∧ vᵢ`, since deleting `a` from `s` deletes
the entry in position `pos(a, s)`.

## Main definitions

* `Etingof.koszulKBasis b i` — the `k`-basis of `Cᵢ` indexed by `(κ →₀ ℕ) × i`-subsets of `κ`.

## Main results

* `Etingof.exteriorContraction_basis_of_notMem`, `Etingof.exteriorContraction_basis_of_mem` —
  the contraction `ι_{xₐ*}` on the wedge basis: it kills `e_s` when `a ∉ s` and sends it to
  `(-1)^(pos(a,s)+1) e_(s \ {a})` when `a ∈ s`.
* `Etingof.koszulD_koszulKBasis` — the differential in coordinates.
* `Etingof.koszulAug_koszulKBasis` — the augmentation in coordinates: `x^α ⊗ 1 ↦ [α = 0]`.
-/

universe u v w

open scoped TensorProduct

namespace Etingof

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

/-! ### The position of an element in a finset -/

section Position

variable {κ : Type w} [LinearOrder κ]

/-- The position of `a` in the increasing listing of `s`, namely the number of elements of `s`
strictly below `a`. This is the index `j` for which `s.orderEmbOfFin _ j = a`
(`Etingof.orderEmbOfFin_finsetPos`). -/
def finsetPos (s : Finset κ) (a : κ) : ℕ := (s.filter (· < a)).card

theorem finsetPos_lt_card {s : Finset κ} {a : κ} (ha : a ∈ s) : finsetPos s a < s.card := by
  classical
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
  exact absurd (Finset.mem_filter.mp (hsub ha)).2 (lt_irrefl a)

/-- `finsetPos s a` really is the index of `a` in the increasing listing of `s`. -/
theorem orderEmbOfFin_finsetPos {s : Finset κ} {n : ℕ} (h : s.card = n) {a : κ} (ha : a ∈ s) :
    s.orderEmbOfFin h ⟨finsetPos s a, h ▸ finsetPos_lt_card ha⟩ = a := by
  classical
  -- `a` is in the range of the increasing listing, say `a = orderEmbOfFin h j`.
  obtain ⟨j, rfl⟩ : a ∈ Set.range (s.orderEmbOfFin h) := by
    rw [Finset.range_orderEmbOfFin]; exact ha
  congr 1
  refine Fin.ext ?_
  -- The elements of `s` below `orderEmbOfFin h j` are exactly the `orderEmbOfFin h i` with `i < j`.
  change finsetPos s (s.orderEmbOfFin h j) = (j : ℕ)
  have himg : s.filter (· < s.orderEmbOfFin h j) =
      Finset.map (s.orderEmbOfFin h).toEmbedding (Finset.univ.filter (· < j)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hxs, hxlt⟩
      obtain ⟨i, rfl⟩ : x ∈ Set.range (s.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]; exact hxs
      exact ⟨i, by simpa using hxlt, rfl⟩
    · rintro ⟨i, hij, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, by simpa using hij⟩
  have hIio : Finset.univ.filter (· < j) = Finset.Iio j := by ext i; simp
  rw [finsetPos, himg, Finset.card_map, hIio, Fin.card_Iio]

end Position

/-! ### The contraction on the wedge basis -/

section Contraction

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- Deleting the `j₀`-th entry from the increasing listing of `s` gives the increasing listing
of `s.erase a`, where `a` is the `j₀`-th entry. -/
theorem orderEmbOfFin_erase {s : Finset κ} {n : ℕ} (h : s.card = n + 1) {a : κ} (ha : a ∈ s)
    (herase : (s.erase a).card = n) :
    (fun i => s.orderEmbOfFin h
        ((⟨finsetPos s a, h ▸ finsetPos_lt_card ha⟩ : Fin (n + 1)).succAbove i)) =
      (s.erase a).orderEmbOfFin herase := by
  set j₀ : Fin (n + 1) := ⟨finsetPos s a, h ▸ finsetPos_lt_card ha⟩ with hj₀
  have hemb : s.orderEmbOfFin h j₀ = a := orderEmbOfFin_finsetPos h ha
  refine Finset.orderEmbOfFin_unique _ (fun i => ?_) ?_
  · refine Finset.mem_erase.mpr ⟨?_, Finset.orderEmbOfFin_mem _ _ _⟩
    rw [← hemb]
    exact fun hcon => (Fin.succAbove_ne j₀ i) ((s.orderEmbOfFin h).injective hcon)
  · exact (s.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove j₀)

omit [DecidableEq κ] in
/-- The contraction `ι_{xₐ*}` kills the wedge basis vector `e_s` when `a ∉ s`. -/
theorem exteriorContraction_basis_of_notMem (b : Module.Basis κ k V) (a : κ) (n : ℕ)
    (s : Set.powersetCard κ (n + 1)) (ha : a ∉ (s : Finset κ)) :
    exteriorContraction k (b.coord a) n (b.exteriorPower (n + 1) s) = 0 := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorContraction_ιMulti]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : (b.coord a) (b (Set.powersetCard.ofFinEmbEquiv.symm s j)) = 0 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    rintro rfl
    exact ha (Finset.orderEmbOfFin_mem _ _ _)
  simp [Function.comp_apply, this]

/-- **The contraction on the wedge basis.** For `a ∈ s`,
`ι_{xₐ*} e_s = (-1)^(pos(a,s)+1) e_(s \ {a})`, where `pos(a, s) = #{c ∈ s : c < a}`. -/
theorem exteriorContraction_basis_of_mem (b : Module.Basis κ k V) (a : κ) (n : ℕ)
    (s : Set.powersetCard κ (n + 1)) (ha : a ∈ (s : Finset κ))
    (herase : ((s : Finset κ).erase a).card = n) :
    exteriorContraction k (b.coord a) n (b.exteriorPower (n + 1) s) =
      ((-1 : k) ^ (finsetPos (s : Finset κ) a + 1)) •
        b.exteriorPower n ⟨(s : Finset κ).erase a, Set.powersetCard.mem_iff.mpr herase⟩ := by
  have hcard : (s : Finset κ).card = n + 1 := s.2
  have hlt : finsetPos (s : Finset κ) a < n + 1 := by
    have := finsetPos_lt_card ha; omega
  set j₀ : Fin (n + 1) := ⟨finsetPos (s : Finset κ) a, hlt⟩ with hj₀
  have hemb : (s : Finset κ).orderEmbOfFin hcard j₀ = a := orderEmbOfFin_finsetPos hcard ha
  have hsymm : (Set.powersetCard.ofFinEmbEquiv.symm s : Fin (n + 1) → κ) =
      (s : Finset κ).orderEmbOfFin hcard := rfl
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorContraction_ιMulti]
  -- Only the term `j = j₀` survives.
  rw [Finset.sum_eq_single j₀]
  · rw [hsymm, Function.comp_apply, hemb, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, mul_one]
    congr 1
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    congr 1
    have := orderEmbOfFin_erase hcard ha herase
    funext i
    exact congrArg b (congrFun this i)
  · intro j _ hj
    have hz : (b.coord a) (b ((s : Finset κ).orderEmbOfFin hcard j)) = 0 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
      intro hcon
      exact hj ((((s : Finset κ).orderEmbOfFin hcard).injective (hemb.trans hcon.symm)).symm)
    simp [hsymm, Function.comp_apply, hz]
  · intro h; exact absurd (Finset.mem_univ _) h

end Contraction

/-! ### The monomial basis of `SV` -/

section Monomial

variable {κ : Type w}

theorem symmetricAlgebra_basis_apply (b : Module.Basis κ k V) (α : κ →₀ ℕ) :
    b.symmetricAlgebra α =
      (SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.monomial α 1) := by
  simp [Module.Basis.symmetricAlgebra]

/-- Multiplying a monomial basis vector of `SV` by the variable `xₐ` bumps the exponent. -/
theorem ι_mul_symmetricAlgebra_basis (b : Module.Basis κ k V) (a : κ) (α : κ →₀ ℕ) :
    SymmetricAlgebra.ι k V (b a) * b.symmetricAlgebra α =
      b.symmetricAlgebra (α + Finsupp.single a 1) := by
  have hι : SymmetricAlgebra.ι k V (b a) =
      (SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X a) := by
    simp
  rw [hι, symmetricAlgebra_basis_apply, symmetricAlgebra_basis_apply, ← map_mul]
  congr 1
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm]

end Monomial

/-! ### The `k`-basis of `Cᵢ` and the differential in coordinates -/

section KBasis

variable {κ : Type w} [LinearOrder κ]

variable (k V) in
/-- **The `k`-basis of `Cᵢ = SV ⊗ ⋀ⁱ V`** indexed by pairs `(α, s)` of a monomial exponent
`α : κ →₀ ℕ` and an `i`-element subset `s ⊆ κ`: the basis vector is `x^α ⊗ e_s`. -/
noncomputable def koszulKBasis (b : Module.Basis κ k V) (i : ℕ) :
    Module.Basis ((κ →₀ ℕ) × Set.powersetCard κ i) k (koszulX k V i) :=
  (b.symmetricAlgebra).tensorProduct (b.exteriorPower i)

@[simp]
theorem koszulKBasis_apply (b : Module.Basis κ k V) (i : ℕ)
    (p : (κ →₀ ℕ) × Set.powersetCard κ i) :
    koszulKBasis k V b i p = b.symmetricAlgebra p.1 ⊗ₜ[k] b.exteriorPower i p.2 :=
  Module.Basis.tensorProduct_apply _ _ _ _

variable [DecidableEq κ]

/-- `s` with one of its elements removed, as an `i`-element subset. -/
def eraseElem {i : ℕ} (s : Set.powersetCard κ (i + 1)) (a : (s : Finset κ)) :
    Set.powersetCard κ i :=
  ⟨(s : Finset κ).erase a, Set.powersetCard.mem_iff.mpr (by
    rw [Finset.card_erase_of_mem a.2, s.2]; rfl)⟩

omit [LinearOrder κ] in
@[simp]
theorem coe_eraseElem {i : ℕ} (s : Set.powersetCard κ (i + 1)) (a : (s : Finset κ)) :
    (eraseElem s a : Finset κ) = (s : Finset κ).erase a := rfl

variable [Fintype κ]

/-- **The Koszul differential in coordinates.** On the basis vector `x^α ⊗ e_s`,

`d (x^α ⊗ e_s) = ∑_{a ∈ s} (-1)^(pos(a, s) + 1) x^(α + eₐ) ⊗ e_(s \ {a})`,

where `pos(a, s) = #{c ∈ s : c < a}`. This is the book's alternating sum
`dᵢ(f)(u) = ιᵤ (f u)` written out on the monomial/subset basis; it is the starting point for
the combinatorial proof of exactness. -/
theorem koszulD_koszulKBasis (b : Module.Basis κ k V) (i : ℕ)
    (α : κ →₀ ℕ) (s : Set.powersetCard κ (i + 1)) :
    koszulD b i (koszulKBasis k V b (i + 1) (α, s)) =
      ∑ a ∈ (s : Finset κ).attach, ((-1 : k) ^ (finsetPos (s : Finset κ) a + 1)) •
        koszulKBasis k V b i (α + Finsupp.single (a : κ) 1, eraseElem s a) := by
  classical
  rw [koszulKBasis_apply, koszulD_tmul]
  -- Terms with `a ∉ s` vanish, so the sum over `κ` collapses to a sum over `s`.
  have hsub : ∑ a : κ, (SymmetricAlgebra.ι k V (b a) * b.symmetricAlgebra α) ⊗ₜ[k]
        exteriorContraction k (b.coord a) i (b.exteriorPower (i + 1) s)
      = ∑ a ∈ (s : Finset κ), (SymmetricAlgebra.ι k V (b a) * b.symmetricAlgebra α) ⊗ₜ[k]
        exteriorContraction k (b.coord a) i (b.exteriorPower (i + 1) s) :=
    (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => by
      rw [exteriorContraction_basis_of_notMem b a i s ha, TensorProduct.tmul_zero]).symm
  rw [hsub, ← Finset.sum_attach (s := (s : Finset κ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have herase : ((s : Finset κ).erase (a : κ)).card = i := by
    rw [Finset.card_erase_of_mem a.2, s.2]; rfl
  rw [exteriorContraction_basis_of_mem b (a : κ) i s a.2 herase,
    ι_mul_symmetricAlgebra_basis, TensorProduct.tmul_smul, koszulKBasis_apply]
  rfl

omit [Fintype κ] in
/-- The augmentation in coordinates: `ε (x^α ⊗ 1) = 1` if `α = 0` and `0` otherwise. -/
theorem koszulAug_koszulKBasis (b : Module.Basis κ k V) (α : κ →₀ ℕ)
    (s : Set.powersetCard κ 0) :
    KoszulAugModule.equiv k V (koszulAug k V (koszulKBasis k V b 0 (α, s))) =
      if α = 0 then 1 else 0 := by
  classical
  rw [koszulKBasis_apply, koszulAug_tmul, symmetricAlgebra_basis_apply]
  have hε : SymmetricAlgebra.algebraMapInv
      ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.monomial α 1)) =
      if α = 0 then 1 else 0 := by
    have : SymmetricAlgebra.algebraMapInv (R := k) (M := V) =
        (MvPolynomial.aeval (fun _ : κ => (0 : k))).comp
          (SymmetricAlgebra.equivMvPolynomial b).toAlgHom := by
      apply SymmetricAlgebra.algHom_ext
      apply b.ext
      intro j
      simp [SymmetricAlgebra.algebraMapInv_ι]
    rw [this]
    change MvPolynomial.aeval (fun _ : κ => (0 : k))
        ((SymmetricAlgebra.equivMvPolynomial b)
          ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.monomial α 1))) =
        if α = 0 then 1 else 0
    rw [AlgEquiv.apply_symm_apply, MvPolynomial.aeval_monomial, map_one, one_mul]
    by_cases hα : α = 0
    · simp [hα]
    · rw [if_neg hα]
      obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
        by_contra hcon
        exact hα (Finsupp.ext (by simpa using not_exists.mp hcon))
      refine Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr hj) ?_
      exact zero_pow hj
  rw [hε]
  by_cases hα : α = 0 <;>
    simp [hα, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.zeroEquiv_ιMulti]

end KBasis

end Etingof

import EtingofRepresentationTheory.Chapter8.KoszulBasis
import Mathlib.Data.Finsupp.Order

set_option backward.isDefEq.respectTransparency false

/-!
# The contracting homotopy of the augmented Koszul complex

`Chapter8/KoszulDifferential.lean` builds the Koszul complex `Cᵢ = SV ⊗ ⋀ⁱ V` of
Problem 8.2.10(i), `Chapter8/KoszulAugmentation.lean` adds the augmentation `ε : C₀ → k` and the
freeness of the terms, and `Chapter8/KoszulBasis.lean` writes the differential out on the
monomial/subset `k`-basis `x^α ⊗ e_s`. The one thing still missing for "free resolution of `k`"
is exactness. This file supplies the input that gives it: a **contracting homotopy** of the
augmented complex

`⋯ → C₂ → C₁ → C₀ --ε--> k → 0`.

The homotopy `h` is `k`-linear, not `SV`-linear — no `SV`-linear contracting homotopy can exist,
since the complex is a resolution of `k` and not split over `SV`. It is also characteristic-free,
unlike the Euler-operator homotopy `dκ + κd = (p + q) • id`, which needs `p + q` invertible.

## The homotopy

On the basis vector `x^α ⊗ e_s` set `p = min (supp α)` (when `α ≠ 0`). Then

* `h (x^α ⊗ e_s) = -(x^(α - eₚ) ⊗ e_(insert p s))` when `p` exists and `p < c` for every `c ∈ s`;
* `h (x^α ⊗ e_s) = 0` otherwise.

The condition "`p ∈ supp α`, `p` is `≤` everything in `supp α`, and `p <` everything in `s`" is
`Etingof.IsKoszulPivot`. At most one `a` can satisfy it (`Etingof.IsKoszulPivot.unique`), which is
what makes the defining sum in `Etingof.koszulHFun` a single term or zero.

## Main definitions

* `Etingof.IsKoszulPivot α s a` — the pivot condition on `(α, s)` witnessed by `a`.
* `Etingof.koszulH b i : koszulX k V i →ₗ[k] koszulX k V (i + 1)` — the homotopy.
* `Etingof.koszulEta : KoszulAugModule k V →ₗ[k] koszulX k V 0` — the `k`-linear splitting
  `1 ↦ 1 ⊗ 1` of the augmentation.

## Main results

* `Etingof.koszulAug_koszulEta` — `ε ∘ η = id`.
* `Etingof.koszulD_koszulH_add_koszulH_koszulD` — `d ∘ h + h ∘ d = id` on `C_{i+1}`.
* `Etingof.koszulD_koszulH_add_eta_aug` — `d ∘ h + η ∘ ε = id` on `C₀`.

The two homotopy identities are stated pointwise, with `LinearMap`-level restatements
`Etingof.koszulD_comp_koszulH_add_koszulH_comp_koszulD` and
`Etingof.koszulD_comp_koszulH_add_koszulEta_comp_koszulAug`.
-/

universe u v w

open scoped TensorProduct

namespace Etingof

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

/-! ### Finsupp arithmetic on exponents -/

section Exponent

variable {κ : Type w}

/-- Removing one copy of `xₐ` from a monomial and putting it back is the identity, provided the
monomial really contained `xₐ`. -/
theorem sub_single_add_single {α : κ →₀ ℕ} {a : κ} (h : 1 ≤ α a) :
    α - Finsupp.single a 1 + Finsupp.single a 1 = α := by
  ext x
  rcases eq_or_ne a x with rfl | hne
  · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  · have h0 : (Finsupp.single a (1 : ℕ)) x = 0 := Finsupp.single_eq_of_ne hne.symm
    simp only [Finsupp.add_apply, Finsupp.tsub_apply]
    omega

/-- Putting one copy of `xₐ` back after removing one copy of `x_p` is the same as doing it the
other way round, provided the monomial really contained `x_p`. -/
theorem sub_single_add_single_comm {α : κ →₀ ℕ} {p a : κ} (h : 1 ≤ α p) :
    α - Finsupp.single p 1 + Finsupp.single a 1 =
      α + Finsupp.single a 1 - Finsupp.single p 1 := by
  ext x
  rcases eq_or_ne p x with rfl | hne
  · rcases eq_or_ne a p with rfl | hne'
    · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · have h0 : (Finsupp.single a (1 : ℕ)) p = 0 := Finsupp.single_eq_of_ne hne'.symm
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
  · have h0 : (Finsupp.single p (1 : ℕ)) x = 0 := Finsupp.single_eq_of_ne hne.symm
    simp only [Finsupp.add_apply, Finsupp.tsub_apply]
    omega

/-- Adding one copy of `xₐ` and then removing it again is the identity. -/
theorem add_single_sub_single {α : κ →₀ ℕ} {a : κ} :
    α + Finsupp.single a 1 - Finsupp.single a 1 = α := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  omega

/-- The support of `α + eₐ` is `insert a (supp α)`. -/
theorem mem_support_add_single {α : κ →₀ ℕ} {a m : κ} :
    m ∈ (α + Finsupp.single a 1).support ↔ m = a ∨ m ∈ α.support := by
  rcases eq_or_ne m a with rfl | hne
  · simp [Finsupp.mem_support_iff, Finsupp.add_apply]
  · simp [Finsupp.mem_support_iff, Finsupp.add_apply, hne]

end Exponent

/-! ### Inserting an element into a subset of fixed size -/

section Insert

variable {κ : Type w} [DecidableEq κ]

/-- `insert a s` as an `(i + 1)`-element subset, for `a ∉ s`. The counterpart of
`Etingof.eraseElem`. -/
def insertElem {i : ℕ} (s : Set.powersetCard κ i) {a : κ} (ha : a ∉ (s : Finset κ)) :
    Set.powersetCard κ (i + 1) :=
  ⟨insert a (s : Finset κ), Set.powersetCard.mem_iff.mpr (by
    rw [Finset.card_insert_of_notMem ha, Set.powersetCard.card_eq])⟩

@[simp]
theorem coe_insertElem {i : ℕ} (s : Set.powersetCard κ i) {a : κ} (ha : a ∉ (s : Finset κ)) :
    (insertElem s ha : Finset κ) = insert a (s : Finset κ) := rfl

end Insert

/-! ### Positions after inserting a smallest element -/

section Position

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- Inserting `p` below every element of `s` puts `p` in position `0`. -/
theorem finsetPos_insert_self {s : Finset κ} {p : κ} (hp : ∀ c ∈ s, p < c) :
    finsetPos (insert p s) p = 0 := by
  rw [finsetPos, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact lt_irrefl _
  · exact not_lt.mpr (hp x hx).le

/-- Inserting `p` below every element of `s` shifts every other position up by one. -/
theorem finsetPos_insert_of_mem {s : Finset κ} {p c : κ} (hp : ∀ c' ∈ s, p < c') (hc : c ∈ s) :
    finsetPos (insert p s) c = finsetPos s c + 1 := by
  have hpn : p ∉ s := fun h => absurd (hp p h) (lt_irrefl p)
  have hfil : (insert p s).filter (· < c) = insert p (s.filter (· < c)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx | hx, hlt⟩
      · exact Or.inl hx
      · exact Or.inr ⟨hx, hlt⟩
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨Or.inl rfl, hp c hc⟩
      · exact ⟨Or.inr hx, hlt⟩
  rw [finsetPos, hfil, Finset.card_insert_of_notMem fun h => hpn (Finset.mem_filter.mp h).1,
    finsetPos]

omit [DecidableEq κ] in
/-- The least element of `s` sits in position `0`. -/
theorem finsetPos_min' {s : Finset κ} (h : s.Nonempty) : finsetPos s (s.min' h) = 0 := by
  rw [finsetPos, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun x hx => not_lt.mpr (s.min'_le x hx)

end Position

/-! ### The pivot condition -/

section Pivot

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- **The pivot condition.** `a` is a *pivot* of the pair `(α, s)` when `xₐ` divides the monomial
`x^α`, `a` is the smallest such variable, and `a` is strictly below every element of `s`.

This is exactly the condition under which the contracting homotopy `Etingof.koszulH` is nonzero on
`x^α ⊗ e_s`: it moves `xₐ` out of the monomial and into the wedge factor, where it must land in
position `0`. -/
def IsKoszulPivot (α : κ →₀ ℕ) (s : Finset κ) (a : κ) : Prop :=
  a ∈ α.support ∧ (∀ m ∈ α.support, a ≤ m) ∧ ∀ c ∈ s, a < c

instance (α : κ →₀ ℕ) (s : Finset κ) : DecidablePred (IsKoszulPivot α s) := fun a => by
  unfold IsKoszulPivot; infer_instance

omit [DecidableEq κ] in
theorem IsKoszulPivot.notMem {α : κ →₀ ℕ} {s : Finset κ} {a : κ} (h : IsKoszulPivot α s a) :
    a ∉ s := fun ha => absurd (h.2.2 a ha) (lt_irrefl a)

omit [DecidableEq κ] in
/-- **A pair has at most one pivot** — each of the two candidates is `≤` the other. This is what
collapses the defining sum of `Etingof.koszulHFun` to a single term. -/
theorem IsKoszulPivot.unique {α : κ →₀ ℕ} {s : Finset κ} {a a' : κ} (h : IsKoszulPivot α s a)
    (h' : IsKoszulPivot α s a') : a = a' :=
  le_antisymm (h.2.1 a' h'.1) (h'.2.1 a h.1)

omit [DecidableEq κ] in
theorem IsKoszulPivot.one_le {α : κ →₀ ℕ} {s : Finset κ} {a : κ} (h : IsKoszulPivot α s a) :
    1 ≤ α a :=
  Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h.1)

end Pivot

/-! ### The homotopy -/

section Homotopy

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- **The contracting homotopy on basis vectors.** On `x^α ⊗ e_s` it returns
`-(x^(α - eₐ) ⊗ e_(insert a s))` for the pivot `a` of `(α, s)`, and `0` when there is no pivot.
By `Etingof.IsKoszulPivot.unique` at most one summand is nonzero. -/
noncomputable def koszulHFun (b : Module.Basis κ k V) (i : ℕ)
    (P : (κ →₀ ℕ) × Set.powersetCard κ i) : koszulX k V (i + 1) :=
  ∑ a ∈ P.1.support,
    if h : IsKoszulPivot P.1 (P.2 : Finset κ) a then
      -koszulKBasis k V b (i + 1) (P.1 - Finsupp.single a 1, insertElem P.2 h.notMem)
    else 0

theorem koszulHFun_of_isKoszulPivot (b : Module.Basis κ k V) {i : ℕ} (α : κ →₀ ℕ)
    (s : Set.powersetCard κ i) {a : κ} (h : IsKoszulPivot α (s : Finset κ) a) :
    koszulHFun b i (α, s) =
      -koszulKBasis k V b (i + 1) (α - Finsupp.single a 1, insertElem s h.notMem) := by
  rw [koszulHFun,
    Finset.sum_eq_single_of_mem a h.1 fun c _ hc => dif_neg fun h' => hc (h'.unique h),
    dif_pos h]

theorem koszulHFun_of_forall_not (b : Module.Basis κ k V) {i : ℕ} (α : κ →₀ ℕ)
    (s : Set.powersetCard κ i) (h : ∀ a, ¬IsKoszulPivot α (s : Finset κ) a) :
    koszulHFun b i (α, s) = 0 :=
  Finset.sum_eq_zero fun a _ => dif_neg (h a)

/-- **The contracting homotopy** `h : Cᵢ → Cᵢ₊₁` of the augmented Koszul complex, the `k`-linear
extension of `Etingof.koszulHFun`. It is only `k`-linear: an `SV`-linear contracting homotopy
cannot exist, since `C_•` resolves `k` and is not `SV`-split. -/
noncomputable def koszulH (b : Module.Basis κ k V) (i : ℕ) :
    koszulX k V i →ₗ[k] koszulX k V (i + 1) :=
  (koszulKBasis k V b i).constr k (koszulHFun b i)

@[simp]
theorem koszulH_koszulKBasis (b : Module.Basis κ k V) (i : ℕ)
    (P : (κ →₀ ℕ) × Set.powersetCard κ i) :
    koszulH b i (koszulKBasis k V b i P) = koszulHFun b i P :=
  Module.Basis.constr_basis _ _ _ _

/-- The `k`- and `SV`-actions on the augmentation module are compatible: `SV` acts through the
counit `ε`, which is a `k`-algebra map. This is what lets `Etingof.koszulAug` be restricted to a
`k`-linear map, so that it can sit in a `k`-linear homotopy identity. -/
instance : IsScalarTower k (SymmetricAlgebra k V) (KoszulAugModule k V) where
  smul_assoc c s x := by
    apply (KoszulAugModule.equiv k V).injective
    have h1 : KoszulAugModule.equiv k V ((c • s) • x) =
        SymmetricAlgebra.algebraMapInv (c • s) * KoszulAugModule.equiv k V x :=
      KoszulAugModule.equiv_smul _ _
    have h2 : KoszulAugModule.equiv k V (c • (s • x)) =
        c • KoszulAugModule.equiv k V (s • x) := map_smul _ _ _
    rw [h1, h2, KoszulAugModule.equiv_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

variable (k V) in
/-- **The `k`-linear splitting of the augmentation**, `η : k → C₀`, `1 ↦ 1 ⊗ 1`. Like the
homotopy it is only `k`-linear. -/
noncomputable def koszulEta : KoszulAugModule k V →ₗ[k] koszulX k V 0 :=
  ((TensorProduct.mk k (SymmetricAlgebra k V) (⋀[k]^0 V)).flip
      ((exteriorPower.zeroEquiv k V).symm 1)).comp
    ((Algebra.linearMap k (SymmetricAlgebra k V)).comp
      (KoszulAugModule.equiv k V).toLinearMap)

theorem koszulEta_apply (c : KoszulAugModule k V) :
    koszulEta k V c =
      algebraMap k (SymmetricAlgebra k V) (KoszulAugModule.equiv k V c) ⊗ₜ[k]
        (exteriorPower.zeroEquiv k V).symm 1 :=
  rfl

/-- **`ε ∘ η = id`**: the splitting really splits the augmentation. -/
theorem koszulAug_koszulEta (c : KoszulAugModule k V) :
    koszulAug k V (koszulEta k V c) = c := by
  apply (KoszulAugModule.equiv k V).injective
  rw [koszulEta_apply, koszulAug_tmul]
  simp

/-! ### The differential as a sum over a plain finset

`Etingof.koszulD_koszulKBasis` sums over `s.attach`; for the homotopy computation it is more
convenient to sum over `s` itself, with the membership hypothesis absorbed into a `dite`. -/

/-- One term of the Koszul differential on `x^α ⊗ e_s`, as a function of a plain `a : κ`. -/
noncomputable def koszulDTerm (b : Module.Basis κ k V) (i : ℕ) (α : κ →₀ ℕ)
    (s : Set.powersetCard κ (i + 1)) (a : κ) : koszulX k V i :=
  if h : a ∈ (s : Finset κ) then
    ((-1 : k) ^ (finsetPos (s : Finset κ) a + 1)) •
      koszulKBasis k V b i (α + Finsupp.single a 1, eraseElem s ⟨a, h⟩)
  else 0

variable [Fintype κ]

theorem koszulD_koszulKBasis' (b : Module.Basis κ k V) (i : ℕ) (α : κ →₀ ℕ)
    (s : Set.powersetCard κ (i + 1)) :
    koszulD b i (koszulKBasis k V b (i + 1) (α, s)) =
      ∑ a ∈ (s : Finset κ), koszulDTerm b i α s a := by
  rw [koszulD_koszulKBasis, ← Finset.sum_attach (s := (s : Finset κ)) (koszulDTerm b i α s)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [koszulDTerm, dif_pos a.2]

/-! ### `d h + h d = id` in positive degrees -/

/-- The homotopy identity `d h + h d = id` on the basis vectors of `C_{i+1}`. -/
theorem koszulD_koszulH_add_koszulH_koszulD_koszulKBasis (b : Module.Basis κ k V) (i : ℕ)
    (α : κ →₀ ℕ) (s : Set.powersetCard κ (i + 1)) :
    koszulD b (i + 1) (koszulH b (i + 1) (koszulKBasis k V b (i + 1) (α, s))) +
        koszulH b i (koszulD b i (koszulKBasis k V b (i + 1) (α, s))) =
      koszulKBasis k V b (i + 1) (α, s) := by
  have hne : (s : Finset κ).Nonempty := by
    rw [← Finset.card_pos, Set.powersetCard.card_eq]; omega
  rw [koszulH_koszulKBasis, koszulD_koszulKBasis' b i α s, map_sum]
  by_cases hpiv : ∃ p, IsKoszulPivot α (s : Finset κ) p
  · -- **Case A.** A pivot `p` exists; `p` is below every element of `s`, so `h` is nonzero on
    -- `x^α ⊗ e_s` and the `a = p` term of `d h` reproduces `x^α ⊗ e_s` while the remaining
    -- terms cancel against `h d` one by one.
    obtain ⟨p, hp⟩ := hpiv
    rw [koszulHFun_of_isKoszulPivot b α s hp, map_neg,
      koszulD_koszulKBasis' b (i + 1) (α - Finsupp.single p 1) (insertElem s hp.notMem),
      coe_insertElem, Finset.sum_insert hp.notMem]
    have hpt : p ∈ (insertElem s hp.notMem : Finset κ) := by
      rw [coe_insertElem]; exact Finset.mem_insert_self _ _
    have h1 : koszulDTerm b (i + 1) (α - Finsupp.single p 1) (insertElem s hp.notMem) p =
        -koszulKBasis k V b (i + 1) (α, s) := by
      have hpos : finsetPos (insertElem s hp.notMem : Finset κ) p = 0 :=
        finsetPos_insert_self hp.2.2
      have herase : eraseElem (insertElem s hp.notMem) ⟨p, hpt⟩ = s :=
        Subtype.ext (Finset.erase_insert hp.notMem)
      rw [koszulDTerm, dif_pos hpt, hpos, sub_single_add_single hp.one_le, herase]
      rw [koszulKBasis_apply, pow_one]
      change (((-1 : k) • b.symmetricAlgebra α) ⊗ₜ[k]
          (Module.Basis.exteriorPower (i + 1) b) s :
          SymmetricAlgebra k V ⊗[k] (⋀[k]^(i + 1) V)) =
        (-b.symmetricAlgebra α) ⊗ₜ[k] (Module.Basis.exteriorPower (i + 1) b) s
      set_option backward.isDefEq.respectTransparency true in
        simpa only [TensorProduct.neg_tmul] using
          congrArg (fun z : SymmetricAlgebra k V =>
            z ⊗ₜ[k] (Module.Basis.exteriorPower (i + 1) b) s)
            (neg_one_smul k (b.symmetricAlgebra α))
    have h2 : ∀ a ∈ (s : Finset κ), koszulH b i (koszulDTerm b i α s a) =
        koszulDTerm b (i + 1) (α - Finsupp.single p 1) (insertElem s hp.notMem) a := by
      intro a ha
      have hpa : p < a := hp.2.2 a ha
      have hat : a ∈ (insertElem s hp.notMem : Finset κ) := by
        rw [coe_insertElem]; exact Finset.mem_insert_of_mem ha
      -- `p` is still the pivot after `d` has moved `xₐ` into the monomial and deleted `a` from `s`.
      have hpiv2 : IsKoszulPivot (α + Finsupp.single a 1)
          ((eraseElem s ⟨a, ha⟩ : Finset κ)) p := by
        refine ⟨mem_support_add_single.mpr (Or.inr hp.1), fun m hm => ?_, fun c hc => ?_⟩
        · rcases mem_support_add_single.mp hm with rfl | hm
          · exact hpa.le
          · exact hp.2.1 m hm
        · rw [coe_eraseElem] at hc
          exact hp.2.2 c (Finset.mem_of_mem_erase hc)
      have hset : insertElem (eraseElem s ⟨a, ha⟩) hpiv2.notMem =
          eraseElem (insertElem s hp.notMem) ⟨a, hat⟩ :=
        Subtype.ext (Finset.erase_insert_of_ne (ne_of_lt hpa)).symm
      have hpos2 : finsetPos (insertElem s hp.notMem : Finset κ) a =
          finsetPos (s : Finset κ) a + 1 := finsetPos_insert_of_mem hp.2.2 ha
      rw [koszulDTerm, dif_pos ha, map_smul, koszulH_koszulKBasis,
        koszulHFun_of_isKoszulPivot b _ _ hpiv2, koszulDTerm, dif_pos hat, hpos2,
        ← sub_single_add_single_comm hp.one_le, hset, smul_neg, ← neg_smul]
      congr 1
      ring
    rw [h1, Finset.sum_congr rfl h2]
    abel
  · -- **Case B.** No pivot; `h` kills `x^α ⊗ e_s`, and in `h d` only the term deleting the least
    -- element `q` of `s` survives, contributing `x^α ⊗ e_s` back.
    have hpiv' : ∀ a, ¬IsKoszulPivot α (s : Finset κ) a := fun a h => hpiv ⟨a, h⟩
    rw [koszulHFun_of_forall_not b α s hpiv', map_zero, zero_add]
    have hqs : (s : Finset κ).min' hne ∈ (s : Finset κ) := Finset.min'_mem _ _
    rw [Finset.sum_eq_single_of_mem ((s : Finset κ).min' hne) hqs]
    · -- The `a = q` term.
      have hpivq : IsKoszulPivot (α + Finsupp.single ((s : Finset κ).min' hne) 1)
          ((eraseElem s ⟨(s : Finset κ).min' hne, hqs⟩ : Finset κ)) ((s : Finset κ).min' hne) := by
        refine ⟨mem_support_add_single.mpr (Or.inl rfl), fun m hm => ?_, fun c hc => ?_⟩
        · rcases mem_support_add_single.mp hm with rfl | hm
          · exact le_rfl
          · -- If some exponent sat below `q`, the least one would already be a pivot of `(α, s)`.
            rcases le_or_gt ((s : Finset κ).min' hne) m with hle | hcon
            · exact hle
            · have hsupp : α.support.Nonempty := ⟨m, hm⟩
              refine absurd ?_ (hpiv' (α.support.min' hsupp))
              refine ⟨Finset.min'_mem _ _, fun m' hm' => Finset.min'_le _ _ hm', fun c hc => ?_⟩
              calc α.support.min' hsupp ≤ m := Finset.min'_le _ _ hm
                _ < (s : Finset κ).min' hne := hcon
                _ ≤ c := Finset.min'_le _ _ hc
        · rw [coe_eraseElem] at hc
          exact lt_of_le_of_ne (Finset.min'_le _ _ (Finset.mem_of_mem_erase hc))
            (Ne.symm (Finset.ne_of_mem_erase hc))
      have hset : insertElem (eraseElem s ⟨(s : Finset κ).min' hne, hqs⟩) hpivq.notMem = s := by
        apply Subtype.ext
        rw [coe_insertElem, coe_eraseElem]
        exact Finset.insert_erase hqs
      rw [koszulDTerm, dif_pos hqs, map_smul, koszulH_koszulKBasis,
        koszulHFun_of_isKoszulPivot b _ _ hpivq, add_single_sub_single, hset,
        finsetPos_min' hne]
      simp
    · -- Every other term of `d` leaves `q` behind in the subset, so `h` kills it.
      intro a ha hane
      have hnp : ∀ c, ¬IsKoszulPivot (α + Finsupp.single a 1)
          ((eraseElem s ⟨a, ha⟩ : Finset κ)) c := by
        intro c hc
        have hqe : (s : Finset κ).min' hne ∈ (eraseElem s ⟨a, ha⟩ : Finset κ) := by
          rw [coe_eraseElem]; exact Finset.mem_erase.mpr ⟨Ne.symm hane, hqs⟩
        have hcq : c < (s : Finset κ).min' hne := hc.2.2 _ hqe
        have hqa : (s : Finset κ).min' hne ≤ a := Finset.min'_le _ _ ha
        have hcα : c ∈ α.support := by
          rcases mem_support_add_single.mp hc.1 with rfl | h
          · exact absurd (lt_of_lt_of_le hcq hqa) (lt_irrefl _)
          · exact h
        exact hpiv' c ⟨hcα, fun m hm => hc.2.1 m (mem_support_add_single.mpr (Or.inr hm)),
          fun c' hc' => lt_of_lt_of_le hcq (Finset.min'_le _ _ hc')⟩
      rw [koszulDTerm, dif_pos ha, map_smul, koszulH_koszulKBasis,
        koszulHFun_of_forall_not b _ _ hnp, smul_zero]

/-- **The homotopy identity in positive degrees**, `d ∘ h + h ∘ d = id` on `C_{i+1}`. Together
with `Etingof.koszulD_koszulH_add_eta_aug` this says the augmented Koszul complex is contractible
as a complex of `k`-modules, hence exact. -/
theorem koszulD_koszulH_add_koszulH_koszulD (b : Module.Basis κ k V) (i : ℕ)
    (x : koszulX k V (i + 1)) :
    koszulD b (i + 1) (koszulH b (i + 1) x) + koszulH b i (koszulD b i x) = x := by
  have hlin : ((koszulD b (i + 1)).restrictScalars k).comp (koszulH b (i + 1)) +
      (koszulH b i).comp ((koszulD b i).restrictScalars k) = LinearMap.id := by
    refine (koszulKBasis k V b (i + 1)).ext fun P => ?_
    obtain ⟨α, s⟩ := P
    simpa using koszulD_koszulH_add_koszulH_koszulD_koszulKBasis b i α s
  simpa using LinearMap.congr_fun hlin x

/-! ### `d h + η ε = id` in degree zero -/

omit [LinearOrder κ] [DecidableEq κ] [Fintype κ] in
theorem symmetricAlgebra_basis_zero (b : Module.Basis κ k V) : b.symmetricAlgebra 0 = 1 := by
  rw [symmetricAlgebra_basis_apply, MvPolynomial.monomial_zero', MvPolynomial.C_1, map_one]

omit [DecidableEq κ] [Fintype κ] in
theorem exteriorPower_basis_zero (b : Module.Basis κ k V) (s : Set.powersetCard κ 0) :
    b.exteriorPower 0 s = (exteriorPower.zeroEquiv k V).symm 1 := by
  apply (exteriorPower.zeroEquiv k V).injective
  rw [LinearEquiv.apply_symm_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  exact exteriorPower.zeroEquiv_ιMulti _

/-- The degree-zero homotopy identity `d h + η ε = id` on the basis vectors of `C₀`. -/
theorem koszulD_koszulH_add_eta_aug_koszulKBasis (b : Module.Basis κ k V) (α : κ →₀ ℕ)
    (s : Set.powersetCard κ 0) :
    koszulD b 0 (koszulH b 0 (koszulKBasis k V b 0 (α, s))) +
        koszulEta k V (koszulAug k V (koszulKBasis k V b 0 (α, s))) =
      koszulKBasis k V b 0 (α, s) := by
  have hs : (s : Finset κ) = ∅ := Finset.card_eq_zero.mp (Set.powersetCard.card_eq s)
  rw [koszulH_koszulKBasis]
  by_cases hα : α = 0
  · -- `x^0 ⊗ 1` is the one basis vector the homotopy misses; the splitting `η ε` catches it.
    subst hα
    rw [koszulHFun_of_forall_not b _ _ fun a h => by simpa using h.1, map_zero, zero_add]
    have haug : koszulAug k V (koszulKBasis k V b 0 (0, s)) =
        (KoszulAugModule.equiv k V).symm 1 := by
      apply (KoszulAugModule.equiv k V).injective
      rw [koszulAug_koszulKBasis, LinearEquiv.apply_symm_apply, if_pos rfl]
    rw [haug, koszulEta_apply, LinearEquiv.apply_symm_apply, map_one, koszulKBasis_apply,
      symmetricAlgebra_basis_zero, exteriorPower_basis_zero]
  · -- Otherwise the pivot is the least variable of `x^α`, the condition on `s = ∅` being vacuous.
    have hsupp : α.support.Nonempty := Finsupp.support_nonempty_iff.mpr hα
    have hp : IsKoszulPivot α (s : Finset κ) (α.support.min' hsupp) :=
      ⟨Finset.min'_mem _ _, fun m hm => Finset.min'_le _ _ hm, fun c hc => by
        rw [hs] at hc; exact absurd hc (Finset.notMem_empty c)⟩
    have haug : koszulAug k V (koszulKBasis k V b 0 (α, s)) = 0 := by
      apply (KoszulAugModule.equiv k V).injective
      rw [koszulAug_koszulKBasis, if_neg hα, map_zero]
    have hpt : α.support.min' hsupp ∈ (insertElem s hp.notMem : Finset κ) := by
      rw [coe_insertElem]; exact Finset.mem_insert_self _ _
    have hins : (insertElem s hp.notMem : Finset κ) = {α.support.min' hsupp} := by
      rw [coe_insertElem, hs]; rfl
    have herase : eraseElem (insertElem s hp.notMem) ⟨α.support.min' hsupp, hpt⟩ = s :=
      Subtype.ext (Finset.erase_insert hp.notMem)
    have hpos : finsetPos (insertElem s hp.notMem : Finset κ) (α.support.min' hsupp) = 0 :=
      finsetPos_insert_self hp.2.2
    rw [koszulHFun_of_isKoszulPivot b α s hp, map_neg,
      koszulD_koszulKBasis' b 0 (α - Finsupp.single (α.support.min' hsupp) 1)
        (insertElem s hp.notMem),
      hins, Finset.sum_singleton, koszulDTerm, dif_pos hpt, hpos,
      sub_single_add_single hp.one_le, herase, haug, map_zero, add_zero]
    rw [koszulKBasis_apply, pow_one]
    change -((((-1 : k) • b.symmetricAlgebra α) ⊗ₜ[k]
        (Module.Basis.exteriorPower 0 b) s :
        SymmetricAlgebra k V ⊗[k] (⋀[k]^0 V))) =
      b.symmetricAlgebra α ⊗ₜ[k] (Module.Basis.exteriorPower 0 b) s
    have hsign :
        ((-1 : k) • b.symmetricAlgebra α) ⊗ₜ[k] (Module.Basis.exteriorPower 0 b) s =
          -(b.symmetricAlgebra α ⊗ₜ[k] (Module.Basis.exteriorPower 0 b) s) := by
      simpa only [TensorProduct.neg_tmul] using
        congrArg (fun z : SymmetricAlgebra k V =>
          z ⊗ₜ[k] (Module.Basis.exteriorPower 0 b) s)
          (neg_one_smul k (b.symmetricAlgebra α))
    set_option backward.isDefEq.respectTransparency true in
      exact (congrArg Neg.neg hsign).trans (neg_neg _)

/-- **The degree-zero homotopy identity**, `d ∘ h + η ∘ ε = id` on `C₀`. -/
theorem koszulD_koszulH_add_eta_aug (b : Module.Basis κ k V) (x : koszulX k V 0) :
    koszulD b 0 (koszulH b 0 x) + koszulEta k V (koszulAug k V x) = x := by
  have hlin : ((koszulD b 0).restrictScalars k).comp (koszulH b 0) +
      (koszulEta k V).comp ((koszulAug k V).restrictScalars k) = LinearMap.id := by
    refine (koszulKBasis k V b 0).ext fun P => ?_
    obtain ⟨α, s⟩ := P
    simpa using koszulD_koszulH_add_eta_aug_koszulKBasis b α s
  simpa using LinearMap.congr_fun hlin x

/-! ### `LinearMap`-level restatements -/

theorem koszulD_comp_koszulH_add_koszulH_comp_koszulD (b : Module.Basis κ k V) (i : ℕ) :
    ((koszulD b (i + 1)).restrictScalars k).comp (koszulH b (i + 1)) +
      (koszulH b i).comp ((koszulD b i).restrictScalars k) = LinearMap.id :=
  LinearMap.ext fun x => by
    simpa using koszulD_koszulH_add_koszulH_koszulD b i x

theorem koszulD_comp_koszulH_add_koszulEta_comp_koszulAug (b : Module.Basis κ k V) :
    ((koszulD b 0).restrictScalars k).comp (koszulH b 0) +
      (koszulEta k V).comp ((koszulAug k V).restrictScalars k) = LinearMap.id :=
  LinearMap.ext fun x => by
    simpa using koszulD_koszulH_add_eta_aug b x

end Homotopy

end Etingof

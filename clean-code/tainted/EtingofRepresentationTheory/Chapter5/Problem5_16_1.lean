import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.CharValueHookFormula

/-!
# Problem 5.16.1: the branching rule for `Sₙ ⊆ Sₙ₊₁`

**Problem 5.16.1.** For a Young diagram `μ`, let `A(μ)` be the set of Young diagrams obtained by
adding a square to `μ`, and let `R(μ)` be the set of Young diagrams obtained by removing a square
from `μ`.

(a) Show that `Res_{S_{n-1}}^{S_n} V_μ = ⨁_{λ ∈ R(μ)} V_λ`.

(b) Show that `Ind_{S_{n-1}}^{S_n} V_μ = ⨁_{λ ∈ A(μ)} V_λ`.

## Formalization

We index by `n` and `n+1` (avoiding natural-number subtraction). `Sₙ = Equiv.Perm (Fin n)` is
embedded into `Sₙ₊₁ = Equiv.Perm (Fin (n+1))` as the pointwise stabilizer of the last point via
`permEmb := Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb`.

* **Adding/removing a square via containment.** A Young diagram of size `n` obtained by removing one
  square from `μ ⊢ n+1` is exactly a diagram `λ ⊢ n` contained in `μ` (`λ ⊆ μ`); dually a diagram of
  size `n+1` obtained by adding a square to `μ ⊢ n` is a `λ ⊢ n+1` containing `μ`. So
  `removeSquare μ = {λ : Nat.Partition n // λ ⊆ μ}` and `addSquare μ = {λ : Nat.Partition (n+1) //
  μ ⊆ λ}`, using containment of `Nat.Partition.toYoungDiagram`.
* **(a) Restriction.** The character of `Res V_μ` (the character of `V_μ` evaluated on the image of
  `Sₙ` in `Sₙ₊₁`) equals the sum of the characters of the `V_λ` for `λ ∈ R(μ)`. Over `ℂ`, this
  character identity is equivalent to the isomorphism `Res V_μ ≅ ⨁_{λ ∈ R(μ)} V_λ`.
* **(b) Induction.** By Frobenius reciprocity the multiplicity of `V_λ` (`λ ⊢ n+1`) in
  `Ind_{Sₙ}^{Sₙ₊₁} V_μ` equals the multiplicity of `V_μ` in `Res V_λ`, i.e. the reciprocity pairing
  `⟨χ_{V_μ}, Res χ_{V_λ}⟩_{Sₙ}`. We state that this pairing is `1` if `μ ⊆ λ` (`λ ∈ A(μ)`) and `0`
  otherwise, precisely `Ind V_μ = ⨁_{λ ∈ A(μ)} V_λ`.

Both parts are proved: (a) `res_spechtModule_character` via the Frobenius character formula and
the Pieri rule for `p₁` (`res_charValue_sum`), and (b) `ind_spechtModule_multiplicity` via
Frobenius reciprocity and Specht-character orthonormality.
-/

noncomputable section

namespace Etingof

open scoped Classical

/-- The embedding `Sₙ ↪ Sₙ₊₁` as the pointwise stabilizer of the last point of `Fin (n+1)`,
extending a permutation of `Fin n` by the identity via `Fin.castSuccEmb`. -/
noncomputable def permEmb (n : ℕ) :
    Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb

/-- `R(μ)` for `μ ⊢ n+1`: the Young diagrams obtained by removing one square, i.e. the partitions
`λ ⊢ n` whose diagram is contained in that of `μ`. -/
noncomputable def removeSquare {n : ℕ} (μ : Nat.Partition (n + 1)) :
    Finset (Nat.Partition n) :=
  Finset.univ.filter fun la => la.toYoungDiagram ≤ μ.toYoungDiagram

/-- `A(μ)` for `μ ⊢ n`: the Young diagrams obtained by adding one square, i.e. the partitions
`λ ⊢ n+1` whose diagram contains that of `μ`. -/
noncomputable def addSquare {n : ℕ} (μ : Nat.Partition n) :
    Finset (Nat.Partition (n + 1)) :=
  Finset.univ.filter fun la => μ.toYoungDiagram ≤ la.toYoungDiagram

/-- The Frobenius-reciprocity pairing of two class functions on `Sₙ`:
`⟨χ, ψ⟩ = |Sₙ|⁻¹ Σ_σ χ(σ) ψ(σ⁻¹)`. -/
noncomputable def branchingPairing (n : ℕ)
    (χ ψ : Equiv.Perm (Fin n) → ℂ) : ℂ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), χ σ * ψ σ⁻¹

/-- The embedding `Sₙ ↪ Sₙ₊₁` adds a fixed point, so the full cycle type of `permEmb n σ`
is that of `σ` with one extra `1`-cycle. -/
lemma fullCycleType_permEmb (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    fullCycleType (n + 1) (permEmb n σ) = 1 ::ₘ fullCycleType n σ := by
  have hct : (permEmb n σ).cycleType = σ.cycleType := by
    rw [permEmb, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
    simp only [Equiv.Perm.cycleType_extendDomain]
  have hsupp : (permEmb n σ).support.card = σ.support.card := by
    rw [permEmb, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
    simp only [Equiv.Perm.card_support_extend_domain]
  have hle : σ.support.card ≤ n := σ.support.card_le_univ.trans_eq (Fintype.card_fin n)
  unfold fullCycleType
  rw [hct, hsupp, show n + 1 - σ.support.card = (n - σ.support.card) + 1 from by omega,
    Multiset.replicate_succ, Multiset.add_cons]

/-- The power-sum polynomial of the embedded permutation factors out `∑ⱼ Xⱼ = psum 1`. -/
lemma psumPart_permEmb (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.psumPart (Fin (n + 1)) ℚ (fullCycleTypePartition (permEmb n σ)) =
      (∑ i, MvPolynomial.X i) *
        MvPolynomial.psumPart (Fin (n + 1)) ℚ (fullCycleTypePartition σ) := by
  simp only [MvPolynomial.psumPart]
  rw [show (fullCycleTypePartition (permEmb n σ)).parts = fullCycleType (n + 1) (permEmb n σ) from
      rfl, fullCycleType_permEmb n σ,
    show (1 ::ₘ fullCycleType n σ) = (1 : ℕ) ::ₘ (fullCycleTypePartition σ).parts from rfl,
    Multiset.map_cons, Multiset.prod_cons, MvPolynomial.psum_one]

/-! ### Row-length bounded partition and the containment correspondence -/

/-- Containment of Young diagrams is equivalent to row-by-row containment of row lengths. -/
lemma youngDiagram_le_iff_rowLen {μ ν : YoungDiagram} :
    μ ≤ ν ↔ ∀ i, μ.rowLen i ≤ ν.rowLen i := by
  constructor
  · intro h i
    rcases Nat.eq_zero_or_pos (μ.rowLen i) with hz | hz
    · omega
    · have hmem : (i, μ.rowLen i - 1) ∈ μ := by rw [YoungDiagram.mem_iff_lt_rowLen]; omega
      have := SetLike.le_def.mp h hmem
      rw [YoungDiagram.mem_iff_lt_rowLen] at this; omega
  · intro h
    rw [SetLike.le_def]
    rintro ⟨i, j⟩ hc
    rw [YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
    exact lt_of_lt_of_le hc (h i)

/-- Rows past index `n-1` of a partition of `n` are empty. -/
lemma toYoungDiagram_rowLen_eq_zero_of_ge {n : ℕ} (la : Nat.Partition n) {i : ℕ} (hi : n ≤ i) :
    la.toYoungDiagram.rowLen i = 0 := by
  classical
  by_contra hne
  have hmem : (i, 0) ∈ la.toYoungDiagram := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have hsub : (Finset.range (i + 1)).image (fun k => ((k, 0) : ℕ × ℕ)) ⊆
      la.toYoungDiagram.cells := by
    intro c hc'
    simp only [Finset.mem_image, Finset.mem_range] at hc'
    obtain ⟨k, hk, rfl⟩ := hc'
    exact (YoungDiagram.mem_cells _).mpr
      (la.toYoungDiagram.isLowerSet (show ((k, 0) : ℕ × ℕ) ≤ (i, 0) from ⟨by omega, le_refl 0⟩)
        hmem)
  have h1 : ((Finset.range (i + 1)).image (fun k => ((k, 0) : ℕ × ℕ))).card ≤
      la.toYoungDiagram.cells.card := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range,
    la.toYoungDiagram_card] at h1
  omega

/-- The row lengths of a partition of `n` sum to `n` (all rows fit within `Fin (n+1)`). -/
lemma sum_rowLen_fin (n : ℕ) (la : Nat.Partition n) :
    ∑ i : Fin (n + 1), la.toYoungDiagram.rowLen i.val = n := by
  classical
  have hcell : ∀ i j : ℕ, (i, j) ∈ la.toYoungDiagram.cells → i < n + 1 := by
    intro i j hc
    by_contra h
    have := (YoungDiagram.mem_cells _).mp hc
    rw [YoungDiagram.mem_iff_lt_rowLen] at this
    rw [toYoungDiagram_rowLen_eq_zero_of_ge la (by omega)] at this
    omega
  have hbi : la.toYoungDiagram.cells = Finset.univ.biUnion
      (fun i : Fin (n + 1) =>
        ({i.val} : Finset ℕ) ×ˢ Finset.range (la.toYoungDiagram.rowLen i.val)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_range]
    constructor
    · intro hc
      exact ⟨⟨i, hcell i j hc⟩, rfl,
        (YoungDiagram.mem_iff_lt_rowLen.mp ((YoungDiagram.mem_cells _).mp hc))⟩
    · rintro ⟨i', rfl, hj⟩
      exact (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
  have hsum : (∑ i : Fin (n + 1), la.toYoungDiagram.rowLen i.val)
      = la.toYoungDiagram.cells.card := by
    rw [hbi, Finset.card_biUnion (fun x _ y _ hxy => Finset.disjoint_left.mpr (by
      rintro ⟨a, b⟩ ha hb
      simp only [Finset.mem_product, Finset.mem_singleton] at ha hb
      exact hxy (Fin.val_injective (ha.1.symm.trans hb.1))))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul]
  rw [hsum, la.toYoungDiagram_card]

/-- Two lists of positive naturals with equal `getD i 0` at every index are equal. -/
lemma list_ext_getD_of_pos {L M : List ℕ} (hL : ∀ x ∈ L, 0 < x) (hM : ∀ x ∈ M, 0 < x)
    (h : ∀ i, L.getD i 0 = M.getD i 0) : L = M := by
  apply List.ext_getElem?
  intro i
  rcases lt_or_ge i L.length with hiL | hiL
  · rcases lt_or_ge i M.length with hiM | hiM
    · rw [List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hiM]
      have := h i
      rw [List.getD_eq_getElem _ _ hiL, List.getD_eq_getElem _ _ hiM] at this
      rw [this]
    · exfalso
      have hLi : 0 < L.getD i 0 := by
        rw [List.getD_eq_getElem _ _ hiL]; exact hL _ (List.getElem_mem _)
      rw [h i, List.getD_eq_default _ _ hiM] at hLi; exact absurd hLi (lt_irrefl 0)
  · rcases lt_or_ge i M.length with hiM | hiM
    · exfalso
      have hMi : 0 < M.getD i 0 := by
        rw [List.getD_eq_getElem _ _ hiM]; exact hM _ (List.getElem_mem _)
      rw [← h i, List.getD_eq_default _ _ hiL] at hMi; exact absurd hMi (lt_irrefl 0)
    · rw [List.getElem?_eq_none hiL, List.getElem?_eq_none hiM]

/-- The bounded partition (with `n+1` parts) recording the row lengths of `λ ⊢ n`. -/
noncomputable def resBP {n : ℕ} (la : Nat.Partition n) : BoundedPartition (n + 1) n where
  parts i := la.toYoungDiagram.rowLen i.val
  decreasing i j hij := la.toYoungDiagram.rowLen_anti i.val j.val hij
  sum_eq := sum_rowLen_fin n la

/-- `weightToPartition` recovers `λ` from its row-length bounded partition. -/
lemma weightToPartition_resBP {n : ℕ} (la : Nat.Partition n) :
    ((resBP la).sum_eq ▸ weightToPartition (n + 1) (resBP la).parts : Nat.Partition n) = la := by
  have hrec : ∀ (p q : ℕ) (heq : p = q) (P : Nat.Partition p), (heq ▸ P).parts = P.parts := by
    intro p q heq P; subst heq; rfl
  set WP := weightToPartition (n + 1) (resBP la).parts with hWP
  -- Row lengths of `WP` and `la` agree at every index.
  have hrl : ∀ i : ℕ, WP.toYoungDiagram.rowLen i = la.toYoungDiagram.rowLen i := by
    intro i
    rcases lt_or_ge i (n + 1) with hi | hi
    · rw [hWP, weightToPartition_rowLen (n + 1) (resBP la) ⟨i, hi⟩]; rfl
    · rw [hWP, weightToPartition_rowLen_eq_zero (n + 1) _ hi,
        toYoungDiagram_rowLen_eq_zero_of_ge la (by omega)]
  -- Hence their sorted-parts lists agree, so the partitions agree.
  have hsp : WP.sortedParts = la.sortedParts := by
    apply list_ext_getD_of_pos
    · intro x hx; exact WP.parts_pos ((Multiset.mem_sort _).mp hx)
    · intro x hx; exact la.parts_pos ((Multiset.mem_sort _).mp hx)
    · intro i
      have := hrl i
      rwa [Nat.Partition.toYoungDiagram_rowLen_eq_getD,
        Nat.Partition.toYoungDiagram_rowLen_eq_getD] at this
  apply Nat.Partition.ext
  rw [hrec _ _ (resBP la).sum_eq]
  have hWPp : WP.parts = ↑WP.sortedParts := (Multiset.sort_eq _ _).symm
  have hlap : la.parts = ↑la.sortedParts := (Multiset.sort_eq _ _).symm
  rw [hWPp, hlap, hsp]

/-- The parts of a bounded partition are the row lengths of its underlying partition. -/
lemma bp_parts_eq_rowLen {N m : ℕ} (bp : BoundedPartition N m) (i : Fin N) :
    bp.parts i =
      (bp.sum_eq ▸ weightToPartition N bp.parts : Nat.Partition m).toYoungDiagram.rowLen i.val := by
  have hrec : ∀ (p q : ℕ) (heq : p = q) (P : Nat.Partition p),
      (heq ▸ P).toYoungDiagram = P.toYoungDiagram := by intro p q heq P; subst heq; rfl
  rw [hrec _ _ bp.sum_eq, weightToPartition_rowLen N bp i]

/-- Two partitions of `n` with equal row lengths at every index are equal. -/
lemma Partition_eq_of_rowLen_eq {n : ℕ} {p q : Nat.Partition n}
    (h : ∀ i, p.toYoungDiagram.rowLen i = q.toYoungDiagram.rowLen i) : p = q := by
  have hsp : p.sortedParts = q.sortedParts := by
    apply list_ext_getD_of_pos
    · intro x hx; exact p.parts_pos ((Multiset.mem_sort _).mp hx)
    · intro x hx; exact q.parts_pos ((Multiset.mem_sort _).mp hx)
    · intro i
      have := h i
      rwa [Nat.Partition.toYoungDiagram_rowLen_eq_getD,
        Nat.Partition.toYoungDiagram_rowLen_eq_getD] at this
  apply Nat.Partition.ext
  rw [show p.parts = ↑p.sortedParts from (Multiset.sort_eq _ _).symm,
    show q.parts = ↑q.sortedParts from (Multiset.sort_eq _ _).symm, hsp]

/-- `i` is a *legal box-removal row* for the weight `a`: row `i` is nonempty and strictly
longer than every later row. -/
def IsLegalRem {n : ℕ} (a : Fin (n + 1) → ℕ) (i : Fin (n + 1)) : Prop :=
  1 ≤ a i ∧ ∀ j : Fin (n + 1), i < j → a j ≤ a i - 1

/-- The bounded partition obtained by removing one box from row `i` of a legal weight. -/
def bpDecr {n : ℕ} (a : Fin (n + 1) → ℕ) (hant : Antitone a) (hsum : ∑ j, a j = n + 1)
    (i : Fin (n + 1)) (hleg : IsLegalRem a i) : BoundedPartition (n + 1) n where
  parts j := if j = i then a j - 1 else a j
  decreasing := by
    intro p r hpr
    change (if r = i then a r - 1 else a r) ≤ (if p = i then a p - 1 else a p)
    by_cases hp : p = i <;> by_cases hr : r = i
    · rw [if_pos hp, if_pos hr]
      have : a p = a r := by rw [hp, hr]
      omega
    · rw [if_pos hp, if_neg hr]
      have hlt : i < r := lt_of_le_of_ne (hp ▸ hpr) (Ne.symm hr)
      have := hleg.2 r hlt; rw [hp]; exact this
    · rw [if_neg hp, if_pos hr]
      have : a r ≤ a p := hant hpr
      omega
    · rw [if_neg hp, if_neg hr]; exact hant hpr
  sum_eq := by
    have hsplit : ∀ j, (if j = i then a j - 1 else a j) + (if j = i then 1 else 0) = a j := by
      intro j; by_cases hj : j = i
      · rw [if_pos hj, if_pos hj]; have : 1 ≤ a j := hj ▸ hleg.1; omega
      · rw [if_neg hj, if_neg hj, add_zero]
    have h2 : ∑ j, ((if j = i then a j - 1 else a j) + (if j = i then 1 else 0)) = n + 1 := by
      rw [Finset.sum_congr rfl (fun j _ => hsplit j)]; exact hsum
    rw [Finset.sum_add_distrib] at h2
    have h3 : ∑ j : Fin (n + 1), (if j = i then 1 else 0) = 1 := by
      rw [Finset.sum_ite_eq' Finset.univ i (fun _ => 1)]; simp
    omega

@[simp] lemma bpDecr_parts {n : ℕ} (a : Fin (n + 1) → ℕ) (hant : Antitone a)
    (hsum : ∑ j, a j = n + 1) (i : Fin (n + 1)) (hleg : IsLegalRem a i) (j : Fin (n + 1)) :
    (bpDecr a hant hsum i hleg).parts j = if j = i then a j - 1 else a j := rfl

/-- The `shiftedExps` of a weight over `Fin (n+1)` is `f j + (n - j)`. -/
lemma shiftedExps_val {n : ℕ} (f : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    shiftedExps (n + 1) f j = f j + (n - j.val) := by
  simp [shiftedExps]

/-- **Core coefficient identity (Pieri rule for `p₁`).** Extracting the `(μ+ρ)`-coefficient of
`Δ · (∑ⱼ Xⱼ) · p_ν` sums the `charValue`s over all box removals of `μ`. Here `Δ` is the
Vandermonde alternant, `∑ⱼ Xⱼ = p₁`, and `removeSquare μ` are the diagrams `λ ⊢ n` contained in
`μ ⊢ n+1`. -/
lemma res_charValue_sum (n : ℕ) (bpμ : BoundedPartition (n + 1) (n + 1)) (ν : Nat.Partition n) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (shiftedExps (n + 1) bpμ.parts))
        ((alternantMatrix (n + 1) (vandermondeExps (n + 1))).det *
          ((∑ i, MvPolynomial.X i) * MvPolynomial.psumPart (Fin (n + 1)) ℚ ν))
      = ∑ la ∈ removeSquare (bpμ.sum_eq ▸ weightToPartition (n + 1) bpμ.parts),
          charValue (n + 1) (resBP la) ν := by
  classical
  set μ := (bpμ.sum_eq ▸ weightToPartition (n + 1) bpμ.parts : Nat.Partition (n + 1)) with hμ
  set g := (alternantMatrix (n + 1) (vandermondeExps (n + 1))).det *
    MvPolynomial.psumPart (Fin (n + 1)) ℚ ν with hg
  set D := Finsupp.equivFunOnFinite.symm (shiftedExps (n + 1) bpμ.parts) with hD
  -- Abbreviations for the box-removal bounded partition and its underlying partition.
  set bpd : (i : Fin (n + 1)) → IsLegalRem bpμ.parts i → BoundedPartition (n + 1) n :=
    fun i hleg => bpDecr bpμ.parts bpμ.decreasing bpμ.sum_eq i hleg with hbpd
  set partOf : (i : Fin (n + 1)) → IsLegalRem bpμ.parts i → Nat.Partition n :=
    fun i hleg => (bpd i hleg).sum_eq ▸ weightToPartition (n + 1) (bpd i hleg).parts with hpartOf
  have hbpd_parts : ∀ (i : Fin (n + 1)) (hleg : IsLegalRem bpμ.parts i) (j : Fin (n + 1)),
      (bpd i hleg).parts j = if j = i then bpμ.parts j - 1 else bpμ.parts j := by
    intro i hleg j; simp only [hbpd, bpDecr_parts]
  -- `g` is antisymmetric.
  have hanti : ∀ τ : Equiv.Perm (Fin (n + 1)),
      MvPolynomial.rename τ g = Equiv.Perm.sign τ • g := by
    intro τ
    rw [hg, map_mul, rename_alternant_det, (psumPart_isSymmetric (n + 1) ν) τ, smul_mul_assoc]
  -- Row lengths of `μ`.
  have hμrow : ∀ i : Fin (n + 1), μ.toYoungDiagram.rowLen i.val = bpμ.parts i := by
    intro i; rw [hμ]; exact (bp_parts_eq_rowLen bpμ i).symm
  have hμrow0 : ∀ k : ℕ, n + 1 ≤ k → μ.toYoungDiagram.rowLen k = 0 := fun k hk =>
    toYoungDiagram_rowLen_eq_zero_of_ge μ (by omega)
  -- `D i = shiftedExps` value.
  have hDval : ∀ i : Fin (n + 1), D i = bpμ.parts i + (n - i.val) := by
    intro i; rw [hD, Finsupp.coe_equivFunOnFinite_symm, shiftedExps_val]
  -- The box-removal exponent equals `D` minus a unit.
  have hexp : ∀ (i : Fin (n + 1)) (hleg : IsLegalRem bpμ.parts i),
      D - Finsupp.single i 1
        = Finsupp.equivFunOnFinite.symm (shiftedExps (n + 1) (bpd i hleg).parts) := by
    intro i hleg
    apply Finsupp.ext
    intro j
    have hL : (D - Finsupp.single i (1 : ℕ)) j
        = bpμ.parts j + (n - j.val) - (if i = j then 1 else 0) := by
      rw [Finsupp.tsub_apply, hDval, Finsupp.single_apply]
    have hR : (Finsupp.equivFunOnFinite.symm (shiftedExps (n + 1) (bpd i hleg).parts)) j
        = (if j = i then bpμ.parts j - 1 else bpμ.parts j) + (n - j.val) := by
      rw [Finsupp.coe_equivFunOnFinite_symm, shiftedExps_val, hbpd_parts]
    rw [hL, hR]
    by_cases hj : j = i
    · rw [if_pos hj.symm, if_pos hj]
      have hpj : 1 ≤ bpμ.parts j := by rw [hj]; exact hleg.1
      omega
    · rw [if_neg (fun h => hj h.symm), if_neg hj]; omega
  -- For a legal row, the coefficient is the corresponding `charValue`.
  have hval_coeff : ∀ (i : Fin (n + 1)) (hleg : IsLegalRem bpμ.parts i),
      MvPolynomial.coeff (D - Finsupp.single i (1 : ℕ)) g
        = charValue (n + 1) (resBP (partOf i hleg)) ν := by
    intro i hleg
    have hpe : (bpd i hleg).parts = (resBP (partOf i hleg)).parts := by
      funext k
      change (bpd i hleg).parts k = (partOf i hleg).toYoungDiagram.rowLen k.val
      simp only [hpartOf]; exact bp_parts_eq_rowLen (bpd i hleg) k
    rw [hexp i hleg, hpe]; rfl
  -- Legal ⇒ in support.
  have hsupp_of_legal : ∀ (i : Fin (n + 1)), IsLegalRem bpμ.parts i → i ∈ D.support := by
    intro i hleg
    rw [Finsupp.mem_support_iff, hDval]; have := hleg.1; omega
  set legalFinset := Finset.univ.filter (fun i : Fin (n + 1) => IsLegalRem bpμ.parts i) with hLF
  -- Terms vanish off `legalFinset`.
  have hzero : ∀ i ∈ Finset.univ, i ∉ legalFinset →
      (if i ∈ D.support then MvPolynomial.coeff (D - Finsupp.single i (1 : ℕ)) g else 0) = 0 := by
    intro i _ hi
    have hnleg : ¬ IsLegalRem bpμ.parts i := by simpa [hLF] using hi
    by_cases hmem : i ∈ D.support
    · rw [if_pos hmem]
      have hsi : bpμ.parts i + (n - i.val) ≠ 0 := by
        have := hmem; rw [Finsupp.mem_support_iff, hDval] at this; exact this
      -- Row index is `< n` (the last row would be a fixed point already handled).
      have hival : i.val < n := by
        by_contra hge
        have hie : i.val = n := by omega
        exact hnleg ⟨by rw [hie] at hsi; omega, fun j hj => by
          exact absurd hj (by rw [Fin.lt_def]; omega)⟩
      set j0 : Fin (n + 1) := ⟨i.val + 1, by omega⟩ with hj0
      have hj0v : j0.val = i.val + 1 := by rw [hj0]
      have hij0lt : i < j0 := by rw [Fin.lt_def]; omega
      have haj0le : bpμ.parts j0 ≤ bpμ.parts i := bpμ.decreasing (le_of_lt hij0lt)
      have haieq : bpμ.parts i = bpμ.parts j0 := by
        rcases eq_or_lt_of_le haj0le with h | h
        · exact h.symm
        · exfalso; apply hnleg
          refine ⟨by omega, fun j hj => ?_⟩
          have hjj0 : j0 ≤ j := by
            rw [Fin.le_iff_val_le_val]; rw [Fin.lt_def] at hj; omega
          have := bpμ.decreasing hjj0; omega
      have hij0 : i ≠ j0 := by rw [Ne, Fin.ext_iff]; omega
      have hdeq : (D - Finsupp.single i (1 : ℕ)) i = (D - Finsupp.single i (1 : ℕ)) j0 := by
        rw [Finsupp.tsub_apply, Finsupp.tsub_apply, hDval, hDval, Finsupp.single_apply,
          Finsupp.single_apply, if_pos rfl, if_neg hij0, haieq]
        omega
      exact coeff_zero_of_antisym_repeated (i := i) (j := j0) g hanti (D - Finsupp.single i (1 : ℕ))
        hij0 hdeq
    · rw [if_neg hmem]
  -- Rewrite the coefficient sum, restrict to legal rows, and match the box-removal sum.
  rw [show (alternantMatrix (n + 1) (vandermondeExps (n + 1))).det *
        ((∑ i, MvPolynomial.X i) * MvPolynomial.psumPart (Fin (n + 1)) ℚ ν)
        = (∑ i, MvPolynomial.X i) * g from by rw [hg]; ring,
    Finset.sum_mul, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_X_mul']
  rw [← Finset.sum_subset (Finset.subset_univ legalFinset) hzero]
  refine Finset.sum_bij (fun i hi => partOf i (Finset.mem_filter.mp hi).2) ?_ ?_ ?_ ?_
  · -- maps into `removeSquare μ`
    intro i hi
    have hleg := (Finset.mem_filter.mp hi).2
    rw [removeSquare, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [youngDiagram_le_iff_rowLen]
    intro k
    rcases lt_or_ge k (n + 1) with hk | hk
    · rw [show (partOf i hleg).toYoungDiagram.rowLen k = (bpd i hleg).parts ⟨k, hk⟩ from by
          simp only [hpartOf]; exact (bp_parts_eq_rowLen (bpd i hleg) ⟨k, hk⟩).symm,
        hμrow ⟨k, hk⟩, hbpd_parts i hleg ⟨k, hk⟩]
      split <;> omega
    · rw [toYoungDiagram_rowLen_eq_zero_of_ge (partOf i hleg) (by omega), hμrow0 k hk]
  · -- injective
    intro i hi i' hi' heq
    have hleg := (Finset.mem_filter.mp hi).2
    have hleg' := (Finset.mem_filter.mp hi').2
    by_contra hne
    have h1 : (bpd i hleg).parts i = (bpd i' hleg').parts i := by
      rw [bp_parts_eq_rowLen (bpd i hleg) i, bp_parts_eq_rowLen (bpd i' hleg') i]
      change (partOf i hleg).toYoungDiagram.rowLen i.val
          = (partOf i' hleg').toYoungDiagram.rowLen i.val
      rw [heq]
    rw [hbpd_parts i hleg i, hbpd_parts i' hleg' i, if_pos rfl, if_neg hne] at h1
    have := hleg.1; omega
  · -- surjective
    intro la hla
    rw [removeSquare, Finset.mem_filter] at hla
    have hle := hla.2
    rw [youngDiagram_le_iff_rowLen] at hle
    have htermle : ∀ k : Fin (n + 1), la.toYoungDiagram.rowLen k.val ≤ bpμ.parts k := by
      intro k; have := hle k.val; rwa [hμrow k] at this
    have hsumterm : ∑ k : Fin (n + 1), (bpμ.parts k - la.toYoungDiagram.rowLen k.val) = 1 := by
      have h1 : ∑ k : Fin (n + 1), la.toYoungDiagram.rowLen k.val = n := sum_rowLen_fin n la
      have h3 : ∑ k : Fin (n + 1),
          (la.toYoungDiagram.rowLen k.val + (bpμ.parts k - la.toYoungDiagram.rowLen k.val))
          = ∑ k, bpμ.parts k :=
        Finset.sum_congr rfl fun k _ => by have := htermle k; omega
      rw [Finset.sum_add_distrib, h1, bpμ.sum_eq] at h3
      omega
    obtain ⟨i, hi1⟩ : ∃ i : Fin (n + 1), bpμ.parts i - la.toYoungDiagram.rowLen i.val = 1 := by
      by_contra hcon; push Not at hcon
      have hz : ∀ k, bpμ.parts k - la.toYoungDiagram.rowLen k.val = 0 := by
        intro k; by_contra hk0
        have hge : 2 ≤ bpμ.parts k - la.toYoungDiagram.rowLen k.val := by have := hcon k; omega
        have hle2 := Finset.single_le_sum
          (f := fun k => bpμ.parts k - la.toYoungDiagram.rowLen k.val)
          (fun k _ => Nat.zero_le _) (Finset.mem_univ k)
        rw [hsumterm] at hle2; omega
      rw [Finset.sum_eq_zero (fun k _ => hz k)] at hsumterm; omega
    have hother : ∀ j : Fin (n + 1), j ≠ i →
        bpμ.parts j - la.toYoungDiagram.rowLen j.val = 0 := by
      intro j hj; by_contra hj0
      have hpair : (bpμ.parts i - la.toYoungDiagram.rowLen i.val)
          + (bpμ.parts j - la.toYoungDiagram.rowLen j.val)
          ≤ ∑ k, (bpμ.parts k - la.toYoungDiagram.rowLen k.val) := by
        rw [← Finset.sum_pair (f := fun k => bpμ.parts k - la.toYoungDiagram.rowLen k.val)
          (Ne.symm hj)]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [hsumterm] at hpair; omega
    have hleg : IsLegalRem bpμ.parts i := by
      refine ⟨by omega, fun j hj => ?_⟩
      have hji : j ≠ i := Ne.symm (ne_of_lt hj)
      have h1 : bpμ.parts j - la.toYoungDiagram.rowLen j.val = 0 := hother j hji
      have h1' : la.toYoungDiagram.rowLen j.val ≤ bpμ.parts j := htermle j
      have h2 : la.toYoungDiagram.rowLen j.val ≤ la.toYoungDiagram.rowLen i.val :=
        la.toYoungDiagram.rowLen_anti i.val j.val (le_of_lt (by rwa [Fin.lt_def] at hj))
      omega
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hleg⟩, ?_⟩
    -- `partOf i hleg = la`
    apply Partition_eq_of_rowLen_eq
    intro k
    rcases lt_or_ge k (n + 1) with hk | hk
    · rw [show (partOf i hleg).toYoungDiagram.rowLen k = (bpd i hleg).parts ⟨k, hk⟩ from by
          simp only [hpartOf]; exact (bp_parts_eq_rowLen (bpd i hleg) ⟨k, hk⟩).symm,
        hbpd_parts i hleg ⟨k, hk⟩]
      by_cases hki : (⟨k, hk⟩ : Fin (n + 1)) = i
      · have hkv : k = i.val := congrArg Fin.val hki
        rw [if_pos hki, show (⟨k, hk⟩ : Fin (n + 1)) = i from hki, show k = i.val from hkv]
        omega
      · rw [if_neg hki]
        have h : bpμ.parts ⟨k, hk⟩ - la.toYoungDiagram.rowLen k = 0 := hother ⟨k, hk⟩ hki
        have h' : la.toYoungDiagram.rowLen k ≤ bpμ.parts ⟨k, hk⟩ := htermle ⟨k, hk⟩
        omega
    · rw [toYoungDiagram_rowLen_eq_zero_of_ge (partOf i hleg) (by omega),
        toYoungDiagram_rowLen_eq_zero_of_ge la (by omega)]
  · -- values match
    intro i hi
    have hleg := (Finset.mem_filter.mp hi).2
    rw [if_pos (hsupp_of_legal i hleg)]
    exact hval_coeff i hleg

/-- Problem 5.16.1(a). Branching rule for restriction: for `μ ⊢ n+1`, the restriction of the
Specht module `V_μ` to `Sₙ ⊆ Sₙ₊₁` decomposes as `⨁_{λ ∈ R(μ)} V_λ`. Equivalently, on every
`σ ∈ Sₙ` the character of `V_μ` at the image `permEmb σ` equals the sum of the characters of the
`V_λ` over `λ ∈ R(μ)`. -/
theorem res_spechtModule_character (n : ℕ) (μ : Nat.Partition (n + 1))
    (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter (n + 1) μ (permEmb n σ) =
      ∑ la ∈ removeSquare μ, spechtModuleCharacter n la σ := by
  classical
  obtain ⟨bpμ, hbpμ⟩ := exists_boundedPartition_weightToPartition_eq (n + 1) μ
  -- Relate the left side to `charValue` over `n+1` variables.
  have hLHS : spechtModuleCharacter (n + 1) μ (permEmb n σ) =
      ((charValue (n + 1) bpμ (fullCycleTypePartition (permEmb n σ)) : ℚ) : ℂ) := by
    have key := charValue_eq_spechtModuleCharacter (n + 1) (n + 1) bpμ (permEmb n σ)
    rw [hbpμ] at key; exact key.symm
  -- Relate each right-side term to `charValue`.
  have hRHS : ∀ la ∈ removeSquare μ, spechtModuleCharacter n la σ =
      ((charValue (n + 1) (resBP la) (fullCycleTypePartition σ) : ℚ) : ℂ) := by
    intro la _
    have key := charValue_eq_spechtModuleCharacter (n + 1) n (resBP la) σ
    rw [weightToPartition_resBP] at key; exact key.symm
  -- The rational-coefficient identity: expand the cycle type of the embedding and apply the core.
  have hQ : charValue (n + 1) bpμ (fullCycleTypePartition (permEmb n σ))
      = ∑ la ∈ removeSquare μ, charValue (n + 1) (resBP la) (fullCycleTypePartition σ) := by
    have hdef : charValue (n + 1) bpμ (fullCycleTypePartition (permEmb n σ))
        = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (shiftedExps (n + 1) bpμ.parts))
            ((alternantMatrix (n + 1) (vandermondeExps (n + 1))).det
              * MvPolynomial.psumPart (Fin (n + 1)) ℚ (fullCycleTypePartition (permEmb n σ))) := rfl
    rw [hdef, psumPart_permEmb n σ, ← hbpμ]
    exact res_charValue_sum n bpμ (fullCycleTypePartition σ)
  rw [hLHS, Finset.sum_congr rfl hRHS]
  exact_mod_cast hQ

/-- Problem 5.16.1(b). Branching rule for induction: for `μ ⊢ n`, the induced module
`Ind_{Sₙ}^{Sₙ₊₁} V_μ` decomposes as `⨁_{λ ∈ A(μ)} V_λ`. By Frobenius reciprocity the multiplicity
of `V_λ` (`λ ⊢ n+1`) in the induced module is the reciprocity pairing of `χ_{V_μ}` with the
restriction of `χ_{V_λ}`; this multiplicity is `1` when `λ ∈ A(μ)` (i.e. `μ ⊆ λ`) and `0`
otherwise. -/
theorem ind_spechtModule_multiplicity (n : ℕ) (μ : Nat.Partition n)
    (la : Nat.Partition (n + 1)) :
    branchingPairing n (spechtModuleCharacter n μ)
        (fun σ => spechtModuleCharacter (n + 1) la (permEmb n σ)) =
      if μ.toYoungDiagram ≤ la.toYoungDiagram then 1 else 0 := by
  classical
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) = (Nat.factorial n : ℂ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hne : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  -- Expand the pairing using part (a) (restriction branching) and character orthonormality.
  have hexpand :
      ∑ σ : Equiv.Perm (Fin n),
        spechtModuleCharacter n μ σ *
          spechtModuleCharacter (n + 1) la (permEmb n σ⁻¹)
        = (Nat.factorial n : ℂ) *
            ∑ ρ ∈ removeSquare la, (if μ = ρ then (1 : ℂ) else 0) := by
    -- Apply the restriction rule at `σ⁻¹`, distribute, swap the sums, and use orthonormality.
    have e1 : ∑ σ : Equiv.Perm (Fin n),
        spechtModuleCharacter n μ σ *
          spechtModuleCharacter (n + 1) la (permEmb n σ⁻¹)
        = ∑ σ : Equiv.Perm (Fin n),
            ∑ ρ ∈ removeSquare la,
              spechtModuleCharacter n μ σ * spechtModuleCharacter n ρ σ⁻¹ := by
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [res_spechtModule_character n la σ⁻¹, Finset.mul_sum]
    rw [e1, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [specht_char_inner n μ ρ]
  unfold branchingPairing
  dsimp only
  rw [hexpand, hcard, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  simp only [Finset.sum_ite_eq, removeSquare, Finset.mem_filter, Finset.mem_univ, true_and]

end Etingof

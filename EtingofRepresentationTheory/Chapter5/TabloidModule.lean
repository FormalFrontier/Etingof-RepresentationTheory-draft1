import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_12_1
import EtingofRepresentationTheory.Chapter5.PolytabloidBasis

/-!
# Tabloid Module Infrastructure

This file defines the **tabloid type** and **T-relative column subgroup** needed for
the polytabloid linear independence proof.

A tabloid is a left P_λ-coset of S_n: two permutations give the same tabloid iff their
"row assignments" agree (same entries in each row). The row assignment of a permutation
σ sends entry k to row rowOfPos(σ(k)).

## Main definitions

* `Etingof.TabloidSetoid` — the equivalence relation σ₁ ~ σ₂ iff σ₁ σ₂⁻¹ ∈ P_λ
* `Etingof.Tabloid` — the quotient type (left P_λ cosets)
* `Etingof.sytToTabloid` — maps an SYT to its tabloid
* `Etingof.RelColumnSubgroup` — Q'_T = σ_T Q_λ σ_T⁻¹ (acts on entries via T's columns)

## Main results

* `Etingof.sytToTabloid_injective` — different SYTs give different tabloids
* `Etingof.RelColumnSubgroup_ne_tabloid` — non-identity T-column perms change tabloid

## References

* James, "The Representation Theory of the Symmetric Groups", Chapter 3
-/

namespace Etingof

noncomputable section

variable {n : ℕ} {la : Nat.Partition n}

/-! ### Tabloid equivalence relation -/

/-- Two permutations give the same tabloid (row assignment) iff they differ by a
left multiplication from the row subgroup: σ₁ ~ σ₂ iff σ₁ σ₂⁻¹ ∈ P_λ.

This captures: entry k is in row rowOfPos(σ₁(k)) = rowOfPos(σ₂(k)) for all k. -/
def TabloidSetoid (n : ℕ) (la : Nat.Partition n) :
    Setoid (Equiv.Perm (Fin n)) where
  r σ₁ σ₂ := σ₁ * σ₂⁻¹ ∈ RowSubgroup n la
  iseqv := {
    refl := fun σ => by
      show σ * σ⁻¹ ∈ RowSubgroup n la
      rw [mul_inv_cancel]
      exact (RowSubgroup n la).one_mem
    symm := fun {σ₁ σ₂} h => by
      show σ₂ * σ₁⁻¹ ∈ RowSubgroup n la
      have : σ₂ * σ₁⁻¹ = (σ₁ * σ₂⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv]
      rw [this]
      exact (RowSubgroup n la).inv_mem h
    trans := fun {σ₁ σ₂ σ₃} h₁₂ h₂₃ => by
      show σ₁ * σ₃⁻¹ ∈ RowSubgroup n la
      have key : σ₁ * σ₃⁻¹ = (σ₁ * σ₂⁻¹) * (σ₂ * σ₃⁻¹) := by
        group
      rw [key]
      exact (RowSubgroup n la).mul_mem h₁₂ h₂₃
  }

/-- A tabloid of shape λ is a left P_λ-coset of S_n: an equivalence class of
permutations under the relation σ₁ ~ σ₂ iff σ₁ σ₂⁻¹ ∈ P_λ. -/
def Tabloid (n : ℕ) (la : Nat.Partition n) :=
  Quotient (TabloidSetoid n la)

noncomputable instance : Fintype (Tabloid n la) := by
  haveI : DecidableRel (TabloidSetoid n la).r := Classical.decRel _
  unfold Tabloid
  exact Quotient.fintype (TabloidSetoid n la)

/-- The tabloid of a permutation σ: its left P_λ-coset. -/
def toTabloid (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) :
    Tabloid n la :=
  Quotient.mk (TabloidSetoid n la) σ

/-- Two permutations give the same tabloid iff they differ by a row permutation. -/
theorem toTabloid_eq_iff (σ₁ σ₂ : Equiv.Perm (Fin n)) :
    toTabloid n la σ₁ = toTabloid n la σ₂ ↔ σ₁ * σ₂⁻¹ ∈ RowSubgroup n la :=
  Quotient.eq (r := TabloidSetoid n la)

/-- Two permutations give the same tabloid iff they have the same row assignment:
for all entries k, the row of k is the same. -/
theorem toTabloid_eq_iff_rowAssign (σ₁ σ₂ : Equiv.Perm (Fin n)) :
    toTabloid n la σ₁ = toTabloid n la σ₂ ↔
      ∀ k : Fin n, rowOfPos la.sortedParts (σ₁ k).val =
                    rowOfPos la.sortedParts (σ₂ k).val := by
  rw [toTabloid_eq_iff]
  constructor
  · intro h k
    have hmem := h (σ₂ k)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply,
               Equiv.Perm.inv_apply_self] at hmem
    exact hmem
  · intro h k
    show rowOfPos la.sortedParts ((σ₁ * σ₂⁻¹) k).val = rowOfPos la.sortedParts k.val
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [h (σ₂⁻¹ k)]
    congr 1
    exact congrArg Fin.val (Equiv.apply_symm_apply σ₂ k)

/-! ### SYT to tabloid map -/

/-- The row of entry k in SYT T (via the canonical filling). -/
def sytRowOfEntry (n : ℕ) (la : Nat.Partition n) (T : StandardYoungTableau n la)
    (k : Fin n) : ℕ :=
  rowOfPos la.sortedParts (sytPerm n la T k).val

/-- The tabloid associated to a standard Young tableau T: the left P_λ-coset of σ_T. -/
def sytToTabloid (n : ℕ) (la : Nat.Partition n) (T : StandardYoungTableau n la) :
    Tabloid n la :=
  toTabloid n la (sytPerm n la T)

/-- In a standard tableau, entries in the same row are ordered by their column positions:
if entries k₁ and k₂ are in the same row and k₁ has a strictly smaller column index
(both measured via sytPerm and canonical row/col functions), then k₁ < k₂. -/
private theorem syt_entry_lt_of_col_lt (T : StandardYoungTableau n la) (k₁ k₂ : Fin n)
    (hrow : rowOfPos la.sortedParts (sytPerm n la T k₁).val =
            rowOfPos la.sortedParts (sytPerm n la T k₂).val)
    (hcol : colOfPos la.sortedParts (sytPerm n la T k₁).val <
            colOfPos la.sortedParts (sytPerm n la T k₂).val) :
    k₁ < k₂ := by
  set e := Equiv.ofBijective T.val T.prop.1
  -- Key identity: e.symm k = (canonicalFilling n la) (sytPerm n la T k)
  have hcell : ∀ k : Fin n, e.symm k = (canonicalFilling n la) (sytPerm n la T k) := by
    intro k
    simp only [e, sytPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  -- Same row for the cells
  have hrow' : (e.symm k₁).val.1 = (e.symm k₂).val.1 := by
    rw [hcell k₁, hcell k₂]; exact hrow
  -- k₁'s column < k₂'s column for the cells
  have hcol' : (e.symm k₁).val.2 < (e.symm k₂).val.2 := by
    rw [hcell k₁, hcell k₂]; exact hcol
  -- Apply standard row-increasing property
  have h := T.prop.2.1 (e.symm k₁) (e.symm k₂) hrow' hcol'
  -- T.val (e.symm kᵢ) = kᵢ by definition of e
  rwa [show T.val (e.symm k₁) = k₁ from e.apply_symm_apply k₁,
       show T.val (e.symm k₂) = k₂ from e.apply_symm_apply k₂] at h

/-- Different standard Young tableaux give different tabloids.

Proof: if T₁ and T₂ have the same row assignment for all entries, then within each
row the entries are sorted in the same increasing order (by standardness of both T₁
and T₂), so the fillings are identical. The proof proceeds by strong induction on
entry values: for the smallest entry where the tableaux disagree, one can find a
strictly smaller entry at the same position in the other tableau, contradicting
minimality. -/
theorem sytToTabloid_injective (n : ℕ) (la : Nat.Partition n) :
    Function.Injective (sytToTabloid n la) := by
  intro T₁ T₂ h
  rw [sytToTabloid, sytToTabloid, toTabloid_eq_iff_rowAssign] at h
  apply sytPerm_injective n la
  -- Prove ∀ k, sytPerm T₁ k = sytPerm T₂ k by strong induction on k.val
  suffices ∀ (m : ℕ) (k : Fin n), k.val = m → sytPerm n la T₁ k = sytPerm n la T₂ k by
    exact Equiv.ext (fun k => this k.val k rfl)
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro k hkm
    have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
    -- Suffices: colOfPos agrees (rowOfPos already agrees by h)
    suffices hcol : colOfPos la.sortedParts (sytPerm n la T₁ k).val =
                    colOfPos la.sortedParts (sytPerm n la T₂ k).val by
      exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts
        (sytPerm n la T₁ k).val (sytPerm n la T₂ k).val
        (by omega) (by omega) (h k) hcol)
    -- Prove colOfPos equal by contradiction
    by_contra hcol_ne
    rcases lt_or_gt_of_ne hcol_ne with hlt | hlt
    · -- Case: col(sytPerm T₁ k) < col(sytPerm T₂ k)
      -- k' := (sytPerm T₂)⁻¹(sytPerm T₁ k) is in same row with smaller column in T₂
      set k' := (sytPerm n la T₂).symm (sytPerm n la T₁ k)
      have hk'_eq : sytPerm n la T₂ k' = sytPerm n la T₁ k :=
        (sytPerm n la T₂).apply_symm_apply (sytPerm n la T₁ k)
      -- k' < k by standard property of T₂
      have hk'_lt : k' < k :=
        syt_entry_lt_of_col_lt T₂ k' k
          (by simp only [hk'_eq]; exact h k)
          (by simp only [hk'_eq]; exact hlt)
      -- By IH: sytPerm T₁ k' = sytPerm T₂ k'
      have hih := ih k'.val (by omega) k' rfl
      -- So sytPerm T₁ k' = sytPerm T₂ k' = sytPerm T₁ k, contradicting injectivity
      exact absurd ((sytPerm n la T₁).injective (by rw [hih, hk'_eq])) (ne_of_lt hk'_lt)
    · -- Case: col(sytPerm T₁ k) > col(sytPerm T₂ k) — symmetric with T₁
      set k' := (sytPerm n la T₁).symm (sytPerm n la T₂ k)
      have hk'_eq : sytPerm n la T₁ k' = sytPerm n la T₂ k :=
        (sytPerm n la T₁).apply_symm_apply (sytPerm n la T₂ k)
      have hk'_lt : k' < k :=
        syt_entry_lt_of_col_lt T₁ k' k
          (by simp only [hk'_eq]; exact (h k).symm)
          (by simp only [hk'_eq]; exact hlt)
      have hih := ih k'.val (by omega) k' rfl
      exact absurd ((sytPerm n la T₂).injective (by rw [← hih, hk'_eq])) (ne_of_lt hk'_lt)

/-! ### T-relative column subgroup -/

/-- The column subgroup relative to SYT T: Q'_T = σ_T Q_λ σ_T⁻¹.

An element π ∈ Q'_T acts on ENTRIES, permuting them within the columns of T.
Specifically, π ∈ Q'_T iff π = σ_T q σ_T⁻¹ for some q ∈ Q_λ. -/
def RelColumnSubgroup (n : ℕ) (la : Nat.Partition n)
    (T : StandardYoungTableau n la) : Subgroup (Equiv.Perm (Fin n)) :=
  (ColumnSubgroup n la).map (MulAut.conj (sytPerm n la T)).toMonoidHom

theorem mem_RelColumnSubgroup_iff (T : StandardYoungTableau n la)
    (π : Equiv.Perm (Fin n)) :
    π ∈ RelColumnSubgroup n la T ↔
      ∃ q ∈ ColumnSubgroup n la,
        π = sytPerm n la T * q * (sytPerm n la T)⁻¹ := by
  simp only [RelColumnSubgroup, Subgroup.mem_map, MulAut.conj_apply,
             MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

/-- Key factoring identity: σ_T · q = (σ_T q σ_T⁻¹) · σ_T.
When q ∈ Q_λ, the left factor σ_T q σ_T⁻¹ is in Q'_T. -/
theorem sytPerm_mul_eq_conj_mul (T : StandardYoungTableau n la)
    (q : Equiv.Perm (Fin n)) :
    sytPerm n la T * q =
      (sytPerm n la T * q * (sytPerm n la T)⁻¹) * sytPerm n la T := by
  simp [mul_assoc]

/-- The left factor σ_T q σ_T⁻¹ is in Q'_T when q ∈ Q_λ. -/
theorem conj_mem_RelColumnSubgroup (T : StandardYoungTableau n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n la) :
    sytPerm n la T * q * (sytPerm n la T)⁻¹ ∈ RelColumnSubgroup n la T := by
  rw [mem_RelColumnSubgroup_iff]; exact ⟨q, hq, rfl⟩

/-! ### Tabloid of conjugated permutation -/

/-- The tabloid of σ_T · q is the tabloid of (σ_T q σ_T⁻¹) · σ_T. -/
theorem toTabloid_sytPerm_mul_eq (T : StandardYoungTableau n la)
    (q : Equiv.Perm (Fin n)) :
    toTabloid n la (sytPerm n la T * q) =
      toTabloid n la ((sytPerm n la T * q * (sytPerm n la T)⁻¹) *
                       sytPerm n la T) := by
  congr 1; simp [mul_assoc]

/-- The identity Q'_T element preserves the tabloid of T. -/
theorem toTabloid_id_mul_sytPerm (T : StandardYoungTableau n la) :
    toTabloid n la (1 * sytPerm n la T) = sytToTabloid n la T := by
  simp [sytToTabloid]

/-- A non-identity element of Q'_T changes the tabloid of σ_T.

This is the key combinatorial fact: if π ∈ Q'_T and π ≠ 1, then the tabloid
P_λ · (π · σ_T) ≠ P_λ · σ_T. This holds because π permutes entries within T's
columns, and for a standard tableau, this moves at least one entry to a different row
(entries in a column are in strictly increasing rows). -/
theorem RelColumnSubgroup_ne_tabloid (T : StandardYoungTableau n la)
    (π : Equiv.Perm (Fin n)) (hπ : π ∈ RelColumnSubgroup n la T) (hne : π ≠ 1) :
    toTabloid n la (π * sytPerm n la T) ≠ sytToTabloid n la T := by
  sorry

end

end Etingof

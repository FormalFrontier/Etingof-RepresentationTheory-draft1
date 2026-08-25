/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.RingAuxiliary
import RepresentationTheory.FieldAlgebraProperties
import RepresentationTheory.RingTheory.Idempotent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Data.Matrix.Basis
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic



universe u

namespace RepresentationTheory.RingTheory.ElementProperties




/-- A condition on an element of a ring. -/
def ringElementCondition {A : Type*} [Ring A] (e : A) : Prop :=
  IsIdempotentElem e ∧ Ideal.span {a * e * b | (a : A) (b : A)} = ⊤


/-- Places an element in the Jacobson radical when every left multiple of it is nilpotent. -/
theorem mem_jacobson_of_all_left_multiples_isNilpotent {R : Type*} [Ring R] {c : R}
    (h : ∀ w : R, IsNilpotent (w * c)) : c ∈ Ring.jacobson R := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  intro y
  obtain ⟨b, hb⟩ := (h y).isUnit_one_add.exists_left_inv
  refine ⟨b, ?_⟩
  rw [mul_add, mul_one, ← mul_assoc] at hb
  rw [Ideal.mem_bot, add_comm (b * y * c) b, hb, sub_self]





private lemma matrix_single_generates_ideal (k : Type u) [Field k]
    {n : ℕ} [NeZero n] :
    Ideal.span {a * Matrix.single (0 : Fin n) (0 : Fin n) (1 : k) * b |
      (a : Matrix (Fin n) (Fin n) k) (b : Matrix (Fin n) (Fin n) k)} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  -- Each matrix unit E_{r,s} = E_{r,0} · E_{0,0} · E_{0,s} is in the ideal of E₀₀.
  -- Every matrix x is a k-linear combination of matrix units.
  -- We show each scaled matrix unit c • E_{r,s} is in the ideal.
  -- c • E_{r,s} = (c • E_{r,0}) · E_{0,0} · E_{0,s}
  -- For each (r, s) entry of x, show that x r s • E_{r,s} is in the ideal.
  -- x r s • E_{r,s} = (x r s • E_{r,0}) · E_{0,0} · E_{0,s}, which is in the ideal of E₀₀.
  -- Then x = ∑ r s, x r s • E_{r,s} is in the ideal.
  -- We use that Matrix.single r s c · Matrix.single 0 0 1 · Matrix.single 0 s' 1
  -- follows from Matrix.single_mul_single_same.
  let I := Ideal.span {a * Matrix.single (0 : Fin n) (0 : Fin n) (1 : k) * b |
      (a : Matrix (Fin n) (Fin n) k) (b : Matrix (Fin n) (Fin n) k)}
  suffices h : ∀ (r s : Fin n) (c : k), Matrix.single r s c ∈ I by
    have hx : x = ∑ r, ∑ s, Matrix.single r s (x r s) := by
      ext i j
      simp only [Matrix.sum_apply]
      rw [Finset.sum_eq_single i
        (fun b _ hb => by simp [hb])
        (by simp)]
      rw [Finset.sum_eq_single j
        (fun b _ hb => by simp [hb])
        (by simp)]
      simp
    rw [hx]
    exact Ideal.sum_mem _ fun r _ => Ideal.sum_mem _ fun s _ => h r s _
  intro r s c
  -- Matrix.single r s c = (Matrix.single r 0 c) · E₀₀ · (Matrix.single 0 s 1)
  have : Matrix.single r (0 : Fin n) c * Matrix.single 0 0 1 *
      Matrix.single (0 : Fin n) s 1 = Matrix.single r s c := by
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same]
    simp [mul_one]
  rw [← this]
  exact Ideal.subset_span ⟨_, _, rfl⟩


private lemma pi_matrix_single_generates_ideal (k : Type u) [Field k]
    {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)] :
    let R := ∀ i, Matrix (Fin (d i)) (Fin (d i)) k
    Ideal.span {a * (∑ i, (Pi.single i (Matrix.single 0 0 1) : R)) * b |
      (a : R) (b : R)} = ⊤ := by
  intro R
  rw [eq_top_iff]
  intro x _
  let I := Ideal.span {a * (∑ j, (Pi.single j (Matrix.single 0 0 1) : R)) * b |
      (a : R) (b : R)}
  -- Key: Pi.single i m is in I for all i, m
  suffices hsingle : ∀ (i : Fin n) (m : Matrix (Fin (d i)) (Fin (d i)) k),
      Pi.single i m ∈ I from by
    rw [show x = ∑ i, Pi.single i (x i) from (Finset.univ_sum_single x).symm]
    exact Ideal.sum_mem _ fun i _ => hsingle i (x i)
  intro i m
  -- m is in Ideal.span {a * E₁₁ * b} in Mat_{d_i}(k)
  have hgen := matrix_single_generates_ideal k (n := d i)
  rw [eq_top_iff] at hgen
  have hm := hgen (Submodule.mem_top : m ∈ ⊤)
  -- Key: Pi.single i (a * E₁₁ * b) is in I, for any a, b in block i.
  -- This follows from: Pi.single i a * (∑ j, Pi.single j E₁₁) * Pi.single i b = Pi.single i (a * E₁₁ * b)
  -- by orthogonality of Pi.single at different indices.
  -- Since m ∈ Ideal.span {a * E₁₁ * b | a b} in the matrix ring, Pi.single i m ∈ I.
  -- Key helper: Pi.single i is a ring homomorphism (add, zero, mul)
  have single_add : ∀ (a b : Matrix (Fin (d i)) (Fin (d i)) k),
      Pi.single i (a + b) = (Pi.single i a : R) + Pi.single i b := by
    intro a b; ext t r s
    simp only [Pi.add_apply, Pi.single, Function.update, Pi.zero_apply,
      Matrix.add_apply]
    split
    · next h => subst h; rfl
    · simp
  have single_mul : ∀ (a b : Matrix (Fin (d i)) (Fin (d i)) k),
      Pi.single i (a * b) = (Pi.single i a : R) * Pi.single i b := by
    intro a b; ext t r s
    simp only [Pi.mul_apply, Pi.single, Function.update, Pi.zero_apply,
      Matrix.mul_apply]
    split
    · next h => subst h; rfl
    · simp
  -- Key: Pi.single i (a * E₁₁ * b) = (Pi.single i a) * (∑ j, E₁₁^j) * (Pi.single i b) ∈ I
  have hfgen : ∀ (a b : Matrix (Fin (d i)) (Fin (d i)) k),
      Pi.single i (a * Matrix.single 0 0 1 * b) ∈ I := by
    intro a b
    have hcalc : (Pi.single i a : R) * (∑ j, (Pi.single j (Matrix.single 0 0 (1 : k)) : R)) *
        (Pi.single i b : R) = Pi.single i (a * Matrix.single 0 0 1 * b) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_eq_single i]
      · -- single_mul for three factors
        ext t r s
        simp only [Pi.mul_apply, Pi.single, Function.update, Pi.zero_apply,
          Matrix.mul_apply]
        split
        · next h => subst h; rfl
        · simp
      · intro j _ hj
        have : (Pi.single i a : R) * (Pi.single j (Matrix.single 0 0 (1 : k)) : R) = 0 := by
          ext t r s
          simp only [Pi.mul_apply, Pi.zero_apply, Pi.single, Function.update,
            Matrix.zero_apply, Matrix.mul_apply]
          split
          · next h => subst h; simp [dif_neg (Ne.symm hj)]
          · simp
        simp [this]
      · simp
    rw [← hcalc]
    exact Ideal.subset_span ⟨_, _, rfl⟩
  -- Since m is in the span of {a * E₁₁ * b}, Pi.single i m ∈ I by span induction
  have hpi : ∀ y, y ∈ Ideal.span {a * Matrix.single (0 : Fin (d i)) 0 (1 : k) * b |
      (a : Matrix _ _ k) (b : Matrix _ _ k)} → Pi.single i y ∈ I := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact hfgen a b
    | zero =>
      simp only [Pi.single_zero]
      exact I.zero_mem
    | add x y _ _ ihx ihy =>
      rw [single_add]; exact I.add_mem ihx ihy
    | smul r x _ ihx =>
      rw [show r • x = r * x from rfl, single_mul]
      exact I.mul_mem_left _ ihx
  exact hpi m hm


private lemma isIdempotentElem_sum_orthogonal {R : Type*} [Ring R] {n : ℕ}
    {e : Fin n → R} (he : OrthogonalIdempotents e) :
    IsIdempotentElem (∑ i, e i) := by
  simp only [IsIdempotentElem, Finset.sum_mul, Finset.mul_sum]
  rw [show ∑ i, e i = ∑ i, ∑ j, if i = j then e i else 0 by
    simp [Finset.sum_ite_eq]]
  rw [Finset.sum_comm]
  congr 1; ext j
  congr 1; ext i
  split_ifs with hij
  · subst hij; exact (he.idem _).eq
  · exact he.ortho hij


/-- Constructs an element whose associated membership subtype meets the two displayed conditions. -/
lemma exists_element_with_membership_subtype_conditions
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (e : A) (he : ringElementCondition e),
      @RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k _ (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1)
        (RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1) ∧
      @RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k _ (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1)
        (RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1) := by
  -- Step 1: A is Artinian (finite-dim over a field)
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- Step 2: A is semiprimary (automatic from Artinian)
  haveI : IsSemiprimaryRing A := inferInstance
  -- Step 3: A/J(A) is semisimple and finite-dimensional
  set J := Ring.jacobson A
  haveI : IsSemisimpleRing (A ⧸ J) := IsSemiprimaryRing.isSemisimpleRing
  -- Step 4: Wedderburn-Artin decomposition of A/J(A) ≅ ∏ Mat_{n_i}(k)
  -- The quotient algebra is finite-dimensional over k
  letI : Algebra k (A ⧸ J) := Ideal.Quotient.algebra k
  haveI : Module.Finite k (A ⧸ J) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ k J).toLinearMap (Ideal.Quotient.mkₐ_surjective k J)
  obtain ⟨numBlocks, blockSize, hne, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ J)
  -- Step 5: Extract orthogonal idempotents E₁₁ in each block of the product
  -- In ∏ Mat_{n_i}(k), define ēᵢ = Pi.single i (Matrix.single 0 0 1)
  let ē : Fin numBlocks → (∀ i, Matrix (Fin (blockSize i)) (Fin (blockSize i)) k) :=
    fun i => Pi.single i (Matrix.single 0 0 1)
  -- These are orthogonal idempotents in the product
  have hē_orth : OrthogonalIdempotents ē := by
    constructor
    · intro i
      change ē i * ē i = ē i
      simp only [ē, ← Pi.single_mul]
      congr 1
      rw [Matrix.single_mul_single_same]
      simp
    · intro i j hij
      change ē i * ē j = 0
      simp only [ē]
      ext t : 1
      simp only [Pi.mul_apply, Pi.zero_apply]
      by_cases hi : i = t
      · subst hi
        simp [hij]
      · simp [hi]
  -- Transport to A/J(A) via the isomorphism
  let ē_AJ : Fin numBlocks → (A ⧸ J) := fun i => φ.symm (ē i)
  have hē_AJ_orth : OrthogonalIdempotents ē_AJ := by
    constructor
    · intro i
      change ē_AJ i * ē_AJ i = ē_AJ i
      simp only [ē_AJ, ← map_mul, hē_orth.idem i |>.eq]
    · intro i j hij
      change ē_AJ i * ē_AJ j = 0
      simp only [ē_AJ, ← map_mul, hē_orth.ortho hij, map_zero]
  -- Step 6: Lift to A using nilpotency of J
  have hJ_nil : IsNilpotent J := IsSemiprimaryRing.isNilpotent
  have hker_nil : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk J), IsNilpotent x := by
    intro x hx
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨n, hn⟩ := hJ_nil
    exact ⟨n, Ideal.pow_eq_zero_of_mem hn le_rfl hx⟩
  obtain ⟨e_lifted, he_orth, he_comp⟩ := OrthogonalIdempotents.lift_of_isNilpotent_ker
    (Ideal.Quotient.mk J) hker_nil hē_AJ_orth
    (fun i => Ideal.Quotient.mk_surjective (ē_AJ i))
  -- Step 7: Set e = ∑ e_lifted i
  let e := ∑ i, e_lifted i
  have he_idem : IsIdempotentElem e := isIdempotentElem_sum_orthogonal he_orth
  -- Step 8: Show e is full (AeA = A) and eAe is basic
  -- Fullness: In A/J, the images ē_AJ i generate A/J as a two-sided ideal.
  -- Since J is nilpotent, this lifts to fullness in A.
  -- Basicness: eAe/rad(eAe) ≅ k^n (one copy per block), so all simple eAe-modules
  -- are 1-dimensional.
  -- Step 8a: Show that in A/J, the two-sided ideal generated by ē = ∑ ēᵢ is all of A/J.
  have he_quotient_image : ∀ i, Ideal.Quotient.mk J (e_lifted i) = ē_AJ i :=
    fun i => congr_fun he_comp i
  have he_image : Ideal.Quotient.mk J e = ∑ i, ē_AJ i := by
    simp only [e, map_sum, he_quotient_image]
  -- Key fact: in ∏ Mat_{n_i}(k), the two-sided ideal generated by ∑ E₁₁^(i) is the
  -- whole product because E_{rs}^(i) = E_{r0}^(i) · E₀₀^(i) · E_{0s}^(i).
  -- Therefore in A/J, the image of e generates A/J as a two-sided ideal.
  -- This means ∃ aₖ, bₖ such that ∑ aₖ · ē · bₖ = 1 in A/J,
  -- i.e., 1 - ∑ aₖ · e · bₖ ∈ J.
  -- Since J = Ring.jacobson A ⊆ jacobson ⊥, this element is in the Jacobson radical,
  -- so ∑ aₖ · e · bₖ is a unit. Since AeA contains this unit, AeA = ⊤.
  have he_full : ringElementCondition e := by
    constructor
    · exact he_idem
    · -- Strategy: Show 1 ∈ Ideal.span {a * e * b | a b}
      -- Step A: In ∏ Mat_{n_i}(k), ∑ E₁₁ generates the whole ring
      have hpi := pi_matrix_single_generates_ideal k blockSize
      -- Step B: Transport through φ to A/J
      let ē_sum := ∑ i, ē_AJ i
      -- Key: φ.symm (∑ E₁₁) = ē_sum
      have hē_sum_eq : φ.symm (∑ i,
          (Pi.single i (Matrix.single 0 0 1) :
          (∀ i, Matrix (Fin (blockSize i)) (Fin (blockSize i)) k))) =
          ē_sum := by
        simp only [ē_sum, map_sum, ē_AJ, ē]
      have hAJ_gen : Ideal.span {a * ē_sum * b |
          (a : A ⧸ J) (b : A ⧸ J)} = ⊤ := by
        rw [eq_top_iff]; intro x _
        -- Pull back through φ.symm from the product ideal
        suffices key : ∀ y, y ∈ Ideal.span
            {a * (∑ i, (Pi.single i (Matrix.single 0 0 1) :
              (∀ i, Matrix (Fin (blockSize i)) (Fin (blockSize i)) k))) *
              b | (a : ∀ i, Matrix _ _ k) (b : ∀ i, Matrix _ _ k)} →
            φ.symm y ∈ Ideal.span
              {a * ē_sum * b | (a : A ⧸ J) (b : A ⧸ J)} by
          have := key (φ x) (hpi ▸ Submodule.mem_top)
          rwa [φ.symm_apply_apply] at this
        intro y hy
        induction hy using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨a, b, rfl⟩ := hz
          rw [map_mul, map_mul, hē_sum_eq]
          exact Ideal.subset_span ⟨φ.symm a, φ.symm b, rfl⟩
        | zero => simp
        | add a b _ _ iha ihb => rw [map_add]; exact Ideal.add_mem _ iha ihb
        | smul r a _ iha =>
          change φ.symm (r * a) ∈ _
          rw [map_mul]; exact Ideal.mul_mem_left _ _ iha
      -- Step C: The image of e in A/J is ē_sum
      -- So AeA maps onto A/J, meaning AeA + J = A
      -- i.e., 1 ∈ AeA + J
      let I := Ideal.span {a * e * b | (a : A) (b : A)}
      -- The quotient image of I contains the quotient image of e
      have hI_image : ∀ (a b : A ⧸ J),
          a * ē_sum * b ∈ Ideal.map (Ideal.Quotient.mk J) I := by
        intro a b
        obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
        have : Ideal.Quotient.mk J a' * ē_sum * Ideal.Quotient.mk J b' =
            Ideal.Quotient.mk J (a' * e * b') := by
          rw [show ē_sum = Ideal.Quotient.mk J e from he_image.symm]
          simp [map_mul]
        rw [this]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a', b', rfl⟩)
      have hI_map_top : Ideal.map (Ideal.Quotient.mk J) I = ⊤ := by
        rw [eq_top_iff, ← hAJ_gen]
        exact Submodule.span_le.mpr fun _ ⟨a, b, h⟩ => h ▸ hI_image a b
      -- Step D: I ⊔ J = ⊤
      have hIJ_top : I ⊔ J = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [← Ideal.mem_quotient_iff_mem_sup]
        rw [hI_map_top]
        exact Submodule.mem_top
      -- Step E: 1 = x + j with x ∈ I, j ∈ J, so x = 1 - j and 1 - x ∈ J
      have h1_mem : (1 : A) ∈ I ⊔ J := hIJ_top ▸ Submodule.mem_top
      rw [Submodule.mem_sup] at h1_mem
      obtain ⟨x, hxI, j, hjJ, hxj⟩ := h1_mem
      -- x = 1 - j, and j ∈ J which is nilpotent, so j is nilpotent, so x is a unit
      have hx_unit : IsUnit x := by
        have hx_eq : x = 1 - j := by
          have h := hxj; rw [show x + j = 1 ↔ x = 1 - j from
            ⟨fun h => by rw [← h, add_sub_cancel_right],
             fun h => by rw [h, sub_add_cancel]⟩] at h; exact h
        rw [hx_eq]
        exact IsNilpotent.isUnit_one_sub
          (hker_nil j (by rwa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]))
      exact Ideal.eq_top_of_isUnit_mem I hxI hx_unit
  have he_basic : (@RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k _ (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e)
      (RepresentationTheory.RingTheory.Idempotent.submodule.ring he_full.1) (RepresentationTheory.RingTheory.Idempotent.submodule.algebra he_full.1)) ∧
      (@RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k _ (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e)
      (RepresentationTheory.RingTheory.Idempotent.submodule.ring he_full.1) (RepresentationTheory.RingTheory.Idempotent.submodule.algebra he_full.1)) := by
    letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he_full.1
    letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he_full.1
    -- === Part A: φ(q(e)) = constant function E₁₁ ===
    have hφqe : φ (Ideal.Quotient.mk J e) =
        fun i => Matrix.single (0 : Fin (blockSize i)) 0 1 := by
      rw [he_image, map_sum]
      simp only [ē_AJ, ē, AlgEquiv.apply_symm_apply]
      exact Finset.univ_sum_single _
    -- === Part B: For x ∈ eAe, φ(q(x)) at each block is a scalar matrix ===
    have corner_scalar : ∀ (x : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (i : Fin numBlocks),
        (φ (Ideal.Quotient.mk J (x : A))) i =
          Matrix.single 0 0 ((φ (Ideal.Quotient.mk J (x : A))) i 0 0) := by
      intro ⟨xval, hx⟩ i
      obtain ⟨a, ha⟩ := (RepresentationTheory.RingTheory.Idempotent.mem_sandwichSubmodule_iff e xval).mp hx
      have hq : Ideal.Quotient.mk J xval =
          Ideal.Quotient.mk J e * Ideal.Quotient.mk J a * Ideal.Quotient.mk J e := by
        simp only [← map_mul, ha]
      -- LHS and RHS both rewrite using hq, map_mul, hφqe
      -- Then E₁₁ * M * E₁₁ = single 0 0 (M 0 0) by single_mul_mul_single
      conv_lhs => rw [hq, map_mul, map_mul, hφqe]
      conv_rhs => rw [hq, map_mul, map_mul, hφqe]
      simp only [Pi.mul_apply, Matrix.single_mul_mul_single, one_mul, mul_one,
        Matrix.single_apply, ↓reduceIte, and_self]
    -- === Part C: Ring hom π : eAe → Fin numBlocks → k ===
    let π : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e →+* (Fin numBlocks → k) :=
    { toFun := fun x i => (φ (Ideal.Quotient.mk J (x : A))) i 0 0
      map_one' := by
        ext i; change (φ (Ideal.Quotient.mk J e)) i 0 0 = 1
        rw [hφqe]; simp
      map_mul' := fun x y => by
        ext i; simp only [Pi.mul_apply]
        change (φ (Ideal.Quotient.mk J ((x : A) * (y : A)))) i 0 0 =
          (φ (Ideal.Quotient.mk J (x : A))) i 0 0 *
          (φ (Ideal.Quotient.mk J (y : A))) i 0 0
        have h1 : Ideal.Quotient.mk J ((x : A) * (y : A)) =
            Ideal.Quotient.mk J (x : A) * Ideal.Quotient.mk J (y : A) := map_mul _ _ _
        have h2 : φ (Ideal.Quotient.mk J (x : A) * Ideal.Quotient.mk J (y : A)) =
            φ (Ideal.Quotient.mk J (x : A)) * φ (Ideal.Quotient.mk J (y : A)) := map_mul _ _ _
        rw [h1, h2, Pi.mul_apply, corner_scalar x i, corner_scalar y i,
          Matrix.single_mul_single_same, Matrix.single_apply, Matrix.single_apply]
        simp
      map_zero' := by ext i; simp [map_zero, Matrix.zero_apply]
      map_add' := fun x y => by ext i; simp [map_add, Matrix.add_apply] }
    -- === Part D: ker π ⊆ J (elements mapping to 0 in A/J) ===
    have hπ_ker_sub_J : ∀ (x : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e),
        x ∈ RingHom.ker π → (x : A) ∈ J := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hblock : ∀ i, (φ (Ideal.Quotient.mk J (x : A))) i = 0 := by
        intro i; rw [corner_scalar x i]
        have hi : (φ (Ideal.Quotient.mk J (x : A))) i 0 0 = 0 := congr_fun hx i
        rw [hi]; ext r s; simp [Matrix.single_apply]
      have hq0 : Ideal.Quotient.mk J (x : A) = 0 :=
        φ.injective (funext hblock |>.trans (map_zero φ).symm)
      rwa [Ideal.Quotient.eq_zero_iff_mem] at hq0
    -- === Part E: elements of ker π are nilpotent in RepresentationTheory.RingTheory.Idempotent.submodule ===
    have hπ_ker_nilpotent_elem : ∀ (x : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e),
        x ∈ RingHom.ker π → IsNilpotent x := by
      intro x hx
      have hxJ := hπ_ker_sub_J x hx
      obtain ⟨n, hn⟩ := hJ_nil
      -- Use n+1 because (x^0).val = e ≠ 1 = x.val^0 in RepresentationTheory.RingTheory.Idempotent.submodule
      refine ⟨n + 1, ?_⟩
      have hxn : (x : A) ^ n = 0 := Ideal.pow_eq_zero_of_mem hn le_rfl hxJ
      -- For m ≥ 1: (x ^ m : RepresentationTheory.RingTheory.Idempotent.submodule).val = x.val ^ m (since mul in RepresentationTheory.RingTheory.Idempotent.submodule = mul in A)
      have corner_pow : ∀ m, (x ^ (m + 1) : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e).val =
          (x : A) ^ (m + 1) := by
        intro m; induction m with
        | zero => simp [pow_one]
        | succ m ih =>
          have step : (x ^ (m + 2) : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e).val =
              (x ^ (m + 1) : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e).val * (x : A) := by
            change (x ^ (m + 1) * x : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e).val = _; rfl
          rw [step, ih, ← pow_succ]
      have hval : (x ^ (n + 1) : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e).val = (0 : A) :=
        (corner_pow n).trans (by rw [pow_succ, hxn, zero_mul])
      exact Subtype.ext hval
    -- For any x y, the commutator xy - yx maps to 0 under the ring hom π into the
    -- commutative ring `∏ k`, so it lies in `ker π`, a nil two-sided ideal, hence
    -- in the Jacobson radical.  Therefore the radical quotient is commutative.
    have hfaithful : @RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k _ (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e)
        (RepresentationTheory.RingTheory.Idempotent.submodule.ring he_full.1) (RepresentationTheory.RingTheory.Idempotent.submodule.algebra he_full.1) := by
      intro xq yq
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xq
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yq
      rw [← map_mul, ← map_mul, Ideal.Quotient.eq]
      apply mem_jacobson_of_all_left_multiples_isNilpotent
      intro w
      apply hπ_ker_nilpotent_elem
      rw [RingHom.mem_ker, map_mul]
      have hc : π (x * y - y * x) = 0 := by
        rw [map_sub, map_mul, map_mul, mul_comm (π x) (π y), sub_self]
      rw [hc, mul_zero]
    refine ⟨?_, hfaithful⟩
    -- === Part F: ker π annihilates simple modules ===
    -- If a ∈ ker π and a•m ≠ 0, then by simplicity m = (ba)•m for some b,
    -- so m = (ba)^N•m = 0 (ba is nilpotent in ker π), contradiction.
    intro M _instACG _instMod _instSimple _instModk _instST
    have hker_ann : ∀ (a : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e), a ∈ RingHom.ker π →
        ∀ (m : M), a • m = 0 := by
      intro a ha m
      by_contra h_ne
      -- a•m ≠ 0, so span = ⊤ by simplicity
      have hspan : Submodule.span (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) {a • m} = ⊤ := by
        rcases IsSimpleOrder.eq_bot_or_eq_top
          (Submodule.span (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) {a • m}) with h | h
        · have hmem : a • m ∈ (⊥ : Submodule (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) M) :=
            h ▸ Submodule.subset_span rfl
          rw [Submodule.mem_bot] at hmem; exact absurd hmem h_ne
        · exact h
      -- m ∈ span {a • m}, so m = b • (a • m) for some b
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
        (hspan ▸ (Submodule.mem_top : m ∈ ⊤))
      -- c = b * a ∈ ker π (ker is a left ideal)
      have hc_mem : b * a ∈ RingHom.ker π := by
        simp only [RingHom.mem_ker, map_mul, RingHom.mem_ker.mp ha, mul_zero]
      -- c is nilpotent
      obtain ⟨N, hN⟩ := hπ_ker_nilpotent_elem (b * a) hc_mem
      -- m = c • m implies m = c^n • m for all n, then specialize to N
      have hm_eq : (b * a) • m = m := by rw [mul_smul]; exact hb
      have hpow : ∀ n, m = (b * a) ^ n • m := by
        intro n; induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, mul_smul, hm_eq]; exact ih
      have := hpow N; rw [hN, zero_smul] at this
      exact h_ne (by rw [this, smul_zero])
    -- === Part G: finrank k M = 1 ===
    -- Step G.1: M is finite-dimensional over k.
    -- RepresentationTheory.RingTheory.Idempotent.submodule is f.d. over k, and M is a cyclic quotient (simple module).
    haveI : Module.Finite k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.moduleFinite
    haveI : Nontrivial M := IsSimpleModule.nontrivial (R := RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (M := M)
    obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
    -- The map r ↦ r • m₀ is a surjective k-linear map RepresentationTheory.RingTheory.Idempotent.submodule → M
    have hspan_top : Submodule.span (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) {m₀} = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left (by
        intro h; apply hm₀
        have : m₀ ∈ (⊥ : Submodule (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) M) :=
          h ▸ Submodule.subset_span rfl
        rwa [Submodule.mem_bot] at this)
    -- Every m ∈ M is r • m₀ for some r
    have hsurj : ∀ m : M, ∃ r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e, r • m₀ = m := by
      intro m
      have hm : m ∈ (⊤ : Submodule (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) M) := Submodule.mem_top
      rw [← hspan_top] at hm
      exact Submodule.mem_span_singleton.mp hm
    haveI : FiniteDimensional k M := by
      let f : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e →ₗ[k] M :=
        { toFun := fun r => r • m₀
          map_add' := fun x y => add_smul x y m₀
          map_smul' := fun c x => by
            simp only [RingHom.id_apply]
            rw [← smul_assoc] }
      exact Module.Finite.of_surjective f (fun m => by obtain ⟨r, hr⟩ := hsurj m; exact ⟨r, hr⟩)
    -- Step G.2: For each r ∈ RepresentationTheory.RingTheory.Idempotent.submodule, m ↦ r • m is RepresentationTheory.RingTheory.Idempotent.submodule-linear.
    -- This uses: ker π annihilates M, and π maps to commutative k^numBlocks.
    have hcomm_act : ∀ (r s : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (m : M),
        r • (s • m) = s • (r • m) := by
      intro r s m
      -- (rs - sr) ∈ ker π because π maps to a commutative ring
      have hcomm : r * s - s * r ∈ RingHom.ker π := by
        rw [RingHom.mem_ker, map_sub, map_mul, map_mul, sub_eq_zero]
        ext i; exact mul_comm _ _
      -- ker π annihilates M
      have := hker_ann (r * s - s * r) hcomm m
      rw [sub_smul, mul_smul, mul_smul, sub_eq_zero] at this
      exact this
    -- Step G.3: By Schur (alg closed), every RepresentationTheory.RingTheory.Idempotent.submodule-endo of M is a k-scalar.
    have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
        (A := RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (V := M)
    -- For each r, define the RepresentationTheory.RingTheory.Idempotent.submodule-linear map m ↦ r • m
    have hscalar : ∀ r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e, ∃ c : k, ∀ m : M, r • m = c • m := by
      intro r
      let φ_r : M →ₗ[RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e] M :=
        { toFun := fun m => r • m
          map_add' := fun x y => smul_add r x y
          map_smul' := fun s m => by simp only [RingHom.id_apply]; exact hcomm_act r s m }
      obtain ⟨c, hc⟩ := hschur.2 φ_r
      exact ⟨c, fun m => by
        have := LinearMap.ext_iff.mp hc m
        simp [Module.algebraMap_end_apply] at this
        exact this.symm⟩
    -- Step G.4: Every m is c • m₀, so finrank k M = 1.
    have hone_dim : ∀ m : M, ∃ c : k, m = c • m₀ := by
      intro m
      obtain ⟨r, hr⟩ := hsurj m
      obtain ⟨c, hc⟩ := hscalar r
      exact ⟨c, by rw [← hr, hc]⟩
    rw [finrank_eq_one_iff_of_nonzero' m₀ hm₀]
    exact fun m => let ⟨c, hc⟩ := hone_dim m; ⟨c, hc.symm⟩
  exact ⟨e, he_full, he_basic⟩



variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]


private def eCorner {e : A} (_he : IsIdempotentElem e) (M : Type u)
    [AddCommGroup M] [Module A M] : AddSubgroup M where
  carrier := {m | e • m = m}
  zero_mem' := smul_zero e
  add_mem' {a b} ha hb := by change e • (a + b) = a + b; rw [smul_add, ha, hb]
  neg_mem' {a} ha := by change e • (-a) = -a; rw [smul_neg, ha]


private lemma eCorner_prop {e : A} {he : IsIdempotentElem e} {M : Type u}
    [AddCommGroup M] [Module A M] (m : eCorner he M) : e • (m : M) = (m : M) :=
  m.prop


private lemma eCorner_smul_mem {e : A} (he : IsIdempotentElem e) {M : Type u}
    [AddCommGroup M] [Module A M] (r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (m : eCorner he M) :
    e • ((r : A) • (m : M)) = (r : A) • (m : M) := by
  rw [← mul_smul, RepresentationTheory.RingTheory.Idempotent.left_mul_eq_of_mem_sandwichSubmodule he r.prop]


private noncomputable def eCornerModule {e : A} (he : IsIdempotentElem e) (M : Type u)
    [AddCommGroup M] [Module A M] :
    letI := RepresentationTheory.RingTheory.Idempotent.submodule.ring (k := k) he
    Module (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (eCorner he M) :=
  letI := RepresentationTheory.RingTheory.Idempotent.submodule.ring (k := k) he
  { smul := fun r m => ⟨(r : A) • (m : M), eCorner_smul_mem he r m⟩
    one_smul := fun m => Subtype.ext (show e • (m : M) = (m : M) from m.prop)
    mul_smul := fun r s m => Subtype.ext (mul_smul (r : A) (s : A) (m : M))
    smul_add := fun r m₁ m₂ => Subtype.ext (smul_add (r : A) (m₁ : M) (m₂ : M))
    smul_zero := fun r => Subtype.ext (smul_zero (r : A))
    add_smul := fun r s m => Subtype.ext (add_smul (r : A) (s : A) (m : M))
    zero_smul := fun m => Subtype.ext (zero_smul A (m : M)) }


private lemma eCorner_map_mem {e : A} (he : IsIdempotentElem e)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (m : eCorner he M) : e • f (m : M) = f (m : M) := by
  rw [← f.map_smul, eCorner_prop m]

open CategoryTheory




private noncomputable def cornerFunctor {e : A} (he : IsIdempotentElem e) :
    letI := RepresentationTheory.RingTheory.Idempotent.submodule.ring (k := k) he
    ModuleCat.{u} A ⥤ ModuleCat.{u} (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) :=
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he
  { obj := fun M =>
      letI := eCornerModule (k := k) he M
      ModuleCat.of (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (eCorner he M)
    map := fun {M N} f =>
      letI := eCornerModule (k := k) he M
      letI := eCornerModule (k := k) he N
      ModuleCat.ofHom
        { toFun := fun m => ⟨f.hom m.val, eCorner_map_mem he f.hom m⟩
          map_add' := fun m₁ m₂ => Subtype.ext (map_add f.hom m₁.val m₂.val)
          map_smul' := fun r m => Subtype.ext (by
            change f.hom ((r : A) • m.val) = (r : A) • f.hom m.val
            exact f.hom.map_smul r.val m.val) }
    map_id := fun M => by ext; rfl
    map_comp := fun f g => by ext; rfl }




private lemma one_mem_fullIdempotent_span {e : A} (he : ringElementCondition e) :
    (1 : A) ∈ Ideal.span {a * e * b | (a : A) (b : A)} := by
  rw [he.2]; exact Submodule.mem_top


private lemma eCorner_spans {e : A} (he : ringElementCondition e)
    {M : Type u} [AddCommGroup M] [Module A M] (m : M) :
    m ∈ Submodule.span A (Set.range (fun n : M => e • n)) := by
  rw [show m = (1 : A) • m from (one_smul A m).symm]
  have h1 : (1 : A) ∈ Ideal.span {x | ∃ c d : A, c * e * d = x} := by
    rw [he.2]; exact Submodule.mem_top
  generalize (1 : A) = a at h1 ⊢
  induction h1 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, d, rfl⟩ := hx
    rw [mul_smul, mul_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨d • m, rfl⟩)
  | zero => simp
  | add x y _ _ ihx ihy => rw [add_smul]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ihx => rw [smul_assoc]; exact Submodule.smul_mem _ r ihx


private lemma cornerFunctor_faithful {e : A} (he : ringElementCondition e) :
    letI := RepresentationTheory.RingTheory.Idempotent.submodule.ring (k := k) he.1
    (cornerFunctor (k := k) he.1).Faithful := by
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1
  constructor
  intro M N f g hfg
  ext m
  -- m is in the A-span of {e • n | n ∈ M} by fullness
  have hm := eCorner_spans he m
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    have hmem : e • (e • n) = e • n := by rw [← mul_smul, he.1.eq]
    exact congr_arg (fun φ => (φ ⟨e • n, hmem⟩ : eCorner he.1 N).val)
      (ModuleCat.hom_ext_iff.mp hfg)
  | zero => simp [map_zero]
  | add x y _ _ ihx ihy => simp [map_add, ihx, ihy]
  | smul a x _ ihx => simp [map_smul, ihx]




private lemma eCorner_smul_of_idem {e : A} (he : IsIdempotentElem e)
    {M : Type u} [AddCommGroup M] [Module A M] (m : M) :
    e • (e • m) = e • m := by
  rw [← mul_smul, he.eq]


private def toECorner {e : A} (he : IsIdempotentElem e)
    {M : Type u} [AddCommGroup M] [Module A M] (m : M) :
    eCorner he M :=
  ⟨e • m, eCorner_smul_of_idem he m⟩


private lemma toECorner_add {e : A} (he : IsIdempotentElem e)
    {M : Type u} [AddCommGroup M] [Module A M] (m₁ m₂ : M) :
    toECorner he (m₁ + m₂) = toECorner he m₁ + toECorner he m₂ :=
  Subtype.ext (smul_add e m₁ m₂)


private lemma toECorner_of_mem {e : A} {he : IsIdempotentElem e}
    {M : Type u} [AddCommGroup M] [Module A M] (m : eCorner he M) :
    toECorner he (m : M) = m :=
  Subtype.ext (eCorner_prop m)


private lemma toECorner_cornerRing_smul {e : A} (he : IsIdempotentElem e)
    {M : Type u} [AddCommGroup M] [Module A M]
    (r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (m : M) :
    toECorner he ((r : A) • m) =
      letI := eCornerModule (k := k) he M
      r • toECorner he m := by
  apply Subtype.ext
  change e • ((r : A) • m) = (r : A) • (e • m)
  rw [← mul_smul, ← mul_smul]
  congr 1
  rw [RepresentationTheory.RingTheory.Idempotent.left_mul_eq_of_mem_sandwichSubmodule he r.prop, RepresentationTheory.RingTheory.Idempotent.right_mul_eq_of_mem_sandwichSubmodule he r.prop]



private lemma cornerFunctor_full {e : A} (he : ringElementCondition e) :
    letI := RepresentationTheory.RingTheory.Idempotent.submodule.ring (k := k) he.1
    (cornerFunctor (k := k) he.1).Full := by
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1
  constructor
  intro M N φ
  -- Extract finite decomposition: 1 = Σ σ(a,b) • (a * e * b) from fullness
  have hspan : (1 : A) ∈ Submodule.span A (Set.range (fun p : A × A => p.1 * e * p.2)) := by
    suffices h : Submodule.span A (Set.range (fun p : A × A => p.1 * e * p.2)) = ⊤ from
      h ▸ Submodule.mem_top
    have : Set.range (fun p : A × A => p.1 * e * p.2) =
        {x | ∃ a b : A, a * e * b = x} := by
      ext x; constructor
      · rintro ⟨⟨a, b⟩, rfl⟩; exact ⟨a, b, rfl⟩
      · rintro ⟨a, b, rfl⟩; exact ⟨⟨a, b⟩, rfl⟩
    rw [this]; exact he.2
  obtain ⟨σ, hσ⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  -- hσ : σ.sum (fun p c => c • (p.1 * e * p.2)) = 1
  -- Note: Finsupp.sum σ g = ∑ p ∈ σ.support, g p (σ p)
  -- So hσ says: ∑ p ∈ σ.support, σ p • (p.1 * e * p.2) = 1
  -- i.e., ∑ p, (σ p * p.1) * e * p.2 = 1
  letI := eCornerModule (k := k) he.1 M
  letI := eCornerModule (k := k) he.1 N
  -- Define the lift: f(m) = ∑ p, (σ p * p.1) • ↑(φ (toECorner he.1 (p.2 • m)))
  let liftFun : M → N := fun m =>
    ∑ p ∈ σ.support, (σ p * p.1) • (φ (toECorner he.1 (p.2 • m)) : eCorner he.1 N).val
  have lift_add : ∀ m₁ m₂ : M, liftFun (m₁ + m₂) = liftFun m₁ + liftFun m₂ := by
    intro m₁ m₂
    change (∑ p ∈ σ.support, (σ p * p.1) •
        (φ (toECorner he.1 (p.2 • (m₁ + m₂))) : eCorner he.1 N).val) =
      (∑ p ∈ σ.support, (σ p * p.1) • (φ (toECorner he.1 (p.2 • m₁)) : eCorner he.1 N).val) +
      (∑ p ∈ σ.support, (σ p * p.1) • (φ (toECorner he.1 (p.2 • m₂)) : eCorner he.1 N).val)
    rw [← Finset.sum_add_distrib]
    congr 1; ext p
    have hφ : ((ConcreteCategory.hom φ)
        (toECorner he.1 (p.2 • m₁) + toECorner he.1 (p.2 • m₂)) :
        eCorner he.1 N).val =
        ((ConcreteCategory.hom φ) (toECorner he.1 (p.2 • m₁)) :
          eCorner he.1 N).val +
        ((ConcreteCategory.hom φ) (toECorner he.1 (p.2 • m₂)) :
          eCorner he.1 N).val := by
      rw [← AddSubgroup.coe_add]
      exact congrArg (fun x : eCorner he.1 N => (x : N))
        ((ConcreteCategory.hom φ).map_add (toECorner he.1 (p.2 • m₁))
          (toECorner he.1 (p.2 • m₂)))
    rw [smul_add, toECorner_add, hφ, smul_add]
  -- Key identity: ∑ σ p * (p.1 * e * p.2) = 1
  have hσ1 : ∑ p ∈ σ.support, σ p * (p.1 * e * p.2) = 1 := by
    have := hσ; simp only [Finsupp.sum, smul_eq_mul] at this; exact this
  -- Coercion helper: (r •_{eAe} x : eCorner).val = (r : A) • (x : N)
  have coe_smul : ∀ (r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (x : eCorner he.1 N),
      ((r • x : eCorner he.1 N) : N) = (r : A) • (x : N) := fun _ _ => rfl
  have coe_map_smul : ∀ (r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (x : eCorner he.1 M),
      (φ (r • x) : eCorner he.1 N).val =
        (r : A) • (φ x : eCorner he.1 N).val := by
    intro r x
    have hmap : (φ (r • x) : eCorner he.1 N).val =
        (r • (φ x : eCorner he.1 N) : eCorner he.1 N).val :=
      congrArg (fun y : eCorner he.1 N => (y : N))
        ((ConcreteCategory.hom φ).map_smul r x)
    rw [hmap]
    exact coe_smul r ((ConcreteCategory.hom φ) x)
  -- Helper for the generator case: liftFun on e • n
  have lift_eCorner : ∀ (n : M),
      liftFun (e • n) = (φ (toECorner he.1 n) : eCorner he.1 N).val := by
    intro n
    change ∑ p ∈ σ.support, (σ p * p.1) •
        (φ (toECorner he.1 (p.2 • (e • n))) : eCorner he.1 N).val =
      (φ (toECorner he.1 n) : eCorner he.1 N).val
    -- toECorner(p.2 • (e • n)) = ⟨e * p.2 * e • (e • n), ...⟩ = (e*p.2*e) •_{eAe} toECorner(n)
    -- since e • (p.2 • (e • n)) = (e * p.2 * e) • n [using e²=e twice]
    -- and toECorner(n) = ⟨e • n, ...⟩
    have h1 : ∀ p : A × A, toECorner he.1 (p.2 • (e • n)) =
        (⟨e * p.2 * e, ⟨p.2, rfl⟩⟩ : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) • toECorner he.1 n := by
      intro p; apply Subtype.ext
      change e • (p.2 • (e • n)) = (e * p.2 * e) • (e • n)
      rw [mul_smul, mul_smul, eCorner_smul_of_idem he.1 n]
    rw [show ∑ p ∈ σ.support, (σ p * p.1) •
        (φ (toECorner he.1 (p.2 • (e • n))) : eCorner he.1 N).val =
        ∑ p ∈ σ.support, (σ p * p.1 * (e * p.2 * e)) •
          (φ (toECorner he.1 n) : eCorner he.1 N).val by
      apply Finset.sum_congr rfl
      intro p hp
      rw [h1 p, coe_map_smul, ← mul_smul], ← Finset.sum_smul]
    have hsum_e : ∑ p ∈ σ.support, σ p * p.1 * (e * p.2 * e) = e := by
      have : ∀ p ∈ σ.support, σ p * p.1 * (e * p.2 * e) =
          σ p * (p.1 * e * p.2) * e := fun p _ => by simp only [mul_assoc]
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hσ1, one_mul]
    rw [hsum_e]
    exact (φ (toECorner he.1 n)).prop
  have lift_smul : ∀ (r : A) (m : M), liftFun (r • m) = r • liftFun m := by
    -- Quantify r inside the induction so the smul case has IH for all r
    suffices key : ∀ m, m ∈ Submodule.span A (Set.range (fun n : M => e • n)) →
        ∀ r : A, liftFun (r • m) = r • liftFun m from
      fun r m => key m (eCorner_spans he m) r
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      intro r
      -- Goal: liftFun(r • (e • n)) = r • liftFun(e • n)
      rw [← mul_smul, lift_eCorner]
      -- Goal: liftFun((r * e) • n) = r • φ(toECorner n).val
      -- Expand liftFun from definition
      change ∑ p ∈ σ.support, (σ p * p.1) •
          (φ (toECorner he.1 (p.2 • ((r * e) • n))) : eCorner he.1 N).val =
        r • (φ (toECorner he.1 n) : eCorner he.1 N).val
      simp_rw [← mul_smul (α := A)]
      -- toECorner((p.2 * (r * e)) • n) = ⟨e*(p.2*r)*e, _⟩ •_{eAe} toECorner(n)
      have h_toE2 : ∀ p : A × A,
          toECorner he.1 ((p.2 * (r * e)) • n) =
            (⟨e * (p.2 * r) * e, ⟨p.2 * r, rfl⟩⟩ : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) •
              toECorner he.1 n := by
        intro p; apply Subtype.ext
        change e • ((p.2 * (r * e)) • n) = (e * (p.2 * r) * e) • (e • n)
        rw [← mul_smul, ← mul_smul]
        congr 1
        simp only [mul_assoc]
        rw [he.1.eq]
      rw [show ∑ p ∈ σ.support, (σ p * p.1) •
          (φ (toECorner he.1 ((p.2 * (r * e)) • n)) : eCorner he.1 N).val =
          ∑ p ∈ σ.support, (σ p * p.1 * (e * (p.2 * r) * e)) •
            (φ (toECorner he.1 n) : eCorner he.1 N).val by
        apply Finset.sum_congr rfl
        intro p hp
        rw [h_toE2 p, coe_map_smul, ← mul_smul], ← Finset.sum_smul]
      -- Sum: ∑ σ_p * p.1 * (e * (p.2 * r) * e) = r * e
      have hsum_eq : ∑ p ∈ σ.support, σ p * p.1 * (e * (p.2 * r) * e) = r * e := by
        have : ∀ p ∈ σ.support, σ p * p.1 * (e * (p.2 * r) * e) =
            σ p * (p.1 * e * p.2) * r * e := fun p _ => by simp only [mul_assoc]
        rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Finset.sum_mul, hσ1, one_mul]
      rw [hsum_eq, mul_smul, (φ (toECorner he.1 n)).prop]
    | zero =>
      intro r
      simp only [smul_zero]
      have h0 : liftFun (0 : M) = 0 := by
        have h := lift_add (0 : M) 0; simp only [add_zero] at h
        -- h : liftFun 0 = liftFun 0 + liftFun 0
        have : liftFun (0 : M) + liftFun (0 : M) = liftFun (0 : M) + 0 := by rw [add_zero]; exact h.symm
        exact add_left_cancel this
      rw [h0, smul_zero]
    | add x y _ _ ihx ihy =>
      intro r
      rw [smul_add, lift_add, lift_add, ihx r, ihy r, smul_add]
    | smul a x _ ihx =>
      intro r
      -- liftFun(r • (a • x)) = liftFun((r*a) • x) = (r*a) • liftFun(x) = r • (a • liftFun(x))
      --                       = r • liftFun(a • x)
      rw [← mul_smul, ihx (r * a), mul_smul, ← ihx a]
  let f : M →ₗ[A] N :=
    { toFun := liftFun
      map_add' := lift_add
      map_smul' := lift_smul }
  refine ⟨ModuleCat.ofHom f, ?_⟩
  ext ⟨m, hm⟩
  -- hm : e smul m = m. Show f(m) = phi(m,hm) in eN.
  apply Subtype.ext
  change ∑ p ∈ σ.support, (σ p * p.1) •
      ((φ (toECorner he.1 (p.2 • m))) : eCorner he.1 N).val =
    (φ ⟨m, hm⟩ : eCorner he.1 N).val
  -- For m in eM: toECorner(b smul m) = (ebe) smul_{eAe} (m, hm)
  have htoE : ∀ p : A × A, toECorner he.1 (p.2 • m) =
      (⟨e * p.2 * e, ⟨p.2, rfl⟩⟩ : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) • ⟨m, hm⟩ := by
    intro p; apply Subtype.ext
    change e • (p.2 • m) = (e * p.2 * e) • m
    rw [mul_smul, mul_smul, hm]
  rw [show ∑ p ∈ σ.support, (σ p * p.1) •
      (φ (toECorner he.1 (p.2 • m)) : eCorner he.1 N).val =
      ∑ p ∈ σ.support, (σ p * p.1 * (e * p.2 * e)) •
        (φ ⟨m, hm⟩ : eCorner he.1 N).val by
    apply Finset.sum_congr rfl
    intro p hp
    rw [htoE p, coe_map_smul, ← mul_smul], ← Finset.sum_smul]
  -- Sum collapses: sum(sigma(p) * p.1 * e * p.2 * e) = 1 * e = e
  conv_lhs => arg 1; arg 2; ext p; rw [show σ p * p.1 * (e * p.2 * e) =
    σ p * (p.1 * e * p.2) * e by simp only [mul_assoc]]
  rw [← Finset.sum_mul]
  have hσ2 : ∑ p ∈ σ.support, σ p * (p.1 * e * p.2) = 1 := by
    have := hσ; simp only [Finsupp.sum, smul_eq_mul] at this; exact this
  rw [hσ2, one_mul]
  exact (φ ⟨m, hm⟩).prop



set_option maxHeartbeats 800000 in
private lemma cornerFunctor_essSurj {e : A} (he : ringElementCondition e) :
    letI := RepresentationTheory.RingTheory.Idempotent.submodule.ring (k := k) he.1
    (cornerFunctor (k := k) he.1).EssSurj := by
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1
  constructor
  intro N
  -- Extract carrier type and instances from the ModuleCat object
  let Nty : Type u := N
  letI : AddCommGroup Nty := N.isAddCommGroup
  letI : Module (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) Nty := N.isModule
  letI : Module k Nty := Module.compHom Nty (algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e))
  -- Form the balanced tensor product A ⊗_{eAe} N
  -- T = A ⊗_k N with A-module structure via left multiplication
  letI : Module A (TensorProduct k A Nty) := TensorProduct.leftModule
  -- S = A-submodule generated by balanced relations {ar ⊗ n - a ⊗ rn | r ∈ eAe}
  let S : Submodule A (TensorProduct k A Nty) := Submodule.span A
    (Set.range fun (p : A × (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) × Nty) =>
      let ⟨a, r, n⟩ := p
      (a * (r : A)) ⊗ₜ[k] n - a ⊗ₜ[k] (r • n))
  -- Q = T/S has A-module structure
  let M : ModuleCat.{u} A := ModuleCat.of A (TensorProduct k A Nty ⧸ S)
  -- Claim: eM ≅ N as RepresentationTheory.RingTheory.Idempotent.submodule-modules
  -- Forward: ⟨e • [a ⊗ n], _⟩ ↦ (eae-part of a) • n
  -- Inverse: n ↦ ⟨e • [e ⊗ n], _⟩
  letI := eCornerModule (k := k) he.1 M
  -- Helper: eae ∈ RepresentationTheory.RingTheory.Idempotent.submodule for any a
  have eae_mem : ∀ a : A, e * a * e ∈ RepresentationTheory.RingTheory.Idempotent.sandwichSubmodule (k := k) e :=
    fun a => (RepresentationTheory.RingTheory.Idempotent.mem_sandwichSubmodule_iff e _).mpr ⟨a, rfl⟩
  -- Abbreviation for corner elements
  let cr (a : A) : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e := ⟨e * a * e, eae_mem a⟩
  -- Forward map: A ⊗_k N → N by a ⊗ n ↦ cr(a) • n
  -- Build via TensorProduct.lift from a k-bilinear map
  let fwd_tensor : TensorProduct k A Nty →ₗ[k] Nty :=
    TensorProduct.lift
      { toFun := fun a =>
          { toFun := fun n => cr a • n
            map_add' := smul_add (cr a)
            map_smul' := fun c n => by
              -- c •_k n on N means (algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule e) c) • n (via compHom)
              -- Need: cr(a) • (c •_k n) = c •_k (cr(a) • n)
              -- = algebraMap c • (cr(a) • n) = (algebraMap c * cr(a)) • n
              -- and cr(a) • (algebraMap c • n) = (cr(a) * algebraMap c) • n
              -- These are equal since algebraMap commutes with everything in eAe
              dsimp only [RingHom.id_apply]
              change cr a • (algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) c • n) =
                algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) c • (cr a • n)
              rw [← mul_smul, ← mul_smul]
              congr 1; exact (Algebra.commutes c (cr a)).symm }
        map_add' := fun a₁ a₂ => by
          ext n; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          have : cr (a₁ + a₂) = cr a₁ + cr a₂ :=
            Subtype.ext (by simp [cr, mul_add, add_mul])
          rw [this, add_smul]
        map_smul' := fun c a => by
          ext n; simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
            LinearMap.smul_apply]
          -- c •_k (cr(a) • n) vs cr(c • a) • n
          -- cr(c • a) = ⟨e * (c • a) * e⟩ = c • cr(a) in RepresentationTheory.RingTheory.Idempotent.submodule
          have hcr : cr (c • a) = c • cr a :=
            Subtype.ext (by simp [cr, Algebra.smul_mul_assoc, Algebra.mul_smul_comm])
          rw [hcr]
          -- (c • cr(a)) • n = c •_k (cr(a) • n)
          -- = algebraMap c • (cr(a) • n) = (algebraMap c * cr(a)) • n
          -- and (c • cr(a)) • n = (algebraMap c * cr(a)) • n by Algebra.smul_def
          rw [show (c : k) • (cr a • n) = algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) c • (cr a • n)
            from rfl, ← mul_smul, Algebra.smul_def] }
  -- fwd_tensor kills S (balanced relations)
  -- Strategy: use span_induction with P(x) := ∀ a, fwd_tensor(a • x) = 0
  -- then specialize a = 1. This handles the smul case via mul_smul.
  have fwd_kills_S : ∀ x ∈ S, fwd_tensor x = 0 := by
    -- Helper: fwd_tensor on generators is zero (for any left A-multiple)
    have gen_zero : ∀ (a : A) (b : A) (r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (n : Nty),
        fwd_tensor (a • ((b * (r : A)) ⊗ₜ[k] n - b ⊗ₜ[k] (r • n))) = 0 := by
      intro a b r n
      -- a • (b*r ⊗ n - b ⊗ r•n) = (a*b*r) ⊗ n - (a*b) ⊗ r•n in leftModule
      -- In TensorProduct.leftModule, a • (b ⊗ n) = (a * b) ⊗ n
      -- Use smul_sub to distribute, then unfold the leftModule smul on each tensor
      have hleft : ∀ (c d : A) (m : Nty), c • (d ⊗ₜ[k] m) = (c * d) ⊗ₜ[k] m :=
        fun c d m => TensorProduct.smul_tmul' c d m
      rw [smul_sub, hleft, hleft, ← mul_assoc, map_sub]
      -- fwd((a*b*r) ⊗ n) = cr(a*b*r) • n, fwd((a*b) ⊗ r•n) = cr(a*b) • (r•n)
      -- cr(a*b*r) = cr(a*b) * r since r ∈ eAe
      change cr (a * b * (r : A)) • n - cr (a * b) • (r • n) = 0
      have hcr_mul : cr (a * b * (r : A)) = cr (a * b) * r := by
        apply Subtype.ext
        change e * (a * b * (r : A)) * e = (e * (a * b) * e) * (r : A)
        have := RepresentationTheory.RingTheory.Idempotent.left_mul_eq_of_mem_sandwichSubmodule (k := k) he.1 r.prop
        -- this : e * ↑r = ↑r
        calc e * (a * b * (r : A)) * e
            = e * a * b * (r : A) * e := by simp only [mul_assoc]
          _ = e * a * b * (e * (r : A)) * e := by rw [this]
          _ = (e * (a * b) * e) * ((r : A) * e) := by simp only [mul_assoc]
          _ = (e * (a * b) * e) * (r : A) := by
                rw [RepresentationTheory.RingTheory.Idempotent.right_mul_eq_of_mem_sandwichSubmodule (k := k) he.1 r.prop]
      rw [hcr_mul, mul_smul, sub_self]
    intro x hx
    -- Use span_induction with strengthened predicate: P(x) = ∀ a, fwd_tensor(a • x) = 0
    -- Then specialize a = 1 to get fwd_tensor(x) = 0
    suffices h : ∀ a : A, fwd_tensor (a • x) = 0 by
      have := h 1; simp only [one_smul] at this; exact this
    induction hx using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨b, r, n⟩, rfl⟩ := hg
      exact fun a => gen_zero a b r n
    | zero => intro a; simp [smul_zero, map_zero]
    | add y z _ _ ihy ihz =>
      intro a; rw [smul_add, map_add, ihy a, ihz a, add_zero]
    | smul b y _ ihy =>
      intro a; rw [← mul_smul]; exact ihy (a * b)
  -- Quotient map
  let q : TensorProduct k A Nty →ₗ[A] (TensorProduct k A Nty ⧸ S) := S.mkQ
  -- Helper: balanced relation in quotient
  have q_bal_mem : ∀ (a : A) (r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (n : Nty),
      (a * (r : A)) ⊗ₜ[k] n - a ⊗ₜ[k] (r • n) ∈ S :=
    fun a r n => Submodule.subset_span ⟨⟨a, r, n⟩, rfl⟩
  -- Forward map descends to quotient via QuotientAddGroup.lift
  let fwd_q_add : (TensorProduct k A Nty ⧸ S) →+ Nty :=
    QuotientAddGroup.lift S.toAddSubgroup fwd_tensor.toAddMonoidHom
      (fun x hx => fwd_kills_S x hx)
  -- fwd_q_add on representatives: fwd_q_add(q(t)) = fwd_tensor(t)
  have fwd_q_rep : ∀ t : TensorProduct k A Nty, fwd_q_add (q t) = fwd_tensor t :=
    fun _ => rfl
  -- Inverse map: N → eM by n ↦ ⟨q(e ⊗ n), ...⟩
  have inv_mem : ∀ n : Nty, e • (q (e ⊗ₜ[k] n)) = q (e ⊗ₜ[k] n) := by
    intro n
    change q (e • (e ⊗ₜ[k] n)) = q (e ⊗ₜ[k] n)
    congr 1
    change (e * e) ⊗ₜ[k] n = e ⊗ₜ[k] n
    rw [he.1.eq]
  let inv_fun : Nty → eCorner he.1 (TensorProduct k A Nty ⧸ S) :=
    fun n => ⟨q (e ⊗ₜ[k] n), inv_mem n⟩
  have inv_add : ∀ n₁ n₂ : Nty, inv_fun (n₁ + n₂) = inv_fun n₁ + inv_fun n₂ := by
    intro n₁ n₂; apply Subtype.ext
    change q (e ⊗ₜ[k] (n₁ + n₂)) = (q (e ⊗ₜ[k] n₁) : TensorProduct k A Nty ⧸ S) + q (e ⊗ₜ[k] n₂)
    rw [TensorProduct.tmul_add, map_add]
  -- Forward-inverse: fwd(inv(n)) = n
  have fwd_inv : ∀ n : Nty, fwd_q_add (inv_fun n).val = n := by
    intro n
    -- fwd_q_add(q(e ⊗ n)) = fwd_tensor(e ⊗ n) = cr(e) • n = 1 • n = n
    change fwd_tensor (e ⊗ₜ[k] n) = n
    change cr e • n = n
    have : cr e = 1 := Subtype.ext (by change e * e * e = e; rw [he.1.eq, he.1.eq])
    rw [this, one_smul]
  -- Helper: ↑(1 : RepresentationTheory.RingTheory.Idempotent.submodule e) = e
  have coe_one : ((1 : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) : A) = e := rfl
  -- Balanced relation in quotient: q(eae ⊗ n) = q(ea ⊗ n)
  have q_eae_eq_ea : ∀ (a : A) (n : Nty),
      q ((e * a * e) ⊗ₜ[k] n) = q ((e * a) ⊗ₜ[k] n) := by
    intro a n
    rw [← sub_eq_zero, ← map_sub]
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    convert q_bal_mem (e * a) 1 n using 1
    simp only [one_smul, mul_assoc, coe_one]
  -- Balanced relation helper: q(e ⊗ r•n) = q(e*r ⊗ n)
  have q_bal_eq : ∀ (r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (n : Nty),
      q (e ⊗ₜ[k] (r • n)) = q ((e * (r : A)) ⊗ₜ[k] n) := by
    intro r n
    have h : q ((e * (r : A)) ⊗ₜ[k] n) - q (e ⊗ₜ[k] (r • n)) = 0 := by
      rw [← q.map_sub]
      exact (Submodule.Quotient.mk_eq_zero S).mpr (q_bal_mem e r n)
    exact (eq_of_sub_eq_zero h).symm
  -- Inverse-forward: for any m, inv(fwd(m)).val = e • q(m)
  have inv_fwd_all : ∀ t : TensorProduct k A Nty,
      (inv_fun (fwd_tensor t)).val = e • q t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [inv_fun, map_zero, smul_zero]
    | tmul a n =>
      change q (e ⊗ₜ[k] (cr a • n)) = e • q (a ⊗ₜ[k] n)
      -- q(e ⊗ cr(a)•n) = q(e*cr(a) ⊗ n) = q(eae ⊗ n) = q(ea ⊗ n) = e • q(a ⊗ n)
      rw [q_bal_eq (cr a) n, RepresentationTheory.RingTheory.Idempotent.left_mul_eq_of_mem_sandwichSubmodule (k := k) he.1 (eae_mem a), q_eae_eq_ea]
      exact (q.map_smul e (a ⊗ₜ[k] n)).symm
    | add x y ihx ihy =>
      simp only [map_add (f := q), map_add (f := fwd_tensor), smul_add]
      have hadd : (inv_fun (fwd_tensor x + fwd_tensor y)).val =
          (inv_fun (fwd_tensor x)).val + (inv_fun (fwd_tensor y)).val :=
        congr_arg Subtype.val (inv_add (fwd_tensor x) (fwd_tensor y))
      rw [hadd, ihx, ihy]
  -- Round trip for eM
  have inv_fwd : ∀ m : eCorner he.1 (TensorProduct k A Nty ⧸ S),
      inv_fun (fwd_q_add m.val) = m := by
    intro ⟨m, hm⟩
    apply Subtype.ext
    suffices h : (inv_fun (fwd_q_add m)).val = e • m by rw [h, hm]
    clear hm
    induction m using Submodule.Quotient.induction_on with
    | H t =>
      change (inv_fun (fwd_q_add (q t))).val = e • q t
      rw [fwd_q_rep, inv_fwd_all]
  -- inv_fun is RepresentationTheory.RingTheory.Idempotent.submodule-linear
  have inv_smul : ∀ (r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (n : Nty),
      inv_fun (r • n) = r • inv_fun n := by
    intro r n; apply Subtype.ext
    change q (e ⊗ₜ[k] (r • n)) = (r : A) • q (e ⊗ₜ[k] n)
    rw [q_bal_eq r n, ← q.map_smul]
    -- q(e*r ⊗ n) = q((r:A) • (e ⊗ n)) = q((r:A)*e ⊗ n)
    -- e*r = r by left_mul, (r:A)*e = r by right_mul
    congr 1
    change (e * (r : A)) ⊗ₜ[k] n = ((r : A) * e) ⊗ₜ[k] n
    rw [RepresentationTheory.RingTheory.Idempotent.left_mul_eq_of_mem_sandwichSubmodule (k := k) he.1 r.prop,
        RepresentationTheory.RingTheory.Idempotent.right_mul_eq_of_mem_sandwichSubmodule (k := k) he.1 r.prop]
  -- fwd_tensor is RepresentationTheory.RingTheory.Idempotent.submodule-equivariant via A-action
  have fwd_A_smul : ∀ (r : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (t : TensorProduct k A Nty),
      fwd_tensor ((r : A) • t) = r • fwd_tensor t := by
    intro r t
    induction t using TensorProduct.induction_on with
    | zero => simp [smul_zero, map_zero]
    | tmul a n =>
      change cr ((↑r : A) * a) • n = r • (cr a • n)
      rw [← mul_smul]; congr 1
      apply Subtype.ext
      change e * ((↑r : A) * a) * e = (↑r : A) * (e * a * e)
      have hleft := RepresentationTheory.RingTheory.Idempotent.left_mul_eq_of_mem_sandwichSubmodule (k := k) he.1 r.prop
      have hright := RepresentationTheory.RingTheory.Idempotent.right_mul_eq_of_mem_sandwichSubmodule (k := k) he.1 r.prop
      have h1 : e * ((↑r : A) * a) * e = ↑r * a * e := by
        conv_lhs => rw [show e * (↑r * a) * e = (e * ↑r) * a * e from by
          simp only [mul_assoc], hleft]
      have h2 : (↑r : A) * (e * a * e) = ↑r * a * e := by
        conv_lhs => rw [show (↑r : A) * (e * a * e) = (↑r * e) * a * e from by
          simp only [mul_assoc], hright]
      rw [h1, h2]
    | add x y ihx ihy =>
      rw [smul_add, map_add, map_add, ihx, ihy, smul_add]
  -- Construct the isomorphism in ModuleCat
  refine ⟨M, ⟨?_⟩⟩
  exact
    { hom := ModuleCat.ofHom
        { toFun := fun m => fwd_q_add m.val
          map_add' := fun m₁ m₂ => by simp [map_add]
          map_smul' := fun r m => by
            change fwd_q_add ((r : A) • m.val) = r • fwd_q_add m.val
            obtain ⟨mval, hm⟩ := m
            induction mval using Submodule.Quotient.induction_on with
            | H t =>
              change fwd_q_add (q ((↑r : A) • t)) = r • fwd_tensor t
              rw [fwd_q_rep, fwd_A_smul] }
      inv := ModuleCat.ofHom
        { toFun := inv_fun
          map_add' := inv_add
          map_smul' := fun r n => by rw [RingHom.id_apply]; exact inv_smul r n }
      hom_inv_id := by
        ext ⟨m, hm⟩
        exact Subtype.ext (congr_arg Subtype.val (inv_fwd ⟨m, hm⟩))
      inv_hom_id := by ext n; exact fwd_inv n }


/-- Shows that the membership subtype associated with an element satisfying the condition has the displayed property. -/
lemma membershipSubtype_has_condition_of_ringElementCondition
    {e : A} (he : ringElementCondition e) :
    @RepresentationTheory.RingAuxiliary.RingAuxiliary A _ (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1) := by
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1
  haveI hfull : (cornerFunctor (k := k) he.1).Full := cornerFunctor_full he
  haveI hfaith : (cornerFunctor (k := k) he.1).Faithful := cornerFunctor_faithful he
  haveI hesssurj : (cornerFunctor (k := k) he.1).EssSurj := cornerFunctor_essSurj he
  haveI : (cornerFunctor (k := k) he.1).IsEquivalence :=
    { faithful := hfaith, full := hfull, essSurj := hesssurj }
  exact ⟨(cornerFunctor (k := k) he.1).asEquivalence⟩


private noncomputable instance cornerFunctor_additive {e : A} (he : IsIdempotentElem e) :
    letI := RepresentationTheory.RingTheory.Idempotent.submodule.ring (k := k) he
    (cornerFunctor (k := k) he).Additive := by
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he
  exact ⟨fun {M N f g} => by ext m; exact Subtype.ext (LinearMap.add_apply f.hom g.hom m.val)⟩

open scoped ModuleCat in

private noncomputable instance cornerFunctor_linear_k {e : A} (he : IsIdempotentElem e) :
    letI := RepresentationTheory.RingTheory.Idempotent.submodule.ring (k := k) he
    letI := RepresentationTheory.RingTheory.Idempotent.submodule.algebra (k := k) he
    haveI := cornerFunctor_additive (k := k) he
    (cornerFunctor (k := k) he).Linear k := by
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he
  haveI := cornerFunctor_additive (k := k) he
  constructor
  intro M N f r
  -- Need: cornerFunctor.map (r • f) = r • cornerFunctor.map f
  -- After ext m : eCorner he M, both sides give Subtype.ext of an equality in N
  ext m; apply Subtype.ext
  -- LHS: ((r • f).hom m.val : N) by hom_smul = (r • f.hom) m.val = r • f.hom(m.val)
  -- where r acts on N via RestrictScalars k A N, i.e., algebraMap k A r • _
  -- RHS: ((r • cornerFunctor.map f).hom m : eCorner he N).val by hom_smul
  -- = (r • (cornerFunctor.map f).hom) m coerced
  -- where r acts on eCorner he N via RestrictScalars k RepresentationTheory.RingTheory.Idempotent.submodule (eCorner he N)
  -- i.e., algebraMap k RepresentationTheory.RingTheory.Idempotent.submodule r • _ where the RepresentationTheory.RingTheory.Idempotent.submodule smul on eCorner
  -- satisfies (a • x).val = (a : A) • x.val
  -- So RHS = ((algebraMap k RepresentationTheory.RingTheory.Idempotent.submodule r : A) • f.hom m.val)
  -- = (algebraMap k A r * e) • f.hom m.val [since algebraMap k RepresentationTheory.RingTheory.Idempotent.submodule r = r • e]
  -- = algebraMap k A r • (e • f.hom m.val) [by mul_smul]
  -- = algebraMap k A r • f.hom m.val [since f.hom m.val ∈ eN]
  -- Both sides equal algebraMap k A r • f.hom m.val:
  -- LHS via RestrictScalars k A, RHS via algebraMap k RepresentationTheory.RingTheory.Idempotent.submodule r = algebraMap k A r * e
  -- and e • f.hom(m.val) = f.hom(m.val).
  change (r • f).hom m.val = (↑(algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) r) : A) • f.hom m.val
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  -- Goal: r • f.hom m.val = (algebraMap k RepresentationTheory.RingTheory.Idempotent.submodule r : A) • f.hom m.val
  -- LHS r • uses RestrictScalars k A, which is definitionally algebraMap k A r •
  change algebraMap k A r • f.hom m.val =
    (↑(algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) r) : A) • f.hom m.val
  -- (algebraMap k RepresentationTheory.RingTheory.Idempotent.submodule r : A) = algebraMap k A r * e
  have h_one_val : (1 : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e).val = e := by
    change (@One.one (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e)
      (RepresentationTheory.RingTheory.Idempotent.submodule.ring (k := k) he).toSemiring.toMulOneClass.toOne).val = e
    rfl
  have h_alg : (↑(algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) r) : A) = algebraMap k A r * e := by
    rw [Algebra.algebraMap_eq_smul_one, show (r • (1 : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e)).val =
      r • (1 : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e).val from rfl, h_one_val, Algebra.smul_def]
  rw [h_alg, mul_smul]
  -- Goal: algebraMap k A r • f.hom m.val = algebraMap k A r • (e • f.hom m.val)
  -- e • f.hom m.val = f.hom m.val since m ∈ eM
  congr 1
  have : f.hom (e • m.val) = e • f.hom m.val := map_smul f.hom e m.val
  rw [eCorner_prop m] at this
  exact this


/-- Shows that the membership subtype associated with an element satisfying the condition has the displayed indexed property. -/
lemma membershipSubtype_has_indexed_condition_of_ringElementCondition
    {e : A} (he : ringElementCondition e) [Module.Finite k A] :
    @RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k _ A _ _ (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e)
      (RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1) (RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1) := by
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1
  haveI hfull : (cornerFunctor (k := k) he.1).Full := cornerFunctor_full he
  haveI hfaith : (cornerFunctor (k := k) he.1).Faithful := cornerFunctor_faithful he
  haveI hesssurj : (cornerFunctor (k := k) he.1).EssSurj := cornerFunctor_essSurj he
  haveI : (cornerFunctor (k := k) he.1).IsEquivalence :=
    { faithful := hfaith, full := hfull, essSurj := hesssurj }
  let E := (cornerFunctor (k := k) he.1).asEquivalence
  refine ⟨E, ?_⟩
  -- E.functor is definitionally the cornerFunctor, so the Linear instance transfers
  haveI : E.functor.Additive := by
    haveI : E.functor.IsEquivalence := E.isEquivalence_functor
    exact Functor.additive_of_preserves_binary_products E.functor
  exact cornerFunctor_linear_k (k := k) he.1


/-- Under the displayed finite algebra hypotheses, produces an auxiliary object and nested witnesses satisfying two stated conditions. -/
theorem exists_nested_witnesses_with_two_conditions
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧ RepresentationTheory.RingAuxiliary.RingAuxiliary A B := by
  obtain ⟨e, he, _, hbasic⟩ := exists_element_with_membership_subtype_conditions k A
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1
  exact ⟨RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e,
    RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1,
    RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1,
    RepresentationTheory.RingTheory.Idempotent.submodule.moduleFinite,
    hbasic,
    membershipSubtype_has_condition_of_ringElementCondition he⟩


/-- Under the displayed finite algebra hypotheses, produces an auxiliary object and nested witnesses satisfying three stated conditions. -/
theorem exists_nested_witnesses_with_three_conditions
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type u) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'.{u, u, u} k B ∧ RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty k B ∧
        RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k A B := by
  obtain ⟨e, he, hsplit, hbasic⟩ := exists_element_with_membership_subtype_conditions k A
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1
  exact ⟨RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e,
    RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1,
    RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1,
    RepresentationTheory.RingTheory.Idempotent.submodule.moduleFinite,
    hsplit,
    hbasic,
    membershipSubtype_has_indexed_condition_of_ringElementCondition he⟩

end RepresentationTheory.RingTheory.ElementProperties

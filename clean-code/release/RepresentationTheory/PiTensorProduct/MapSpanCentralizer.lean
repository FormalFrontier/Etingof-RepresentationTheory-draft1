/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.MutualCentralizers
import RepresentationTheory.Alignment.Attribute

open RepresentationTheory.Auxiliary.MutualCentralizers

namespace RepresentationTheory.PiTensorProduct.MapSpanCentralizer

namespace Auxiliary

variable {k : Type*} [Field k] [Infinite k]
  {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

private def linearEquivImage :
    Set (Module.End k (auxiliarySpace k V n)) :=
  Set.range fun (g : V ≃ₗ[k] V) =>
    PiTensorProduct.map (fun (_ : Fin n) => g.toLinearMap)

private def endomorphismImage :
    Set (Module.End k (auxiliarySpace k V n)) :=
  Set.range fun (f : Module.End k V) =>
    PiTensorProduct.map (fun (_ : Fin n) => f)

omit [Infinite k] [Module.Finite k V] in
private lemma endomorphismImage_mul_closed :
    ∀ a ∈ endomorphismImage (k := k) (V := V) n,
      ∀ b ∈ endomorphismImage (k := k) (V := V) n,
        a * b ∈ endomorphismImage (k := k) (V := V) n := by
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  exact ⟨f ∘ₗ g, by ext; simp [PiTensorProduct.map_tprod]⟩

omit [Infinite k] [Module.Finite k V] in
private lemma one_mem_endomorphismImage :
    (1 : Module.End k (auxiliarySpace k V n)) ∈
      endomorphismImage (k := k) (V := V) n := by
  exact ⟨LinearMap.id, by ext; simp⟩

omit [Infinite k] in
private lemma finite_nonunit_shifts (f : Module.End k V) :
    Set.Finite {t : k | ¬ IsUnit (f + t • LinearMap.id)} := by
  have key : ∀ t, ¬ IsUnit (f + t • LinearMap.id) →
      Polynomial.IsRoot ((-f).charpoly) t := by
    intro t ht
    rw [Polynomial.IsRoot, LinearMap.eval_charpoly]
    have : algebraMap k (Module.End k V) t - (-f) =
        f + t • LinearMap.id := by
      ext v
      simp [Algebra.algebraMap_eq_smul_one, add_comm]
    rw [this]
    have hnu := mt (LinearMap.isUnit_iff_isUnit_det _).mpr ht
    rwa [isUnit_iff_ne_zero, not_not] at hnu
  exact Set.Finite.subset
    (Polynomial.finite_setOf_isRoot
      (Polynomial.Monic.ne_zero (LinearMap.charpoly_monic (-f))))
    (fun t ht => key t ht)

omit [Infinite k] [Module.Finite k V] in
private lemma map_add_expansion (f g : Fin n → Module.End k V) :
    PiTensorProduct.map (fun i => f i + g i) =
      ∑ S : Finset (Fin n), PiTensorProduct.map (S.piecewise f g) := by
  have h := (PiTensorProduct.mapMultilinear k
    (fun (_ : Fin n) => V) (fun (_ : Fin n) => V)).map_add_univ f g
  simp only [PiTensorProduct.mapMultilinear_apply] at h
  exact h

omit [Infinite k] [Module.Finite k V] in
private lemma map_piecewise_smul_factor
    (f : Module.End k V) (t : k) (S : Finset (Fin n)) :
    PiTensorProduct.map
      (fun i => S.piecewise (fun _ => f) (fun _ => t • LinearMap.id) i) =
    t ^ (Finset.univ \ S).card •
      PiTensorProduct.map
        (fun i => S.piecewise (fun _ => f) (fun _ => LinearMap.id) i) := by
  have hfun :
      (fun i => S.piecewise (fun _ => f) (fun _ => t • LinearMap.id) i) =
        (fun i => S.piecewise (fun _ => (1 : k)) (fun _ => t) i •
          S.piecewise (fun _ => f) (fun _ => LinearMap.id) i) := by
    ext i
    by_cases hi : i ∈ S
    · simp [Finset.piecewise, hi]
    · simp [Finset.piecewise, hi]
  rw [hfun]
  have h := (PiTensorProduct.mapMultilinear k
    (fun (_ : Fin n) => V) (fun (_ : Fin n) => V)).map_smul_univ
    (fun i => S.piecewise (fun _ => (1 : k)) (fun _ => t) i)
    (fun i => S.piecewise (fun _ => f) (fun _ => LinearMap.id) i)
  simp only [PiTensorProduct.mapMultilinear_apply] at h
  rw [h]
  congr 1
  rw [Finset.prod_piecewise]
  simp [Finset.prod_const,
    Finset.inter_eq_right.mpr (Finset.subset_univ S),
    Finset.sdiff_eq_filter]

omit [Infinite k] [Module.Finite k V] in
private lemma tensorPower_add_smul_id_expansion
    (f : Module.End k V) (t : k) :
    PiTensorProduct.map (fun (_ : Fin n) => f + t • LinearMap.id) =
      ∑ S : Finset (Fin n),
        t ^ (Finset.univ \ S).card •
          PiTensorProduct.map
            (fun i => S.piecewise (fun _ => f) (fun _ => LinearMap.id) i) := by
  have h := map_add_expansion n (fun _ => f) (fun _ => t • LinearMap.id)
  rw [h]
  congr 1
  ext1 S
  exact map_piecewise_smul_factor n f t S

omit [Infinite k] [Module.Finite k V] in
private lemma piecewise_univ_eq (f : Module.End k V) :
    (fun i => ((Finset.univ : Finset (Fin n)).piecewise
      (fun _ => f) (fun _ => LinearMap.id) i)) = (fun _ => f) := by
  ext i
  simp [Finset.mem_univ]

omit [Infinite k] in
private lemma lagrange_eval_zero_pow
    (v : Fin (n + 1) → k) (hv : Function.Injective v)
    (m : ℕ) (hm : m ≤ n) :
    ∑ i : Fin (n + 1),
        (Lagrange.basis Finset.univ v i).eval 0 * v i ^ m =
      (0 : k) ^ m := by
  have hv_injOn : Set.InjOn v (Finset.univ : Finset (Fin (n + 1))) := by
    intro a _ b _
    exact @hv a b
  have hdeg : (Polynomial.X ^ m : Polynomial k).degree <
      ((Finset.univ : Finset (Fin (n + 1))).card : ℕ) := by
    have h1 := Polynomial.degree_X_pow_le (R := k) m
    have h2 : (m : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast (show m < n + 1 by omega)
    simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt h1 h2
  have heq :=
    Lagrange.eq_interpolate (f := (Polynomial.X ^ m : Polynomial k)) hv_injOn hdeg
  have heval := congr_arg (Polynomial.eval (0 : k)) heq
  rw [Polynomial.eval_pow, Polynomial.eval_X] at heval
  rw [heval, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  congr 1
  ext i
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, mul_comm]

private lemma endomorphism_map_mem_linearEquiv_span (f : Module.End k V) :
    PiTensorProduct.map (fun (_ : Fin n) => f) ∈
      Submodule.span k (linearEquivImage n) := by
  have hinv : Set.Infinite {t : k | IsUnit (f + t • LinearMap.id)} := by
    rw [show {t : k | IsUnit (f + t • LinearMap.id)} =
        {t : k | ¬ IsUnit (f + t • LinearMap.id)}ᶜ from by
      ext
      simp]
    exact Set.Finite.infinite_compl (finite_nonunit_shifts f)
  let e := hinv.natEmbedding
  let v : Fin (n + 1) → k := fun i => (e i.val).val
  have hv_inj : Function.Injective v := by
    intro a b h
    exact Fin.val_injective (e.injective (Subtype.val_injective h))
  have hv_mem : ∀ i : Fin (n + 1),
      IsUnit (f + v i • LinearMap.id) :=
    fun i => (e i.val).prop
  have hgl : ∀ i : Fin (n + 1),
      PiTensorProduct.map (fun (_ : Fin n) => f + v i • LinearMap.id) ∈
        Submodule.span k (linearEquivImage n) := by
    intro i
    apply Submodule.subset_span
    have hu := hv_mem i
    let u := hu.unit
    refine ⟨⟨u.val, u.inv, ?_, ?_⟩, ?_⟩
    · intro x
      change (u.inv.comp u.val) x = x
      have := u.inv_val
      change u.inv * u.val = 1 at this
      exact DFunLike.congr_fun this x
    · intro x
      change (u.val.comp u.inv) x = x
      have := u.val_inv
      change u.val * u.inv = 1 at this
      exact DFunLike.congr_fun this x
    · change PiTensorProduct.map (fun _ => u.val) =
          PiTensorProduct.map (fun _ => f + v i • LinearMap.id)
      have : u.val = f + v i • LinearMap.id := hu.unit_spec
      simp only [this]
  set L : Fin (n + 1) → k := fun i =>
    (Lagrange.basis (Finset.univ : Finset (Fin (n + 1))) v i).eval 0 with hL_def
  suffices h : PiTensorProduct.map (fun (_ : Fin n) => f) =
      ∑ i : Fin (n + 1), L i •
        PiTensorProduct.map (fun (_ : Fin n) => f + v i • LinearMap.id) by
    rw [h]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hgl i))
  simp_rw [tensorPower_add_smul_id_expansion n f]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single Finset.univ]
  · simp only [Finset.sdiff_self, Finset.card_empty]
    rw [lagrange_eval_zero_pow n v hv_inj 0 (Nat.zero_le _)]
    simp
  · intro S _ hS
    have hne : (Finset.univ \ S).Nonempty :=
      Finset.sdiff_nonempty.mpr (fun h => hS (Finset.eq_univ_of_forall
        (fun x => h (Finset.mem_univ x))))
    have hcard_pos : 0 < (Finset.univ \ S).card := Finset.card_pos.mpr hne
    have hcard_le : (Finset.univ \ S).card ≤ n := by
      calc
        (Finset.univ \ S).card ≤ Finset.univ.card :=
          Finset.card_le_card Finset.sdiff_subset
        _ = n := by simp [Finset.card_univ, Fintype.card_fin]
    rw [lagrange_eval_zero_pow n v hv_inj _ hcard_le]
    simp [zero_pow hcard_pos.ne']
  · intro h
    exact absurd (Finset.mem_univ _) h

end Auxiliary

/-- Over an infinite field, the span of the range of the pointwise tensor-product maps induced
by linear equivalences is the underlying submodule of the auxiliary subalgebra. -/
@[source_ref"Chapter5/Proposition5.19.1"(role:=primary)]
theorem span_range_piTensorProduct_map_eq_auxiliary
    {k : Type*} [Field k] [Infinite k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Submodule.span k (Set.range fun (g : V ≃ₗ[k] V) =>
      PiTensorProduct.map (fun (_ : Fin n) => g.toLinearMap)) =
    (auxiliaryEndomorphismAlgebra k V n).toSubmodule := by
  open Auxiliary in
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact Algebra.subset_adjoin ⟨g.toLinearMap, rfl⟩
  · have h_adjoin_eq : (auxiliaryEndomorphismAlgebra k V n).toSubmodule =
        Submodule.span k (endomorphismImage n) := by
      apply Algebra.adjoin_eq_span_of_subset
      intro x hx
      have hx_mem : x ∈ endomorphismImage (k := k) (V := V) n := by
        induction hx using Submonoid.closure_induction with
        | mem y hy => exact hy
        | one => exact one_mem_endomorphismImage n
        | mul _ _ _ _ ihx ihy =>
          exact endomorphismImage_mul_closed n _ ihx _ ihy
      exact Submodule.subset_span hx_mem
    rw [h_adjoin_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact endomorphism_map_mem_linearEquiv_span n f

/-- Over a field of characteristic zero, the span of the range of the pointwise tensor-product
maps induced by linear equivalences is the underlying submodule of the centralizer of the
auxiliary set. -/
@[source_ref"Chapter5/Proposition5.19.1"(role:=primary)]
theorem span_range_piTensorProduct_map_eq_centralizer_auxiliary
    {k : Type*} [Field k] [CharZero k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Submodule.span k (Set.range fun (g : V ≃ₗ[k] V) =>
      PiTensorProduct.map (fun (_ : Fin n) => g.toLinearMap)) =
    (Subalgebra.centralizer k
      (permutationActionAlgebra k V n :
        Set (Module.End k (auxiliarySpace k V n)))).toSubmodule := by
  rw [span_range_piTensorProduct_map_eq_auxiliary,
    centralizer_permutationActionAlgebra]

example (n : ℕ) (V : Type) [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] :
    Submodule.span ℚ (Set.range fun (g : V ≃ₗ[ℚ] V) =>
      PiTensorProduct.map (fun (_ : Fin n) => g.toLinearMap)) =
    (auxiliaryEndomorphismAlgebra ℚ V n).toSubmodule :=
  span_range_piTensorProduct_map_eq_auxiliary n

example (n : ℕ) (V : Type) [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V] :
    Submodule.span ℝ (Set.range fun (g : V ≃ₗ[ℝ] V) =>
      PiTensorProduct.map (fun (_ : Fin n) => g.toLinearMap)) =
    (auxiliaryEndomorphismAlgebra ℝ V n).toSubmodule :=
  span_range_piTensorProduct_map_eq_auxiliary n

example (n : ℕ) (V : Type) [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] :
    Submodule.span ℚ (Set.range fun (g : V ≃ₗ[ℚ] V) =>
      PiTensorProduct.map (fun (_ : Fin n) => g.toLinearMap)) =
    (Subalgebra.centralizer ℚ
      (permutationActionAlgebra ℚ V n :
        Set (Module.End ℚ (auxiliarySpace ℚ V n)))).toSubmodule :=
  span_range_piTensorProduct_map_eq_centralizer_auxiliary n

end RepresentationTheory.PiTensorProduct.MapSpanCentralizer

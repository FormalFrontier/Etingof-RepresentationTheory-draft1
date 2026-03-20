import EtingofRepresentationTheory.Chapter5.Theorem5_18_4
import Mathlib.LinearAlgebra.Lagrange

/-!
# Proposition 5.19.1: Image of GL(V) spans the centralizer algebra

The image of GL(V) in End(V⊗ⁿ) spans B (the centralizer algebra of the
Sₙ-action). This follows from the fact that the span of g⊗ⁿ for g ∈ GL(V)
equals the span of b⊗ⁿ for all b ∈ End(V), using a polynomial argument.

## Mathlib correspondence

Requires tensor power and Schur-Weyl duality infrastructure not yet in Mathlib.
-/

open Etingof

namespace Etingof.Proposition5_19_1_aux

variable {k : Type*} [Field k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- The GL-image set: {g⊗ⁿ | g ∈ GL(V)} -/
private def glImage : Set (Module.End k (TensorPower k V n)) :=
  Set.range fun (g : V ≃ₗ[k] V) =>
    PiTensorProduct.map (fun (_ : Fin n) => g.toLinearMap)

/-- The End-image set: {f⊗ⁿ | f ∈ End(V)} -/
private def endImage : Set (Module.End k (TensorPower k V n)) :=
  Set.range fun (f : Module.End k V) =>
    PiTensorProduct.map (fun (_ : Fin n) => f)

omit [IsAlgClosed k] [Module.Finite k V] in
/-- The End-image set is closed under multiplication, since
(f⊗ⁿ)(g⊗ⁿ) = (f∘g)⊗ⁿ. -/
private lemma endImage_mul_closed :
    ∀ a ∈ endImage (k := k) (V := V) n, ∀ b ∈ endImage (k := k) (V := V) n,
      a * b ∈ endImage (k := k) (V := V) n := by
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  exact ⟨f ∘ₗ g, by ext; simp [PiTensorProduct.map_tprod]⟩

omit [IsAlgClosed k] [Module.Finite k V] in
/-- 1 ∈ End-image since id⊗ⁿ = id. -/
private lemma one_mem_endImage :
    (1 : Module.End k (TensorPower k V n)) ∈ endImage (k := k) (V := V) n := by
  exact ⟨LinearMap.id, by ext; simp⟩

omit [IsAlgClosed k] in
/-- The set of scalars t where f + t • id is not invertible is finite,
since it's contained in the roots of the characteristic polynomial of -f.

Specifically, det(f + t • id) = (-f).charpoly.eval t, and charpoly(-f)
is monic of degree dim(V), hence has finitely many roots. -/
private lemma finite_nonUnit_shifts (f : Module.End k V) :
    Set.Finite {t : k | ¬ IsUnit (f + t • LinearMap.id)} := by
  have key : ∀ t, ¬ IsUnit (f + t • LinearMap.id) →
      Polynomial.IsRoot ((-f).charpoly) t := by
    intro t ht
    rw [Polynomial.IsRoot, LinearMap.eval_charpoly]
    have : algebraMap k (Module.End k V) t - (-f) = f + t • LinearMap.id := by
      ext v; simp [Algebra.algebraMap_eq_smul_one, add_comm]
    rw [this]
    -- ¬ IsUnit (f + t • id) → det = 0
    have hnu := mt (LinearMap.isUnit_iff_isUnit_det _).mpr ht
    rwa [isUnit_iff_ne_zero, not_not] at hnu
  exact Set.Finite.subset
    (Polynomial.finite_setOf_isRoot (Polynomial.Monic.ne_zero (LinearMap.charpoly_monic (-f))))
    (fun t ht => key t ht)

omit [IsAlgClosed k] [Module.Finite k V] in
/-- Multilinear expansion of PiTensorProduct.map over sums:
`map (fun i => f i + g i) = ∑_S map (S.piecewise f g)`. -/
private lemma map_add_expansion
    (f g : Fin n → Module.End k V) :
    PiTensorProduct.map (fun i => f i + g i) =
      ∑ S : Finset (Fin n),
        PiTensorProduct.map (S.piecewise f g) := by
  have h := (PiTensorProduct.mapMultilinear k
    (fun (_ : Fin n) => V) (fun (_ : Fin n) => V)).map_add_univ f g
  simp only [PiTensorProduct.mapMultilinear_apply] at h
  exact h

omit [IsAlgClosed k] [Module.Finite k V] in
/-- Factoring scalars: piecewise with `t • id` on the complement of S
gives `t ^ |Sᶜ|` times the piecewise with `id`. -/
private lemma map_piecewise_smul_factor
    (f : Module.End k V) (t : k) (S : Finset (Fin n)) :
    PiTensorProduct.map
      (fun i => (S.piecewise (fun _ => f) (fun _ => t • LinearMap.id) i)) =
    t ^ (Finset.univ \ S).card •
      PiTensorProduct.map
        (fun i => (S.piecewise (fun _ => f) (fun _ => LinearMap.id) i)) := by
  -- Write piecewise(f, t•id) = c • piecewise(f, id) where c i = 1 on S, t on Sᶜ
  have hfun : (fun i => S.piecewise (fun _ => f) (fun _ => t • LinearMap.id) i) =
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
  -- Use prod_piecewise to split the product over S and its complement
  rw [Finset.prod_piecewise]
  simp [Finset.prod_const, Finset.inter_eq_right.mpr (Finset.subset_univ S),
    Finset.sdiff_eq_filter]

omit [IsAlgClosed k] [Module.Finite k V] in
/-- The full expansion: `(f + t • id)⊗ⁿ = ∑_S t^|Sᶜ| • map(piecewise f id)`. -/
private lemma tensor_power_expansion
    (f : Module.End k V) (t : k) :
    PiTensorProduct.map (fun (_ : Fin n) => f + t • LinearMap.id) =
      ∑ S : Finset (Fin n),
        t ^ (Finset.univ \ S).card •
          PiTensorProduct.map
            (fun i => (S.piecewise (fun _ => f) (fun _ => LinearMap.id) i)) := by
  have h := map_add_expansion n (fun _ => f) (fun _ => t • LinearMap.id)
  simp only at h
  rw [h]
  congr 1
  ext1 S
  exact map_piecewise_smul_factor n f t S

omit [IsAlgClosed k] [Module.Finite k V] in
/-- The S = Finset.univ term gives f⊗ⁿ. -/
private lemma piecewise_univ_eq (f : Module.End k V) :
    (fun i => ((Finset.univ : Finset (Fin n)).piecewise
      (fun _ => f) (fun _ => LinearMap.id) i)) = (fun _ => f) := by
  ext i
  simp [Finset.mem_univ]

omit [IsAlgClosed k] in
/-- Lagrange identity: ∑ᵢ Lᵢ(0) * tᵢ^m = 0^m for m ≤ n. -/
private lemma lagrange_eval_zero_pow
    (v : Fin (n + 1) → k) (hv : Function.Injective v)
    (m : ℕ) (hm : m ≤ n) :
    ∑ i : Fin (n + 1), (Lagrange.basis Finset.univ v i).eval 0 * v i ^ m =
      (0 : k) ^ m := by
  have hv_injOn : Set.InjOn v (Finset.univ : Finset (Fin (n + 1))) := by
    intro a _ b _; exact @hv a b
  have hdeg : (Polynomial.X ^ m : Polynomial k).degree <
      ((Finset.univ : Finset (Fin (n + 1))).card : ℕ) := by
    have h1 := Polynomial.degree_X_pow_le (R := k) m
    have h2 : (m : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast (show m < n + 1 by omega)
    simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt h1 h2
  -- X^m = interpolate at the nodes, evaluated at 0 gives the identity
  have heq := Lagrange.eq_interpolate (f := (Polynomial.X ^ m : Polynomial k)) hv_injOn hdeg
  have heval := congr_arg (Polynomial.eval (0 : k)) heq
  rw [Polynomial.eval_pow, Polynomial.eval_X] at heval
  -- heval : 0 ^ m = (interpolate univ v (fun i => (v i) ^ m)).eval 0
  rw [heval, Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
  congr 1; ext i
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]

/-- The polynomial density argument: for any f ∈ End(V), f⊗ⁿ is in the
linear span of {g⊗ⁿ | g ∈ GL(V)}.

The proof uses multilinear expansion of `PiTensorProduct.map` and
Lagrange interpolation: pick n+1 distinct t where f + t·id is invertible,
expand (f+t·id)⊗ⁿ as a polynomial in t, and use the Lagrange identity
to express f⊗ⁿ as a k-linear combination of the (f+tᵢ·id)⊗ⁿ ∈ GL-image. -/
private lemma endomorphism_tensor_in_glSpan (f : Module.End k V) :
    PiTensorProduct.map (fun (_ : Fin n) => f) ∈
      Submodule.span k (glImage n) := by
  -- The set {t | IsUnit (f + t • id)} is infinite (complement of a finite set)
  have hinv : Set.Infinite {t : k | IsUnit (f + t • LinearMap.id)} := by
    rw [show {t : k | IsUnit (f + t • LinearMap.id)} =
        {t : k | ¬ IsUnit (f + t • LinearMap.id)}ᶜ from by ext; simp]
    exact Set.Finite.infinite_compl (finite_nonUnit_shifts f)
  -- Pick n+1 distinct scalars where f + t • id is invertible
  let e := hinv.natEmbedding
  let v : Fin (n + 1) → k := fun i => (e i.val).val
  have hv_inj : Function.Injective v := by
    intro a b h
    exact Fin.val_injective (e.injective (Subtype.val_injective h))
  have hv_mem : ∀ i : Fin (n + 1), IsUnit (f + v i • LinearMap.id) :=
    fun i => (e i.val).prop
  -- For each such tᵢ, (f + tᵢ • id)⊗ⁿ ∈ glImage ⊆ span(glImage)
  have hgl : ∀ i : Fin (n + 1),
      PiTensorProduct.map (fun (_ : Fin n) => f + v i • LinearMap.id) ∈
        Submodule.span k (glImage n) := by
    intro i
    apply Submodule.subset_span
    have hu := hv_mem i
    -- Build LinearEquiv from the Unit
    let u := hu.unit
    refine ⟨⟨u.val, u.inv, ?_, ?_⟩, ?_⟩
    · intro x; change (u.inv.comp u.val) x = x
      have := u.inv_val; change u.inv * u.val = 1 at this
      exact DFunLike.congr_fun this x
    · intro x; change (u.val.comp u.inv) x = x
      have := u.val_inv; change u.val * u.inv = 1 at this
      exact DFunLike.congr_fun this x
    · change PiTensorProduct.map (fun _ => u.val) =
          PiTensorProduct.map (fun _ => f + v i • LinearMap.id)
      have : u.val = f + v i • LinearMap.id := hu.unit_spec
      simp only [this]
  -- Lagrange coefficients: Lᵢ(0) for each node
  set L : Fin (n + 1) → k := fun i =>
    (Lagrange.basis (Finset.univ : Finset (Fin (n + 1))) v i).eval 0 with hL_def
  -- Key identity: f⊗ⁿ = ∑ᵢ Lᵢ • (f + vᵢ • id)⊗ⁿ
  suffices h : PiTensorProduct.map (fun (_ : Fin n) => f) =
      ∑ i : Fin (n + 1), L i •
        PiTensorProduct.map (fun (_ : Fin n) => f + v i • LinearMap.id) by
    rw [h]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hgl i))
  -- Expand using multilinearity and Lagrange
  simp_rw [tensor_power_expansion n f]
  -- RHS = ∑ᵢ Lᵢ • ∑_S vᵢ^|Sᶜ| • coeffS
  -- Distribute scalar into inner sum
  simp_rw [Finset.smul_sum, smul_smul]
  -- RHS = ∑ᵢ ∑_S (Lᵢ * vᵢ^|Sᶜ|) • coeffS
  -- Swap sums
  rw [Finset.sum_comm]
  -- RHS = ∑_S ∑ᵢ (Lᵢ * vᵢ^|Sᶜ|) • coeffS = ∑_S (∑ᵢ Lᵢ * vᵢ^|Sᶜ|) • coeffS
  simp_rw [← Finset.sum_smul]
  -- Now show: f⊗ⁿ = ∑_S (∑ᵢ Lᵢ * vᵢ^|Sᶜ|) • coeffS
  -- where ∑ᵢ Lᵢ * vᵢ^m = 0^m by Lagrange
  -- For S = univ: |Sᶜ| = 0 and coefficient is 0^0 = 1
  -- For S ≠ univ: |Sᶜ| ≥ 1 and coefficient is 0^|Sᶜ| = 0
  -- Use Finset.sum_eq_single to isolate the S = univ term
  rw [Finset.sum_eq_single Finset.univ]
  · -- The univ term: coefficient is 1, and coeffS = f⊗ⁿ
    simp only [Finset.sdiff_self, Finset.card_empty]
    rw [lagrange_eval_zero_pow n v hv_inj 0 (Nat.zero_le _)]
    simp
  · -- For S ≠ univ: coefficient is 0
    intro S _ hS
    have hne : (Finset.univ \ S).Nonempty :=
      Finset.sdiff_nonempty.mpr (fun h => hS (Finset.eq_univ_of_forall
        (fun x => h (Finset.mem_univ x))))
    have hcard_pos : 0 < (Finset.univ \ S).card := Finset.card_pos.mpr hne
    have hcard_le : (Finset.univ \ S).card ≤ n := by
      calc (Finset.univ \ S).card ≤ Finset.univ.card := Finset.card_le_card Finset.sdiff_subset
        _ = n := by simp [Finset.card_univ, Fintype.card_fin]
    rw [lagrange_eval_zero_pow n v hv_inj _ hcard_le]
    simp [zero_pow hcard_pos.ne']
  · -- univ ∈ Finset.univ
    intro h; exact absurd (Finset.mem_univ _) h

end Etingof.Proposition5_19_1_aux

/-- The image of GL(V) in End(V⊗ⁿ) spans the centralizer algebra B of the
Sₙ-action on V⊗ⁿ. Specifically, the linear span of {g⊗ⁿ | g ∈ GL(V)}
(where g⊗ⁿ acts as g on each tensor factor) equals the full diagonal
action subalgebra generated by all of End(V), as a submodule.

This is a consequence of the polynomial density argument: if a polynomial
p(t) = det(f + t·id) vanishes for all t, then f is not invertible, but
the set of invertible operators is Zariski-dense in End(V), so the span
of {g⊗ⁿ | g ∈ GL(V)} equals the span of {f⊗ⁿ | f ∈ End(V)}.
(Etingof Proposition 5.19.1) -/
theorem Etingof.Proposition5_19_1
    {k : Type*} [Field k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    -- The linear span of {g⊗ⁿ | g ∈ GL(V)} equals the diagonal action image
    Submodule.span k (Set.range fun (g : V ≃ₗ[k] V) =>
      PiTensorProduct.map (fun (_ : Fin n) => g.toLinearMap)) =
    (diagonalActionImage k V n).toSubmodule := by
  open Etingof.Proposition5_19_1_aux in
  apply le_antisymm
  · -- ⊆: GL-span ≤ diagonalActionImage.toSubmodule
    -- Each g⊗ⁿ is in the End-image generating set, hence in Algebra.adjoin
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact Algebra.subset_adjoin ⟨g.toLinearMap, rfl⟩
  · -- ⊇: diagonalActionImage.toSubmodule ≤ GL-span
    -- Step 1: diagonalActionImage.toSubmodule = span(endImage)
    -- This uses the fact that endImage is closed under * and contains 1
    have h_adjoin_eq : (diagonalActionImage k V n).toSubmodule =
        Submodule.span k (endImage n) := by
      apply Algebra.adjoin_eq_span_of_subset
      intro x hx
      have hx_mem : x ∈ endImage (k := k) (V := V) n := by
        induction hx using Submonoid.closure_induction with
        | mem y hy => exact hy
        | one => exact one_mem_endImage n
        | mul _ _ _ _ ihx ihy => exact endImage_mul_closed n _ ihx _ ihy
      exact Submodule.subset_span hx_mem
    rw [h_adjoin_eq]
    -- Step 2: span(endImage) ≤ span(glImage) by density
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact endomorphism_tensor_in_glSpan n f

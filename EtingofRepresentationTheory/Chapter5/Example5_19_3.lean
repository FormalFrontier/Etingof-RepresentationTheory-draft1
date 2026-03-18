import EtingofRepresentationTheory.Chapter5.Theorem5_18_4

/-!
# Example 5.19.3: Schur Functors for Special Partitions

If λ = (n), then Lλ = SⁿV (symmetric power).
If λ = (1ⁿ), then Lλ = ∧ⁿV (exterior power).
These are irreducible GL(V)-representations (except ∧ⁿV = 0 when n > dim V).

## Mathlib correspondence

Uses `Mathlib.LinearAlgebra.ExteriorAlgebra` and symmetric powers.
-/

open scoped TensorProduct
open Etingof

variable (k : Type*) [Field k]
  (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- The Sₙ-invariant submodule of V⊗ⁿ: tensors fixed by all permutations.
These are the symmetric tensors, i.e., the subspace where σ · x = x for all σ ∈ Sₙ. -/
noncomputable def Etingof.symInvariants :
    Submodule k (TensorPower k V n) :=
  ⨅ σ : Equiv.Perm (Fin n),
    LinearMap.ker ((symGroupAction k V n σ).toLinearMap - LinearMap.id)

/-- The Sₙ-antisymmetric submodule of V⊗ⁿ: tensors where σ · x = sign(σ) · x
for all σ ∈ Sₙ. These are the alternating tensors. -/
noncomputable def Etingof.symAntisymmetric :
    Submodule k (TensorPower k V n) :=
  ⨅ σ : Equiv.Perm (Fin n),
    LinearMap.ker ((symGroupAction k V n σ).toLinearMap -
      ((Equiv.Perm.sign σ : ℤ) : k) • LinearMap.id)

namespace Etingof

section SymHelpers

variable {k : Type} [Field k]
  {V : Type} [AddCommGroup V] [Module k V]
  {n : ℕ}

private lemma mem_symInvariants_iff (x : TensorPower k V n) :
    x ∈ symInvariants k V n ↔ ∀ σ : Equiv.Perm (Fin n), symGroupAction k V n σ x = x := by
  simp only [symInvariants, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_zero]

private lemma mk_symGroupAction_eq (σ : Equiv.Perm (Fin n)) (x : TensorPower k V n) :
    SymmetricPower.mk k (Fin n) V (symGroupAction k V n σ x) =
    SymmetricPower.mk k (Fin n) V x := by
  have : (SymmetricPower.mk k (Fin n) V).comp (symGroupAction k V n σ).toLinearMap =
      SymmetricPower.mk k (Fin n) V := by
    ext f
    simp only [LinearMap.comp_apply, LinearMap.coe_compMultilinearMap, Function.comp_apply,
      LinearEquiv.coe_coe, symGroupAction, PiTensorProduct.reindex_tprod]
    show SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k fun i => f (σ.symm i)) =
      SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k f)
    change (⨂ₛ[k] i, f (σ.symm i)) = ⨂ₛ[k] i, f i
    exact SymmetricPower.tprod_equiv σ.symm f
  exact LinearMap.congr_fun this x

/-- The symmetrization sum: Σ_σ σ · x (without 1/n! factor). -/
private noncomputable def symSum : TensorPower k V n →ₗ[k] TensorPower k V n :=
  ∑ σ : Equiv.Perm (Fin n), (symGroupAction k V n σ).toLinearMap

private lemma symSum_apply (x : TensorPower k V n) :
    symSum x = ∑ σ : Equiv.Perm (Fin n), symGroupAction k V n σ x := by
  simp [symSum, LinearMap.sum_apply]

private lemma symGroupAction_comp (σ τ : Equiv.Perm (Fin n)) (x : TensorPower k V n) :
    symGroupAction k V n τ (symGroupAction k V n σ x) =
    symGroupAction k V n (σ.trans τ) x := by
  -- Prove as linear maps are equal on tprod generators
  have h : ((symGroupAction k V n τ).toLinearMap.comp
      (symGroupAction k V n σ).toLinearMap) =
    (symGroupAction k V n (σ.trans τ)).toLinearMap := by
    ext f
    simp [symGroupAction, PiTensorProduct.reindex_tprod]
  exact LinearMap.congr_fun h x

private lemma symSum_symGroupAction (e : Equiv.Perm (Fin n)) (x : TensorPower k V n) :
    symSum (symGroupAction k V n e x) = symSum x := by
  simp only [symSum_apply]
  simp_rw [symGroupAction_comp e _ x]
  -- Now goal: ∑ σ, symGroupAction (e.trans σ) x = ∑ σ, symGroupAction σ x
  -- e.trans σ = σ * e in Perm. As σ varies, so does σ * e (right mult bijection).
  -- Use Equiv.mulRight e as the reindexing
  exact Fintype.sum_equiv (Equiv.mulRight e) _ _
    (fun σ => by simp [Equiv.Perm.mul_def, Equiv.trans])

private lemma mk_comp_symSum :
    (SymmetricPower.mk k (Fin n) V).comp symSum =
    (Fintype.card (Equiv.Perm (Fin n)) : k) • SymmetricPower.mk k (Fin n) V := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.coe_compMultilinearMap,
    Function.comp_apply, symSum_apply]
  rw [map_sum]
  simp only [mk_symGroupAction_eq, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul k]

private lemma mk_symSum (x : TensorPower k V n) :
    SymmetricPower.mk k (Fin n) V (symSum x) =
    (Fintype.card (Equiv.Perm (Fin n)) : k) • SymmetricPower.mk k (Fin n) V x :=
  LinearMap.congr_fun mk_comp_symSum x

private lemma symSum_of_mem_symInvariants (x : TensorPower k V n)
    (hx : x ∈ symInvariants k V n) :
    symSum x = (Fintype.card (Equiv.Perm (Fin n)) : k) • x := by
  rw [symSum_apply]
  simp only [(mem_symInvariants_iff x).mp hx, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul k]

private lemma symSum_mem_symInvariants (x : TensorPower k V n) :
    symSum x ∈ symInvariants k V n := by
  rw [mem_symInvariants_iff]
  intro τ
  simp only [symSum_apply, map_sum]
  simp_rw [symGroupAction_comp _ τ]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => by simp [Equiv.Perm.mul_def])

private lemma symSum_rel :
    ∀ a b, SymmetricPower.Rel k (Fin n) V a b → symSum a = symSum b := by
  intro a b hab
  cases hab with
  | perm e f =>
    -- tprod(f ∘ e) = reindex(e⁻¹)(tprod f), so use symSum_symGroupAction
    have : PiTensorProduct.tprod k (fun i => f (e i)) =
        symGroupAction k V n e⁻¹ (PiTensorProduct.tprod k f) := by
      simp [symGroupAction, PiTensorProduct.reindex_tprod, Equiv.Perm.inv_def]
    rw [this, symSum_symGroupAction]

private lemma ker_mk_le_ker_symSum :
    LinearMap.ker (SymmetricPower.mk k (Fin n) V) ≤ LinearMap.ker symSum := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  -- Build an AddCon from symSum's kernel
  let c : AddCon (⨂[k] (_ : Fin n), V) := AddCon.ker symSum.toAddMonoidHom
  have hle : addConGen (SymmetricPower.Rel k (Fin n) V) ≤ c :=
    AddCon.addConGen_le (fun a b h => symSum_rel a b h)
  -- mk x = 0 means x ≡ 0 mod addConGen(Rel)
  have hrel : (addConGen (SymmetricPower.Rel k (Fin n) V)) x 0 := by
    have hmk : (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) V))) x =
        (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) V))) 0 := by
      change SymmetricPower.mk k (Fin n) V x = SymmetricPower.mk k (Fin n) V 0
      rw [hx, map_zero]
    exact (AddCon.eq _).mp hmk
  -- c x 0 means symSum x = symSum 0 = 0
  have h := hle hrel
  change symSum x = symSum 0 at h
  rwa [map_zero] at h

private lemma perm_card_eq_factorial :
    (Fintype.card (Equiv.Perm (Fin n)) : k) = (n.factorial : k) := by
  simp [Fintype.card_perm]

end SymHelpers

section AltHelpers

variable {k : Type} [Field k]
  {V : Type} [AddCommGroup V] [Module k V]
  {n : ℕ}

private lemma mem_symAntisymmetric_iff (x : TensorPower k V n) :
    x ∈ symAntisymmetric k V n ↔
      ∀ σ : Equiv.Perm (Fin n),
        symGroupAction k V n σ x = ((Equiv.Perm.sign σ : ℤ) : k) • x := by
  simp only [symAntisymmetric, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

/-- The alternating sum: Σ_σ sign(σ) · σ · x. -/
private noncomputable def altSum : TensorPower k V n →ₗ[k] TensorPower k V n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) • (symGroupAction k V n σ).toLinearMap

private lemma altSum_apply (x : TensorPower k V n) :
    altSum x = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : k) • symGroupAction k V n σ x := by
  simp [altSum, LinearMap.sum_apply, LinearMap.smul_apply]

private lemma sign_sq (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : k) * ((Equiv.Perm.sign σ : ℤ) : k) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

private lemma sign_symm_eq_sign (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ.symm : ℤ) : k) = ((Equiv.Perm.sign σ : ℤ) : k) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [h, Equiv.Perm.sign_symm, Equiv.Perm.sign_inv]

private lemma sign_inv_mul (τ ρ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign (τ⁻¹ * ρ) : ℤ) : k) =
      ((Equiv.Perm.sign τ : ℤ) : k) * ((Equiv.Perm.sign ρ : ℤ) : k) := by
  rw [map_mul, Units.val_mul, Int.cast_mul]
  congr 1
  exact sign_symm_eq_sign τ

private lemma altSum_of_mem_symAntisymmetric (x : TensorPower k V n)
    (hx : x ∈ symAntisymmetric k V n) :
    altSum x = (Fintype.card (Equiv.Perm (Fin n)) : k) • x := by
  rw [altSum_apply]
  simp only [(mem_symAntisymmetric_iff x).mp hx, smul_smul, sign_sq, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul k]

private lemma altSum_mem_symAntisymmetric (x : TensorPower k V n) :
    altSum x ∈ symAntisymmetric k V n := by
  rw [mem_symAntisymmetric_iff]
  intro τ
  rw [altSum_apply, map_sum]
  simp_rw [LinearMapClass.map_smul, symGroupAction_comp _ τ]
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft τ)
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : k) • symGroupAction k V n (σ.trans τ) x)
    (fun ρ => (((Equiv.Perm.sign τ : ℤ) : k) * ((Equiv.Perm.sign ρ : ℤ) : k)) •
      symGroupAction k V n ρ x)
    (fun ρ => ?_)
  dsimp only
  -- ρ.trans τ = τ * ρ (in Perm, a.trans b = b * a)
  rw [show ρ.trans τ = τ * ρ from (Equiv.Perm.mul_def τ ρ).symm]
  -- sign(ρ) = sign(τ) * sign(τ * ρ): since sign(τ * ρ) = sign(τ) * sign(ρ)
  -- so sign(τ) * sign(τ * ρ) = sign(τ)² * sign(ρ) = sign(ρ)
  congr 1
  simp only [Equiv.coe_mulLeft]
  rw [map_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, sign_sq, one_mul]

/-- The projection from tensor power to exterior power, via PiTensorProduct.lift of ιMulti. -/
private noncomputable def π : TensorPower k V n →ₗ[k] ↥(⋀[k]^n V) :=
  PiTensorProduct.lift (exteriorPower.ιMulti k n (M := V)).toMultilinearMap

private lemma π_tprod (v : Fin n → V) :
    π (PiTensorProduct.tprod k v) = exteriorPower.ιMulti k n v := by
  simp [π, PiTensorProduct.lift.tprod]

private lemma π_symGroupAction (σ : Equiv.Perm (Fin n)) (x : TensorPower k V n) :
    π (symGroupAction k V n σ x) = ((Equiv.Perm.sign σ : ℤ) : k) • π x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [symGroupAction, PiTensorProduct.reindex_tprod, map_smul, π_tprod]
    -- Goal: r • ιMulti(fun i => v (σ.symm i)) = ↑↑(sign σ) • r • ιMulti v
    -- Use map_perm: ιMulti(v ∘ σ.symm) = sign(σ.symm) • ιMulti v (ℤˣ-action)
    -- Need to convert ℤˣ-smul to k-smul
    conv_lhs => rw [show (fun i => v (σ.symm i)) = v ∘ ⇑σ.symm from rfl]
    rw [(exteriorPower.ιMulti k n).map_perm (v) σ.symm]
    -- Now LHS: r • sign(σ.symm) • ιMulti v
    -- Convert ℤˣ-smul: sign(σ.symm) • x = ((sign(σ.symm) : ℤ) : k) • x
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k, sign_symm_eq_sign, smul_comm]
  | add x y hx hy => simp [map_add, hx, hy, smul_add]

/-- altSum = toTensorPower ∘ π as linear maps on TensorPower. -/
private lemma altSum_eq_toTensorPower_comp_π :
    altSum = (exteriorPower.toTensorPower k V n).comp π := by
  apply PiTensorProduct.ext
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    altSum_apply, π_tprod, exteriorPower.toTensorPower_apply_ιMulti]
  -- LHS: ∑ σ, ↑↑(sign σ) • symGroupAction σ (tprod v)
  -- RHS: ∑ σ, sign σ • tprod (v ∘ σ)
  -- Unfold symGroupAction on tprod: symGroupAction σ (tprod v) = tprod (v ∘ σ⁻¹)
  simp only [symGroupAction, PiTensorProduct.reindex_tprod]
  -- Now LHS: ∑ σ, ↑↑(sign σ) • tprod (v ∘ σ.symm)
  -- Reindex σ ↦ σ⁻¹, convert ℤˣ-smul to k-smul
  conv_rhs => arg 2; ext σ; rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
  refine Fintype.sum_equiv (Equiv.inv _)
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : k) • (PiTensorProduct.tprod k) (fun i => v (σ.symm i)))
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : k) • (PiTensorProduct.tprod k) (fun i => v (σ i)))
    (fun σ => ?_)
  simp only [Equiv.inv_apply, Equiv.Perm.inv_def]
  rw [sign_symm_eq_sign]

/-- π ∘ toTensorPower = n! • id on ⋀^n V. -/
private lemma π_comp_toTensorPower :
    π.comp (exteriorPower.toTensorPower k V n) =
    (Fintype.card (Equiv.Perm (Fin n)) : k) • LinearMap.id := by
  rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (exteriorPower.ιMulti_span k n V)]
  intro ⟨_, v, rfl⟩
  simp only [Set.mem_range, LinearMap.comp_apply, exteriorPower.toTensorPower_apply_ιMulti,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [map_sum]
  -- Convert ℤˣ-smul to k-smul inside the sum
  simp only [LinearMapClass.map_smul, Units.smul_def, ← Int.cast_smul_eq_zsmul k, π_tprod]
  -- Each term: ↑↑(sign σ) • ιMulti(v ∘ σ) = ↑↑(sign σ) • ↑↑(sign σ) • ιMulti(v) = ιMulti(v)
  simp_rw [show ∀ σ : Equiv.Perm (Fin n), (fun i => v (σ i)) = v ∘ ⇑σ from fun _ => rfl]
  simp_rw [(exteriorPower.ιMulti k n).map_perm v, Units.smul_def, ← Int.cast_smul_eq_zsmul k,
    smul_smul, sign_sq, one_smul, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul k]

/-- π is surjective from TensorPower to ⋀^n V. -/
private lemma π_surjective : Function.Surjective (π (k := k) (V := V) (n := n)) := by
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff, ← exteriorPower.ιMulti_span k n V]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  exact ⟨PiTensorProduct.tprod k v, π_tprod v⟩

end AltHelpers

/-- For the partition λ = (n), the Schur functor L_{(n)} equals SⁿV
(the n-th symmetric power). Specifically, the Sₙ-invariant subspace of
V⊗ⁿ (symmetric tensors, where σ · x = x for all σ) is isomorphic to
the n-th symmetric power Sym[k]^n V.

The GL(V)-action on SⁿV is given by g · (v₁ ⊙ ... ⊙ vₙ) = (gv₁) ⊙ ... ⊙ (gvₙ).
(Etingof Example 5.19.3) -/
theorem Example5_19_3_symmetric
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (symInvariants k V n ≃ₗ[k] SymmetricPower k (Fin n) V) := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : k) ≠ 0 := by
    simp [Fintype.card_perm, Nat.factorial_ne_zero]
  let f : ↥(symInvariants k V n) →ₗ[k] SymmetricPower k (Fin n) V :=
    (SymmetricPower.mk k (Fin n) V).comp (symInvariants k V n).subtype
  exact ⟨LinearEquiv.ofBijective f ⟨fun a b hab => by
    ext1
    have hmk : SymmetricPower.mk k (Fin n) V (a.1 - b.1) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hab
    have hmem : a.1 - b.1 ∈ symInvariants k V n := sub_mem a.2 b.2
    have h1 : symSum (a.1 - b.1) = 0 :=
      ker_mk_le_ker_symSum (LinearMap.mem_ker.mpr hmk)
    have h2 : symSum (a.1 - b.1) = (Fintype.card (Equiv.Perm (Fin n)) : k) • (a.1 - b.1) :=
      symSum_of_mem_symInvariants _ hmem
    rw [h2] at h1
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hcard),
  fun y => by
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp (SymmetricPower.range_mk k (Fin n) V) y
    refine ⟨⟨(Fintype.card (Equiv.Perm (Fin n)) : k)⁻¹ • symSum x,
      Submodule.smul_mem _ _ (symSum_mem_symInvariants x)⟩, ?_⟩
    simp only [f, LinearMap.comp_apply, Submodule.coe_subtype, map_smul,
      mk_symSum, smul_smul, inv_mul_cancel₀ hcard, one_smul, hx]⟩⟩

/-- For the partition λ = (1ⁿ), the Schur functor L_{(1ⁿ)} equals ∧ⁿV
(the n-th exterior power), which is zero when n > dim V.

The Sₙ-antisymmetric subspace of V⊗ⁿ (alternating tensors, where
σ · x = sign(σ) · x for all σ) is isomorphic to the n-th exterior
power ⋀[k]^n V.

The GL(V)-action on ∧ⁿV is given by g · (v₁ ∧ ... ∧ vₙ) = (gv₁) ∧ ... ∧ (gvₙ).
(Etingof Example 5.19.3) -/
theorem Example5_19_3_exterior
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (symAntisymmetric k V n ≃ₗ[k] ⋀[k]^n V) := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : k) ≠ 0 := by
    simp [Fintype.card_perm, Nat.factorial_ne_zero]
  let f : ↥(symAntisymmetric k V n) →ₗ[k] ↥(⋀[k]^n V) :=
    π.comp (symAntisymmetric k V n).subtype
  exact ⟨LinearEquiv.ofBijective f ⟨fun a b hab => by
    -- Injectivity: π(a) = π(b) → a = b
    ext1
    have hπ : π (a.1 - b.1) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hab
    -- altSum(a-b) = toTensorPower(π(a-b)) = toTensorPower(0) = 0
    have h1 : altSum (a.1 - b.1) = 0 := by
      rw [altSum_eq_toTensorPower_comp_π, LinearMap.comp_apply, hπ, map_zero]
    -- altSum(a-b) = n! • (a-b) since a-b ∈ symAntisymmetric
    have h2 : altSum (a.1 - b.1) = (Fintype.card (Equiv.Perm (Fin n)) : k) • (a.1 - b.1) :=
      altSum_of_mem_symAntisymmetric _ (sub_mem a.2 b.2)
    rw [h2] at h1
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hcard),
  fun y => by
    -- Surjectivity: find x ∈ symAntisymmetric with π(x) = y
    obtain ⟨z, hz⟩ := π_surjective y
    -- Take (n!)⁻¹ • altSum(z), which is in symAntisymmetric
    refine ⟨⟨(Fintype.card (Equiv.Perm (Fin n)) : k)⁻¹ • altSum z,
      Submodule.smul_mem _ _ (altSum_mem_symAntisymmetric z)⟩, ?_⟩
    -- π((n!)⁻¹ • altSum(z)) = (n!)⁻¹ • π(altSum(z))
    -- = (n!)⁻¹ • π(toTensorPower(π(z)))   [by altSum = toTensorPower ∘ π]
    -- = (n!)⁻¹ • n! • π(z)                 [by π ∘ toTensorPower = n! • id]
    -- = π(z) = y
    simp only [f, LinearMap.comp_apply, Submodule.coe_subtype, map_smul]
    rw [altSum_eq_toTensorPower_comp_π, LinearMap.comp_apply, hz]
    rw [show π ((exteriorPower.toTensorPower k V n) y) =
        (Fintype.card (Equiv.Perm (Fin n)) : k) • y from
      LinearMap.congr_fun π_comp_toTensorPower y]
    rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]⟩⟩

end Etingof

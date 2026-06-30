import EtingofRepresentationTheory.Chapter5.Theorem5_18_4
import EtingofRepresentationTheory.Chapter5.ExteriorIrreducible

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
    -- v4.31: `AddCon.addConGen_le` is now an `Iff`.
    AddCon.addConGen_le.mpr (fun a b h => symSum_rel a b h)
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
  -- v4.31: `dsimp only` here now makes no progress; the goal is already reduced.
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

-- rc4: instance search for `AddZeroClass ↥(⋀[k]^n V)` in the `add` case now exceeds
-- the default 20000; bump the synthesis budget.
set_option synthInstance.maxHeartbeats 40000 in
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
  -- v4.31: `Equiv.inv_apply` no longer fires; rewrite `(Equiv.inv _) σ` to `σ.symm`
  -- via `Equiv.Perm.inv_def`, then use `sign σ⁻¹ = sign σ`.
  show ((Equiv.Perm.sign σ : ℤ) : k) • (PiTensorProduct.tprod k) (fun i => v (σ.symm i)) =
      ((Equiv.Perm.sign σ⁻¹ : ℤ) : k) • (PiTensorProduct.tprod k) (fun i => v (σ⁻¹ i))
  rw [Equiv.Perm.inv_def, sign_symm_eq_sign]

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

/-! ### GL(V)-equivariance infrastructure

The book asserts that `L_{(n)} = SⁿV` and `L_{(1ⁿ)} = ∧ⁿV` as `GL(V)`-representations,
not merely as `k`-vector spaces. We capture the equivariance by exhibiting, for every
linear endomorphism `g : V →ₗ V` (in particular every `g ∈ GL(V)`), the *natural*
diagonal action `g ⊗ ⋯ ⊗ g` on `V⊗ⁿ`, showing it preserves the symmetric and
antisymmetric subspaces, and showing the isomorphisms intertwine it with the functorial
actions `symmetricPowerMap g` on `SⁿV` and `exteriorPower.map n g` on `∧ⁿV`. -/

section Equivariance

variable {k : Type} [Field k]
  {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
  {n : ℕ}

/-- The functorial action of a linear endomorphism `g : V →ₗ V` on the symmetric power
`SⁿV`, induced from the diagonal action `g ⊗ ⋯ ⊗ g` on `V⊗ⁿ` by descending through the
quotient map `mk`. Restricting `g` to `GL(V)` makes `SⁿV` a `GL(V)`-representation. -/
noncomputable def symmetricPowerMap (g : V →ₗ[k] V) :
    SymmetricPower k (Fin n) V →ₗ[k] SymmetricPower k (Fin n) V :=
  let F : TensorPower k V n →+ SymmetricPower k (Fin n) V :=
    (AddCon.mk' _).comp (PiTensorProduct.map (fun _ : Fin n => g)).toAddMonoidHom
  { toFun := AddCon.lift _ F (fun x y h => Quotient.sound (by
        induction h with
        | of x y h => cases h with
          | perm e f =>
            simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.map_tprod]
            exact AddConGen.Rel.of _ _ (SymmetricPower.Rel.perm e (fun i => g (f i)))
        | refl => exact AddCon.refl _ _
        | symm _ ih => exact AddCon.symm _ ih
        | trans _ _ ih₁ ih₂ => exact AddCon.trans _ ih₁ ih₂
        | add _ _ ih₁ ih₂ => simp only [map_add]; exact AddCon.add _ ih₁ ih₂))
    map_add' := fun x y => by
      refine AddCon.induction_on₂ x y (fun a b => ?_)
      change SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) (a + b))
        = SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) a)
        + SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) b)
      rw [map_add, map_add]
    map_smul' := fun r x => by
      refine AddCon.induction_on x (fun a => ?_)
      change SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) (r • a))
        = r • SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) a)
      rw [map_smul, map_smul] }

omit [Module.Finite k V] in
@[simp] lemma symmetricPowerMap_mk (g : V →ₗ[k] V) (x : TensorPower k V n) :
    symmetricPowerMap g (SymmetricPower.mk k (Fin n) V x) =
      SymmetricPower.mk k (Fin n) V (PiTensorProduct.map (fun _ : Fin n => g) x) :=
  rfl

/-- The diagonal action `g ⊗ ⋯ ⊗ g` preserves the symmetric (`Sₙ`-invariant) subspace,
because it commutes with the permutation operators. -/
lemma symInvariants_map_mem (g : V →ₗ[k] V) {x : TensorPower k V n}
    (hx : x ∈ symInvariants k V n) :
    PiTensorProduct.map (fun _ : Fin n => g) x ∈ symInvariants k V n := by
  rw [mem_symInvariants_iff] at hx ⊢
  intro σ
  have hcomm := LinearMap.congr_fun (symGroupAction_comm_diagonalAction k V n σ g) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcomm
  rw [hcomm, hx σ]

/-- The diagonal action `g ⊗ ⋯ ⊗ g` preserves the antisymmetric subspace, because it
commutes with the permutation operators (so it scales by `sign σ` exactly as before). -/
lemma symAntisymmetric_map_mem (g : V →ₗ[k] V) {x : TensorPower k V n}
    (hx : x ∈ symAntisymmetric k V n) :
    PiTensorProduct.map (fun _ : Fin n => g) x ∈ symAntisymmetric k V n := by
  rw [mem_symAntisymmetric_iff] at hx ⊢
  intro σ
  have hcomm := LinearMap.congr_fun (symGroupAction_comm_diagonalAction k V n σ g) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcomm
  rw [hcomm, hx σ, map_smul]

omit [Module.Finite k V] in
/-- The projection `π : V⊗ⁿ → ∧ⁿV` is natural in `V`: it intertwines the diagonal action
`g ⊗ ⋯ ⊗ g` with the functorial action `exteriorPower.map n g`. -/
lemma π_map (g : V →ₗ[k] V) (x : TensorPower k V n) :
    π (PiTensorProduct.map (fun _ : Fin n => g) x) = exteriorPower.map n g (π x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, PiTensorProduct.map_tprod, π_tprod, exteriorPower.map_apply_ιMulti,
      Function.comp_def]
  | add x y hx hy => simp only [map_add, hx, hy]

end Equivariance

/-- The explicit isomorphism `L_{(n)} ≅ SⁿV`: the `Sₙ`-invariant subspace of `V⊗ⁿ`
(symmetric tensors, where `σ · x = x` for all `σ`) maps isomorphically onto the `n`-th
symmetric power `Sym[k]^n V` via the canonical quotient map `mk`. -/
noncomputable def Example5_19_3_symmetricEquiv
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    symInvariants k V n ≃ₗ[k] SymmetricPower k (Fin n) V := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : k) ≠ 0 := by
    simp [Fintype.card_perm, Nat.factorial_ne_zero]
  exact LinearEquiv.ofBijective
    ((SymmetricPower.mk k (Fin n) V).comp (symInvariants k V n).subtype)
    ⟨fun a b hab => by
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
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, map_smul,
        mk_symSum, smul_smul, inv_mul_cancel₀ hcard, one_smul, hx]⟩

@[simp] lemma Example5_19_3_symmetricEquiv_apply
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (x : symInvariants k V n) :
    Example5_19_3_symmetricEquiv n x = SymmetricPower.mk k (Fin n) V x.val :=
  rfl

/-- For the partition λ = (n), the Schur functor L_{(n)} equals SⁿV
(the n-th symmetric power). Specifically, the Sₙ-invariant subspace of
V⊗ⁿ (symmetric tensors, where σ · x = x for all σ) is isomorphic to
the n-th symmetric power Sym[k]^n V.

The GL(V)-action on SⁿV is given by g · (v₁ ⊙ ... ⊙ vₙ) = (gv₁) ⊙ ... ⊙ (gvₙ);
see `Example5_19_3_symmetric_equivariant` for the equivariance of this isomorphism.
(Etingof Example 5.19.3) -/
theorem Example5_19_3_symmetric
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (symInvariants k V n ≃ₗ[k] SymmetricPower k (Fin n) V) :=
  ⟨Example5_19_3_symmetricEquiv n⟩

/-- The diagonal `GL(V)`-action `g ⊗ ⋯ ⊗ g` restricted to the `Sₙ`-invariant subspace. -/
noncomputable def symInvariantsMap
    {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] {n : ℕ}
    (g : V →ₗ[k] V) : symInvariants k V n →ₗ[k] symInvariants k V n :=
  (PiTensorProduct.map (fun _ : Fin n => g)).restrict (fun _ hx => symInvariants_map_mem g hx)

/-- The isomorphism `L_{(n)} ≅ SⁿV` is `GL(V)`-equivariant: for every `g : V →ₗ V`
(in particular every `g ∈ GL(V)`) it intertwines the diagonal action on the symmetric
tensors with the functorial action `symmetricPowerMap g` on `SⁿV`. This upgrades the
bare `k`-linear isomorphism to an isomorphism of `GL(V)`-representations. -/
theorem Example5_19_3_symmetric_equivariant
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (g : V →ₗ[k] V) (x : symInvariants k V n) :
    Example5_19_3_symmetricEquiv n (symInvariantsMap g x) =
      symmetricPowerMap g (Example5_19_3_symmetricEquiv n x) := by
  simp only [Example5_19_3_symmetricEquiv_apply, symmetricPowerMap_mk, symInvariantsMap,
    LinearMap.coe_restrict_apply]

/-- The explicit isomorphism `L_{(1ⁿ)} ≅ ∧ⁿV`: the `Sₙ`-antisymmetric subspace of `V⊗ⁿ`
(alternating tensors, where `σ · x = sign(σ) · x` for all `σ`) maps isomorphically onto
the `n`-th exterior power `⋀[k]^n V` via the antisymmetrizing projection `π`. -/
noncomputable def Example5_19_3_exteriorEquiv
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    symAntisymmetric k V n ≃ₗ[k] ⋀[k]^n V := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : k) ≠ 0 := by
    simp [Fintype.card_perm, Nat.factorial_ne_zero]
  exact LinearEquiv.ofBijective
    (π.comp (symAntisymmetric k V n).subtype)
    ⟨fun a b hab => by
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
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, map_smul]
      rw [altSum_eq_toTensorPower_comp_π, LinearMap.comp_apply, hz]
      rw [show π ((exteriorPower.toTensorPower k V n) y) =
          (Fintype.card (Equiv.Perm (Fin n)) : k) • y from
        LinearMap.congr_fun π_comp_toTensorPower y]
      rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]⟩

@[simp] lemma Example5_19_3_exteriorEquiv_apply
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (x : symAntisymmetric k V n) :
    Example5_19_3_exteriorEquiv n x = π x.val :=
  rfl

/-- For the partition λ = (1ⁿ), the Schur functor L_{(1ⁿ)} equals ∧ⁿV
(the n-th exterior power), which is zero when n > dim V.

The Sₙ-antisymmetric subspace of V⊗ⁿ (alternating tensors, where
σ · x = sign(σ) · x for all σ) is isomorphic to the n-th exterior
power ⋀[k]^n V.

The GL(V)-action on ∧ⁿV is given by g · (v₁ ∧ ... ∧ vₙ) = (gv₁) ∧ ... ∧ (gvₙ);
see `Example5_19_3_exterior_equivariant` for the equivariance of this isomorphism.
(Etingof Example 5.19.3) -/
theorem Example5_19_3_exterior
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    Nonempty (symAntisymmetric k V n ≃ₗ[k] ⋀[k]^n V) :=
  ⟨Example5_19_3_exteriorEquiv n⟩

/-- The diagonal `GL(V)`-action `g ⊗ ⋯ ⊗ g` restricted to the antisymmetric subspace. -/
noncomputable def symAntisymmetricMap
    {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] {n : ℕ}
    (g : V →ₗ[k] V) : symAntisymmetric k V n →ₗ[k] symAntisymmetric k V n :=
  (PiTensorProduct.map (fun _ : Fin n => g)).restrict (fun _ hx => symAntisymmetric_map_mem g hx)

/-- The isomorphism `L_{(1ⁿ)} ≅ ∧ⁿV` is `GL(V)`-equivariant: for every `g : V →ₗ V`
(in particular every `g ∈ GL(V)`) it intertwines the diagonal action on the antisymmetric
tensors with the functorial action `exteriorPower.map n g` on `∧ⁿV`. This upgrades the
bare `k`-linear isomorphism to an isomorphism of `GL(V)`-representations. -/
theorem Example5_19_3_exterior_equivariant
    {k : Type} [Field k] [CharZero k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (g : V →ₗ[k] V) (x : symAntisymmetric k V n) :
    Example5_19_3_exteriorEquiv n (symAntisymmetricMap g x) =
      exteriorPower.map n g (Example5_19_3_exteriorEquiv n x) := by
  simp only [Example5_19_3_exteriorEquiv_apply, symAntisymmetricMap, LinearMap.coe_restrict_apply]
  exact π_map g x.val

/-! ### Irreducibility (Problem 4.12.3)

The book closes Example 5.19.3 by asserting that `L_{(n)} = SⁿV` and `L_{(1ⁿ)} = ∧ⁿV` are
*irreducible* `GL(V)`-representations, "except that `∧ⁿV` is zero if `n > dim V`", citing
Problem 4.12.3 for the irreducibility.

Three pieces of that final sentence:

* The parenthetical vanishing `∧ⁿV = 0` for `n > dim V` is proved below
  (`Example5_19_3_exterior_subsingleton_of_dim_lt`): a genuine, complete result.

* **The exterior half is now fully proved** (`Example5_19_3_exterior_irreducible`, via
  `Etingof.exteriorPower_eq_bot_or_top` in `Chapter5.ExteriorIrreducible`). The reusable heart of
  Problem 4.12.3 — "an invariant subspace of a diagonal operator with pairwise distinct eigenvalues
  is spanned by a subset of the eigenbasis", and "connectivity of the eigenbasis under the group
  forces irreducibility" — is packaged abstractly in `Chapter5.DiagonalCoordinate`. For `∧ⁿV` the
  diagonal element `diag(2^(2⁰), …, 2^(2^{d-1}))` has distinct eigenvalues on `Module.Basis.exteriorPower`,
  and the permutation matrices (transitive on `n`-subsets) supply the connectivity.

* **The symmetric half (`Example5_19_3_symmetric_irreducible`) remains open.** The same
  `DiagonalCoordinate` criterion applies, but it requires a *monomial basis of `SⁿV`* indexed by
  degree-`n` monomials — which is **absent from Mathlib** (only the exterior basis
  `Module.Basis.exteriorPower` exists; the symmetric-power universal property is a Mathlib TODO).
  Permutations are *not* transitive on monomials, so the connectivity genuinely needs the
  transvections `ρ(1 + E_{ij})` of the book's Hint. Building that basis and the transvection
  connectivity is the remaining work; the criterion is ready to consume them.

The symmetric claim is pinned below as a `Prop`-valued definition referencing the actual
`GL(V)`-action (`symmetricPowerMap` on `SⁿV`): a subrepresentation is a submodule stable under
every `g ∈ GL(V)` (`g : V ≃ₗ[k] V`); irreducibility says the only such submodules are `⊥` and `⊤`. -/

/-- Book fidelity (Example 5.19.3, parenthetical): `∧ⁿV` is the zero representation when
`n > dim V`. Over a field, `finrank (⋀ⁿV) = C(dim V, n) = 0` for `n > dim V`, so `∧ⁿV` is a
subsingleton. -/
theorem Example5_19_3_exterior_subsingleton_of_dim_lt
    {k : Type} [Field k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} (hn : Module.finrank k V < n) :
    Subsingleton (⋀[k]^n V) := by
  have h0 : Module.finrank k (⋀[k]^n V) = 0 := by
    rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hn]
  exact Module.finrank_zero_iff.mp h0

/-- The precise irreducibility claim for `L_{(n)} = SⁿV` (Problem 4.12.3, the first half of
the irreducibility assertion in Example 5.19.3): every `GL(V)`-subrepresentation of the
symmetric power — i.e. every submodule stable under `symmetricPowerMap g` for all
`g ∈ GL(V)` — is either `⊥` or `⊤`.

This records the statement faithfully against the `GL(V)`-action already constructed here. Its
proof reduces, via `Etingof.DiagonalCoordinate.eq_bot_or_eq_top_of_connected`, to (i) a monomial
basis of `SⁿV` with the diagonal element acting by distinct eigenvalues, and (ii) the transvection
connectivity of that basis. Step (i) needs the symmetric-power monomial basis, currently absent
from Mathlib (see the section docstring above), so the proof is deferred; it is **not** asserted to
hold by this definition, which merely names the proposition. The exterior analogue
`Example5_19_3_exterior_irreducible` *is* fully proved. -/
def Example5_19_3_symmetric_irreducible
    {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) : Prop :=
  ∀ W : Submodule k (SymmetricPower k (Fin n) V),
    (∀ g : V ≃ₗ[k] V, ∀ w ∈ W, symmetricPowerMap (g : V →ₗ[k] V) w ∈ W) →
      W = ⊥ ∨ W = ⊤

/-- **Irreducibility of `L_{(1ⁿ)} = ∧ⁿV`** (Problem 4.12.3, the second half of the irreducibility
assertion in Example 5.19.3; for `n > dim V` the space is zero, see
`Example5_19_3_exterior_subsingleton_of_dim_lt`): every `GL(V)`-subrepresentation of the exterior
power — i.e. every submodule stable under `exteriorPower.map n g` for all `g ∈ GL(V)` — is either
`⊥` or `⊤`.

This is a genuine, complete proof of Problem 4.12.3 for the exterior power, following the book's
Hint: the diagonal element `diag(2^(2⁰), …, 2^(2^{d-1}))` has pairwise distinct eigenvalues on the
monomial basis `e_{i₁} ∧ ⋯ ∧ e_{iₙ}` of `∧ⁿV` (the eigenvalues are `2^(∑ 2^{iⱼ})`, distinct by
binary uniqueness), so any subrepresentation is spanned by a subset of that basis; and the
permutation matrices, acting transitively on the `n`-subsets, then force a nonzero subrepresentation
to be everything. See `Etingof.exteriorPower_eq_bot_or_top` for the proof. The hypothesis
`[CharZero k]` (the book works over `ℂ`) is essential: over small finite fields the diagonal element
with distinct eigenvalues need not exist. -/
theorem Example5_19_3_exterior_irreducible
    {k : Type} [Field k] [CharZero k] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) :
    ∀ W : Submodule k (⋀[k]^n V),
    (∀ g : V ≃ₗ[k] V, ∀ w ∈ W, exteriorPower.map n (g : V →ₗ[k] V) w ∈ W) →
      W = ⊥ ∨ W = ⊤ :=
  fun W hW => Etingof.exteriorPower_eq_bot_or_top W hW

end Etingof

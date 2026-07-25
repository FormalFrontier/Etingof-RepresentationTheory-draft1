import Mathlib

/-!
# Problem 2.11.3(d)–(g): symmetric and exterior powers

Etingof defines, for a vector space `V` over a field `k` and `n : ℕ`,

* `S^n V` as the quotient of `V^{⊗ n}` by the subspace spanned by the tensors `T - s(T)`, where
  `T ∈ V^{⊗ n}` and `s` is a transposition of the tensor factors;
* `⋀^n V` as the quotient of `V^{⊗ n}` by the subspace spanned by the tensors `T` such that
  `s(T) = T` for some transposition `s`.

This file constructs those two quotients **exactly as the book defines them** — as
`Submodule.Quotient`s of `PiTensorProduct` — rather than substituting Mathlib's
`SymmetricAlgebra`/`ExteriorAlgebra` models, so that the parts (d)–(g) of the problem can be
stated about the book's own objects.

## Main definitions

* `Etingof.Problem2_11_3.TensorPow k V n` : the `n`-fold tensor power `V^{⊗ n}`.
* `Etingof.Problem2_11_3.permAct σ` : the action of `σ : Equiv.Perm (Fin n)` permuting the
  tensor factors of `V^{⊗ n}`.
* `Etingof.Problem2_11_3.SymPow k V n` and `ExtPow k V n` : the book's `S^n V` and `⋀^n V`.
* `Etingof.Problem2_11_3.symTprod` : the canonical *symmetric* multilinear map `V^n → S^n V`.
* `Etingof.Problem2_11_3.extTprod` : the canonical *alternating* map `V^n → ⋀^n V`.
* `Etingof.Problem2_11_3.symPowMap A` and `extPowMap A` : the operators `S^n A` and `⋀^n A`
  induced by a linear map `A : V → W` (part (f)).

## Main results

* `symTprod_comp_perm` : the canonical map to `S^n V` is invariant under *all* permutations of its
  arguments, not just transpositions.
* `extPowOfExteriorPower_surjective` : the canonical map from Mathlib's `⋀[k]^n V` onto the book's
  `ExtPow k V n` is surjective.
* `extRelSubmodule_le_ker`, `exteriorPowerEquiv` : in characteristic `≠ 2` that map is an
  isomorphism, so the book's quotient model agrees with Mathlib's exterior power.

Parts (d) (bases and dimensions), (e) (the characteristic-zero identification with the symmetric
and antisymmetric *subspaces* of `V^{⊗ n}`) and the trace formulas of part (f) are stated in
`Problem2_11_3_SymExtPow_Statements` and tracked separately.
-/

namespace Etingof.Problem2_11_3

open PiTensorProduct
open scoped TensorProduct

section Defs

variable (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V]

/-- The `n`-fold tensor power `V^{⊗ n}` of `V`, as a `PiTensorProduct` over `Fin n`. -/
abbrev TensorPow (n : ℕ) : Type _ := ⨂[k] (_ : Fin n), V

variable {k V}

/-- The action of a permutation `σ` of `Fin n` on `V^{⊗ n}`, permuting the tensor factors. -/
def permAct {n : ℕ} (σ : Equiv.Perm (Fin n)) : TensorPow k V n ≃ₗ[k] TensorPow k V n :=
  PiTensorProduct.reindex k (fun _ : Fin n => V) σ

@[simp]
lemma permAct_tprod {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Fin n → V) :
    permAct σ (PiTensorProduct.tprod k f) = PiTensorProduct.tprod k fun i => f (σ.symm i) :=
  PiTensorProduct.reindex_tprod (s := fun _ : Fin n => V) σ f

variable (k V)

/-- The subspace of `V^{⊗ n}` spanned by the tensors `T - s(T)` for `s` a transposition of the
tensor factors. Quotienting by it gives the book's `S^n V`. -/
def symRelSubmodule (n : ℕ) : Submodule k (TensorPow k V n) :=
  Submodule.span k {D : TensorPow k V n | ∃ (T : TensorPow k V n) (i j : Fin n), i ≠ j ∧
    D = T - permAct (Equiv.swap i j) T}

/-- The subspace of `V^{⊗ n}` spanned by the tensors `T` with `s(T) = T` for some transposition
`s` of the tensor factors. Quotienting by it gives the book's `⋀^n V`. -/
def extRelSubmodule (n : ℕ) : Submodule k (TensorPow k V n) :=
  Submodule.span k {T : TensorPow k V n | ∃ i j : Fin n, i ≠ j ∧
    permAct (Equiv.swap i j) T = T}

/-- **Problem 2.11.3(d).** The `n`th symmetric power `S^n V`: the quotient of `V^{⊗ n}` by the
span of the tensors `T - s(T)`, `s` a transposition. -/
abbrev SymPow (n : ℕ) : Type _ := TensorPow k V n ⧸ symRelSubmodule k V n

/-- **Problem 2.11.3(d).** The `n`th exterior power `⋀^n V`: the quotient of `V^{⊗ n}` by the
span of the tensors `T` fixed by some transposition. -/
abbrev ExtPow (n : ℕ) : Type _ := TensorPow k V n ⧸ extRelSubmodule k V n

/-- The canonical multilinear map `V^n → S^n V`, `f ↦ [f 0 ⊗ ⋯ ⊗ f (n-1)]`. -/
def symTprod (n : ℕ) : MultilinearMap k (fun _ : Fin n => V) (SymPow k V n) :=
  (symRelSubmodule k V n).mkQ.compMultilinearMap (PiTensorProduct.tprod k)

@[simp]
lemma symTprod_apply {n : ℕ} (f : Fin n → V) :
    symTprod k V n f = (symRelSubmodule k V n).mkQ (PiTensorProduct.tprod k f) := rfl

end Defs

section Basic

variable {k : Type*} [CommRing k] {V W : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

@[simp]
lemma permAct_one {n : ℕ} (T : TensorPow k V n) : permAct (1 : Equiv.Perm (Fin n)) T = T := by
  rw [permAct, show (1 : Equiv.Perm (Fin n)) = Equiv.refl (Fin n) from rfl,
    PiTensorProduct.reindex_refl]
  rfl

lemma permAct_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (T : TensorPow k V n) :
    permAct (σ * τ) T = permAct σ (permAct τ T) := by
  rw [permAct, permAct, permAct, Equiv.Perm.mul_def, ← PiTensorProduct.reindex_reindex]

/-- A pure tensor with two equal entries is fixed by the corresponding transposition, hence lies in
the relation subspace defining `⋀^n V`. -/
lemma tprod_mem_extRelSubmodule {n : ℕ} (f : Fin n → V) {i j : Fin n} (hij : i ≠ j)
    (hf : f i = f j) : PiTensorProduct.tprod k f ∈ extRelSubmodule k V n := by
  refine Submodule.subset_span ⟨i, j, hij, ?_⟩
  rw [permAct_tprod, Equiv.symm_swap]
  congr 1
  funext l
  rcases eq_or_ne l i with rfl | hli
  · rw [Equiv.swap_apply_left]; exact hf.symm
  · rcases eq_or_ne l j with rfl | hlj
    · rw [Equiv.swap_apply_right]; exact hf
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]

/-- The canonical alternating map `V^n → ⋀^n V`. -/
def extTprod (k : Type*) [CommRing k] (V : Type*) [AddCommGroup V] [Module k V] (n : ℕ) :
    V [⋀^Fin n]→ₗ[k] ExtPow k V n where
  toMultilinearMap := (extRelSubmodule k V n).mkQ.compMultilinearMap (PiTensorProduct.tprod k)
  map_eq_zero_of_eq' f i j hf hij := by
    simpa using (Submodule.Quotient.mk_eq_zero _).2 (tprod_mem_extRelSubmodule f hij hf)

@[simp]
lemma extTprod_apply {n : ℕ} (f : Fin n → V) :
    extTprod k V n f = (extRelSubmodule k V n).mkQ (PiTensorProduct.tprod k f) := rfl

/-- The transposition relation of `S^n V` holds after passing to the quotient. -/
lemma symTprod_swap {n : ℕ} (f : Fin n → V) {i j : Fin n} (hij : i ≠ j) :
    symTprod k V n (fun l => f (Equiv.swap i j l)) = symTprod k V n f := by
  have h : PiTensorProduct.tprod k f -
      PiTensorProduct.tprod k (fun l => f (Equiv.swap i j l)) ∈ symRelSubmodule k V n := by
    refine Submodule.subset_span ⟨PiTensorProduct.tprod k f, i, j, hij, ?_⟩
    rw [permAct_tprod, Equiv.symm_swap]
  simpa [symTprod_apply, Submodule.mkQ_apply] using ((Submodule.Quotient.eq _).2 h).symm

/-- **The canonical map to `S^n V` is symmetric in all its arguments**, not merely under the
transpositions used to define the quotient. -/
lemma symTprod_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Fin n → V) :
    symTprod k V n (fun l => f (σ l)) = symTprod k V n f := by
  induction σ using Equiv.Perm.swap_induction_on generalizing f with
  | one => simp
  | swap_mul τ i j hij ihτ =>
      have e1 : symTprod k V n (fun l => f ((Equiv.swap i j * τ) l))
          = symTprod k V n fun m => f (Equiv.swap i j m) :=
        ihτ fun m => f (Equiv.swap i j m)
      exact e1.trans (symTprod_swap f hij)

end Basic

end Etingof.Problem2_11_3

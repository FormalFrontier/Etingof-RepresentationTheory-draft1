import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

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
  arguments, not just the transpositions used to define the quotient.
* `symPowMap_comp`, `extPowMap_comp`, `symPowMap_id`, `extPowMap_id` : functoriality of `S^n` and
  `⋀^n` on operators.
* `extPowOfExteriorPower_surjective` : the canonical map from Mathlib's `⋀[k]^n V` onto the book's
  `ExtPow k V n` is surjective, and `extPowOfExteriorPower_naturality` says it intertwines
  `exteriorPower.map` with `extPowMap`.
* `exteriorPowerEquiv` : over any field that map is an isomorphism, so the book's quotient model
  agrees with Mathlib's exterior power. Transporting Mathlib's basis and dimension along it gives
  `extPowBasis` and `finrank_extPow`, which are the exterior half of part (d). The injectivity
  input is `tensorPowToExteriorPower_eq_zero_of_permAct_swap_eq`, proved on a tensor-product basis
  so that it covers characteristic 2, where the usual `2 • Φ T = 0` argument says nothing.
* `extPowMap_top` : part (g), `⋀^N A = det(A) • Id` in the top degree `N = dim V`, on the book's
  own `ExtPow`. Its Mathlib-side counterpart is `exteriorPower_map_top`, and `det_comp_of_extPowMap`
  runs the book's one-line derivation of `det(A ∘ B) = det(A) det(B)` from it.

The symmetric half of part (d) — the universal property of `S^n V`, a basis indexed by multisets
and the dimension `(m + n - 1).choose n` — is in the sibling file `Problem2_11_3_SymPowBasis.lean`.

Part (e), the characteristic-zero identification of `S^n V` and `⋀^n V` with the symmetric and
antisymmetric *subspaces* of `V^{⊗ n}`, is in
`EtingofRepresentationTheory.Chapter2.Problem2_11_3_SymExtSubspace`.

Still open, tracked as separate items:

* the trace formulas of part (f), `Tr(S^n A)` and `Tr(⋀^n A)` in terms of the eigenvalues of `A`.
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

/-- Permuting a pure tensor reindexes its factors by the inverse permutation. -/
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

/-- The canonical symmetric tensor map is the quotient map applied to a pure tensor. -/
@[simp]
lemma symTprod_apply {n : ℕ} (f : Fin n → V) :
    symTprod k V n f = (symRelSubmodule k V n).mkQ (PiTensorProduct.tprod k f) := rfl

end Defs

section Basic

variable {k : Type*} [CommRing k] {V W : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The identity permutation fixes every tensor. -/
@[simp]
lemma permAct_one {n : ℕ} (T : TensorPow k V n) : permAct (1 : Equiv.Perm (Fin n)) T = T := by
  rw [permAct, show (1 : Equiv.Perm (Fin n)) = Equiv.refl (Fin n) from rfl,
    PiTensorProduct.reindex_refl]
  rfl

/-- The permutation action respects multiplication of permutations. -/
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

/-- The canonical alternating tensor map is the quotient map applied to a pure tensor. -/
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

section Functoriality

variable {k : Type*} [CommRing k] {V W U : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- The operator `A^{⊗ n} : V^{⊗ n} → W^{⊗ n}` induced by `A : V → W`. -/
def tensorPowMap (A : V →ₗ[k] W) (n : ℕ) : TensorPow k V n →ₗ[k] TensorPow k W n :=
  PiTensorProduct.map fun _ : Fin n => A

/-- A tensor-power map acts componentwise on pure tensors. -/
@[simp]
lemma tensorPowMap_tprod (A : V →ₗ[k] W) {n : ℕ} (f : Fin n → V) :
    tensorPowMap A n (PiTensorProduct.tprod k f) = PiTensorProduct.tprod k fun i => A (f i) :=
  PiTensorProduct.map_tprod _ _

/-- Tensor-power maps commute with permutation of the tensor factors. -/
lemma tensorPowMap_permAct (A : V →ₗ[k] W) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (T : TensorPow k V n) :
    tensorPowMap A n (permAct σ T) = permAct σ (tensorPowMap A n T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f => simp
  | add x y hx hy => simp [hx, hy]

/-- A tensor-power map sends symmetric-power relations to symmetric-power relations. -/
lemma symRelSubmodule_le_comap (A : V →ₗ[k] W) (n : ℕ) :
    symRelSubmodule k V n ≤ (symRelSubmodule k W n).comap (tensorPowMap A n) := by
  rw [symRelSubmodule, Submodule.span_le]
  rintro _ ⟨T, i, j, hij, rfl⟩
  refine Submodule.subset_span ⟨tensorPowMap A n T, i, j, hij, ?_⟩
  rw [map_sub, tensorPowMap_permAct]

/-- A tensor-power map sends exterior-power relations to exterior-power relations. -/
lemma extRelSubmodule_le_comap (A : V →ₗ[k] W) (n : ℕ) :
    extRelSubmodule k V n ≤ (extRelSubmodule k W n).comap (tensorPowMap A n) := by
  rw [extRelSubmodule, Submodule.span_le]
  rintro T ⟨i, j, hij, hT⟩
  refine Submodule.subset_span ⟨i, j, hij, ?_⟩
  rw [← tensorPowMap_permAct, hT]

/-- **Problem 2.11.3(f).** The operator `S^n A : S^n V → S^n W` induced by `A : V → W`. -/
def symPowMap (A : V →ₗ[k] W) (n : ℕ) : SymPow k V n →ₗ[k] SymPow k W n :=
  Submodule.mapQ _ _ (tensorPowMap A n) (symRelSubmodule_le_comap A n)

/-- **Problem 2.11.3(f).** The operator `⋀^n A : ⋀^n V → ⋀^n W` induced by `A : V → W`. -/
def extPowMap (A : V →ₗ[k] W) (n : ℕ) : ExtPow k V n →ₗ[k] ExtPow k W n :=
  Submodule.mapQ _ _ (tensorPowMap A n) (extRelSubmodule_le_comap A n)

/-- The induced symmetric-power map acts componentwise on pure symmetric tensors. -/
lemma symPowMap_symTprod (A : V →ₗ[k] W) {n : ℕ} (f : Fin n → V) :
    symPowMap A n (symTprod k V n f) = symTprod k W n fun i => A (f i) := by
  simp [symPowMap, symTprod, Submodule.mapQ_apply]

/-- The induced exterior-power map acts componentwise on pure alternating tensors. -/
lemma extPowMap_extTprod (A : V →ₗ[k] W) {n : ℕ} (f : Fin n → V) :
    extPowMap A n (extTprod k V n f) = extTprod k W n fun i => A (f i) := by
  simp [extPowMap, extTprod, Submodule.mapQ_apply]

/-- The symmetric-power map induced by the identity is the identity. -/
@[simp]
lemma symPowMap_id (n : ℕ) : symPowMap (LinearMap.id : V →ₗ[k] V) n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using congrArg (r • ·) (symPowMap_symTprod LinearMap.id f)
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The exterior-power map induced by the identity is the identity. -/
@[simp]
lemma extPowMap_id (n : ℕ) : extPowMap (LinearMap.id : V →ₗ[k] V) n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using congrArg (r • ·) (extPowMap_extTprod LinearMap.id f)
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Symmetric-power maps preserve composition. -/
lemma symPowMap_comp (A : W →ₗ[k] U) (B : V →ₗ[k] W) (n : ℕ) :
    symPowMap (A ∘ₗ B) n = symPowMap A n ∘ₗ symPowMap B n := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      simp only [map_smul, LinearMap.comp_apply]
      congr 1
      have h1 := symPowMap_symTprod (A ∘ₗ B) f
      have h2 := symPowMap_symTprod A fun i => B (f i)
      have h3 := symPowMap_symTprod B f
      simp only [symTprod_apply, Submodule.mkQ_apply, LinearMap.comp_apply] at h1 h2 h3 ⊢
      rw [h1, h3, h2]
  | add a b ha hb => simp only [map_add, ha, hb, LinearMap.comp_apply]

/-- Exterior-power maps preserve composition. -/
lemma extPowMap_comp (A : W →ₗ[k] U) (B : V →ₗ[k] W) (n : ℕ) :
    extPowMap (A ∘ₗ B) n = extPowMap A n ∘ₗ extPowMap B n := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      simp only [map_smul, LinearMap.comp_apply]
      congr 1
      have h1 := extPowMap_extTprod (A ∘ₗ B) f
      have h2 := extPowMap_extTprod A fun i => B (f i)
      have h3 := extPowMap_extTprod B f
      simp only [extTprod_apply, Submodule.mkQ_apply, LinearMap.comp_apply] at h1 h2 h3 ⊢
      rw [h1, h3, h2]
  | add a b ha hb => simp only [map_add, ha, hb, LinearMap.comp_apply]

end Functoriality

section ExteriorComparison

variable {k : Type*} [CommRing k] {V W : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

variable (k V) in
/-- The canonical map from Mathlib's exterior power onto the book's model `ExtPow k V n`,
sending `v₁ ∧ ⋯ ∧ vₙ` to the class of `v₁ ⊗ ⋯ ⊗ vₙ`. -/
noncomputable def extPowOfExteriorPower (n : ℕ) : (⋀[k]^n V) →ₗ[k] ExtPow k V n :=
  exteriorPower.alternatingMapLinearEquiv (extTprod k V n)

/-- The map from Mathlib's exterior power sends a wedge to its quotient-model class. -/
@[simp]
lemma extPowOfExteriorPower_ιMulti {n : ℕ} (f : Fin n → V) :
    extPowOfExteriorPower k V n (exteriorPower.ιMulti k n f) = extTprod k V n f :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The book's `⋀^n V` is a quotient of Mathlib's exterior power. -/
theorem extPowOfExteriorPower_surjective (n : ℕ) :
    Function.Surjective (extPowOfExteriorPower k V n) := by
  intro x
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      exact ⟨r • exteriorPower.ιMulti k n f, by simp⟩
  | add a b ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      exact ⟨u + v, by rw [map_add, hu, hv, map_add]⟩

variable (k V) in
/-- The map `V^{⊗ n} → ⋀[k]^n V`, `v₁ ⊗ ⋯ ⊗ vₙ ↦ v₁ ∧ ⋯ ∧ vₙ`. -/
noncomputable def tensorPowToExteriorPower (n : ℕ) : TensorPow k V n →ₗ[k] ⋀[k]^n V :=
  PiTensorProduct.lift (exteriorPower.ιMulti k n).toMultilinearMap

/-- The canonical map to Mathlib's exterior power sends pure tensors to wedges. -/
@[simp]
lemma tensorPowToExteriorPower_tprod {n : ℕ} (f : Fin n → V) :
    tensorPowToExteriorPower k V n (PiTensorProduct.tprod k f) = exteriorPower.ιMulti k n f :=
  PiTensorProduct.lift.tprod _

/-- Transposing two tensor factors negates the image in the exterior power. -/
lemma tensorPowToExteriorPower_swap {n : ℕ} {i j : Fin n} (hij : i ≠ j) (T : TensorPow k V n) :
    tensorPowToExteriorPower k V n (permAct (Equiv.swap i j) T)
      = - tensorPowToExteriorPower k V n T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      have h : exteriorPower.ιMulti k n (fun l => f (Equiv.swap i j l))
          = - exteriorPower.ιMulti k n f :=
        (exteriorPower.ιMulti k n).map_swap (v := f) hij
      simp only [map_smul, permAct_tprod, Equiv.symm_swap, tensorPowToExteriorPower_tprod, h,
        smul_neg]
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]

/-- The comparison map is natural: it intertwines Mathlib's `exteriorPower.map A` with the book's
`⋀^n A`. -/
lemma extPowOfExteriorPower_naturality (A : V →ₗ[k] W) (n : ℕ) :
    extPowMap A n ∘ₗ extPowOfExteriorPower k V n
      = extPowOfExteriorPower k W n ∘ₗ exteriorPower.map n A := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span k n V) ?_
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.comp_apply, extPowOfExteriorPower_ιMulti,
    exteriorPower.map_apply_ιMulti]
  simpa [Function.comp_def] using extPowMap_extTprod A f

/-- Permuting the tensor factors precomposes the coordinates in a tensor-product basis: if
`T = ∑_g c_g (v_{g 0} ⊗ ⋯ ⊗ v_{g (n-1)})` then the `g`-coordinate of `σ(T)` is `c_{g ∘ σ}`. -/
lemma piTensorProduct_repr_permAct {I : Type*} (b : Module.Basis I k V) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (T : TensorPow k V n) (g : Fin n → I) :
    (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr (permAct σ T) g
      = (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T (g ∘ σ) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      simp only [map_smul, permAct_tprod, Finsupp.smul_apply,
        _root_.Basis.piTensorProduct_repr_tprod_apply, Function.comp_apply]
      exact congrArg (r • ·)
        (Fintype.prod_equiv σ _ _ fun l => by rw [Equiv.symm_apply_apply]).symm
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- **The key step, valid in every characteristic.** A tensor fixed by a transposition maps to
zero in Mathlib's exterior power.

Away from characteristic 2 this is immediate — `Φ T = Φ (sT) = -Φ T` forces `2 • Φ T = 0` — but
in characteristic 2 that argument is vacuous, so we argue on a basis. Expanding
`T = ∑_g c_g e_g` in the tensor-product basis attached to a basis `{v_i}` of `V`, the hypothesis
`sT = T` says `c_{g ∘ s} = c_g`, while `Φ e_{g ∘ s} = -Φ e_g` because `ιMulti` is alternating.
So the terms of `Φ T = ∑_g c_g Φ e_g` cancel in pairs under the fixed-point-free-where-it-matters
involution `g ↦ g ∘ s`; the `g` it does fix are exactly those with `g i = g j`, whose term is
already zero. -/
lemma tensorPowToExteriorPower_eq_zero_of_permAct_swap_eq {I : Type*} (b : Module.Basis I k V)
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) {T : TensorPow k V n}
    (hT : permAct (Equiv.swap i j) T = T) :
    tensorPowToExteriorPower k V n T = 0 := by
  classical
  -- the coordinates of `T` are invariant under precomposition with the transposition
  have hcs : ∀ g : Fin n → I,
      (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T (g ∘ Equiv.swap i j)
        = (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T g := by
    intro g
    rw [← piTensorProduct_repr_permAct b (Equiv.swap i j) T g, hT]
  -- expand `Φ T` in the tensor-product basis
  have hexp : tensorPowToExteriorPower k V n T
      = ∑ g ∈ ((_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T).support,
          (_root_.Basis.piTensorProduct fun _ : Fin n => b).repr T g •
            exteriorPower.ιMulti k n fun l => b (g l) := by
    conv_lhs => rw [← (_root_.Basis.piTensorProduct fun _ : Fin n => b).linearCombination_repr T]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun g _ => by simp [_root_.Basis.piTensorProduct_apply]
  rw [hexp]
  refine Finset.sum_involution (fun g _ => g ∘ Equiv.swap i j) ?_ ?_ ?_ ?_
  · -- paired terms are negatives of one another
    intro g _
    have hswap : (exteriorPower.ιMulti k n fun l => b ((g ∘ Equiv.swap i j) l))
        = -exteriorPower.ιMulti k n fun l => b (g l) :=
      (exteriorPower.ιMulti k n).map_swap (v := fun l => b (g l)) hij
    rw [hswap, hcs g, smul_neg, add_neg_cancel]
  · -- a term fixed by the involution is itself zero
    intro g _ hF hgs
    refine hF ?_
    have hgij : b (g i) = b (g j) := by
      have h := congrFun hgs i
      simp only [Function.comp_apply, Equiv.swap_apply_left] at h
      rw [h]
    rw [(exteriorPower.ιMulti k n).map_eq_zero_of_eq (fun l => b (g l)) hgij hij, smul_zero]
  · -- the involution preserves the support
    intro g hg
    rw [Finsupp.mem_support_iff] at hg ⊢
    rwa [hcs g]
  · -- it really is an involution
    intro g _
    funext l
    simp

end ExteriorComparison

section ExteriorEquiv

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Every tensor fixed by a transposition maps to zero in the exterior power, **in any
characteristic**. This is the content that identifies Etingof's quotient model with the usual
exterior power. -/
lemma extRelSubmodule_le_ker (n : ℕ) :
    extRelSubmodule k V n ≤ LinearMap.ker (tensorPowToExteriorPower k V n) := by
  rw [extRelSubmodule, Submodule.span_le]
  rintro T ⟨i, j, hij, hT⟩
  exact tensorPowToExteriorPower_eq_zero_of_permAct_swap_eq
    (Module.Basis.ofVectorSpace k V) hij hT

/-- **Problem 2.11.3(d), exterior case.** Over any field, the book's quotient model
`ExtPow k V n` is canonically isomorphic to Mathlib's exterior power `⋀[k]^n V`. -/
noncomputable def exteriorPowerEquiv (n : ℕ) :
    (⋀[k]^n V) ≃ₗ[k] ExtPow k V n := by
  refine LinearEquiv.ofLinear (extPowOfExteriorPower k V n)
    (Submodule.liftQ _ (tensorPowToExteriorPower k V n) (extRelSubmodule_le_ker n)) ?_ ?_
  · refine LinearMap.ext fun x => ?_
    obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
    induction T using PiTensorProduct.induction_on with
    | smul_tprod r f => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  · refine LinearMap.ext_on (exteriorPower.ιMulti_span k n V) ?_
    rintro _ ⟨f, rfl⟩
    simp

/-- The comparison equivalence sends a wedge to its class in the quotient model. -/
@[simp]
lemma exteriorPowerEquiv_ιMulti {n : ℕ} (f : Fin n → V) :
    exteriorPowerEquiv (V := V) n (exteriorPower.ιMulti k n f) = extTprod k V n f :=
  extPowOfExteriorPower_ιMulti f

/-- **Problem 2.11.3(d), exterior case.** A basis `{vᵢ}` of `V` indexed by a linearly ordered `I`
induces a basis of `⋀^n V` indexed by the `n`-element subsets of `I`, whose members are the
classes of the tensors `v_{i₁} ⊗ ⋯ ⊗ v_{iₙ}` for `i₁ < ⋯ < iₙ`. -/
noncomputable def extPowBasis {I : Type*} [LinearOrder I]
    (b : Module.Basis I k V) (n : ℕ) :
    Module.Basis (Set.powersetCard I n) k (ExtPow k V n) :=
  (b.exteriorPower n).map (exteriorPowerEquiv n)

/-- **Problem 2.11.3(d), exterior case.** If `dim V = m` then `dim ⋀^n V = m.choose n`. -/
theorem finrank_extPow [Module.Finite k V] (n : ℕ) :
    Module.finrank k (ExtPow k V n) = (Module.finrank k V).choose n := by
  rw [← (exteriorPowerEquiv (V := V) n).finrank_eq, exteriorPower.finrank_eq]

end ExteriorEquiv

section TopDegree

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- **The determinant appears in top degree.** If `dim V = N`, then feeding `A : V → V` into every
argument of the canonical alternating map `V^N → ⋀[k]^N V` multiplies the value by `det A`.

This is the computational content of part (g). The top exterior power is one-dimensional, so
pairing against the determinant of any basis is *injective*, and `Module.Basis.det_comp` supplies
the determinant on the other side. -/
theorem exteriorPower_ιMulti_comp [FiniteDimensional k V] {N : ℕ} (hN : Module.finrank k V = N)
    (A : V →ₗ[k] V) (f : Fin N → V) :
    exteriorPower.ιMulti k N (fun i => A (f i))
      = LinearMap.det A • exteriorPower.ιMulti k N f := by
  classical
  set b := Module.finBasisOfFinrankEq k V hN with hb
  haveI : FiniteDimensional k (⋀[k]^N V) := Module.Finite.of_basis (b.exteriorPower N)
  -- `D` pairs the top exterior power against the determinant in the basis `b`.
  set D : ⋀[k]^N V →ₗ[k] k := exteriorPower.alternatingMapLinearEquiv b.det with hD
  have hDsurj : Function.Surjective D := by
    intro c
    exact ⟨c • exteriorPower.ιMulti k N b, by simp [hD, Module.Basis.det_self]⟩
  have hrank : Module.finrank k (⋀[k]^N V) = Module.finrank k k := by
    rw [exteriorPower.finrank_eq, hN, Nat.choose_self, Module.finrank_self]
  have hDinj : Function.Injective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hDsurj
  apply hDinj
  rw [map_smul, hD]
  simp only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, smul_eq_mul]
  exact Module.Basis.det_comp b A f

/-- **Problem 2.11.3(g)** for Mathlib's exterior power: in the top degree `N = dim V`, the operator
`⋀^N A` is multiplication by `det A`. -/
theorem exteriorPower_map_top [FiniteDimensional k V] {N : ℕ} (hN : Module.finrank k V = N)
    (A : V →ₗ[k] V) :
    exteriorPower.map N A = LinearMap.det A • (LinearMap.id : ⋀[k]^N V →ₗ[k] ⋀[k]^N V) := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span k N V) ?_
  rintro _ ⟨f, rfl⟩
  rw [exteriorPower.map_apply_ιMulti]
  simpa [Function.comp_def] using exteriorPower_ιMulti_comp hN A f

/-- **Problem 2.11.3(g).** `⋀^N A = det(A) • Id` on Etingof's own top exterior power `ExtPow k V N`.

No hypothesis on the characteristic is needed: the comparison map `extPowOfExteriorPower` onto the
book's quotient is surjective for every commutative ring, and it intertwines `exteriorPower.map`
with `extPowMap`, so the identity descends from `exteriorPower_map_top` regardless of whether the
comparison map is injective. -/
theorem extPowMap_top [FiniteDimensional k V] {N : ℕ} (hN : Module.finrank k V = N)
    (A : V →ₗ[k] V) :
    extPowMap A N = LinearMap.det A • (LinearMap.id : ExtPow k V N →ₗ[k] ExtPow k V N) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := extPowOfExteriorPower_surjective (k := k) (V := V) N x
  have h := LinearMap.congr_fun (extPowOfExteriorPower_naturality A N) y
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [h, exteriorPower_map_top hN A]
  simp

/-- **Problem 2.11.3(g), the book's one-line proof that the determinant is multiplicative.**

`⋀^N` is functorial, so `⋀^N (A ∘ B) = ⋀^N A ∘ ⋀^N B`; by `extPowMap_top` the three sides are
multiplication by `det (A ∘ B)`, `det A` and `det B` on the *one-dimensional* space `⋀^N V`, and
comparing scalars gives the result.

This is the argument Etingof asks for, on the book's own model of `⋀^N V`, over any field: the
one-dimensionality of that model in top degree comes from `finrank_extPow`, which carries no
characteristic hypothesis. The same statement is also recorded as
`Etingof.Problem2_11_3.det_comp` (proved there by citing `LinearMap.det_comp` instead). -/
theorem det_comp_of_extPowMap [FiniteDimensional k V] {N : ℕ}
    (hN : Module.finrank k V = N) (A B : V →ₗ[k] V) :
    LinearMap.det (A ∘ₗ B) = LinearMap.det A * LinearMap.det B := by
  have hrank : Module.finrank k (ExtPow k V N) = 1 := by
    rw [finrank_extPow N, hN, Nat.choose_self]
  haveI : Nontrivial (ExtPow k V N) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hrank]; exact Nat.zero_lt_succ 0)
  obtain ⟨x, hx⟩ := exists_ne (0 : ExtPow k V N)
  have h := extPowMap_comp A B N
  rw [extPowMap_top hN (A ∘ₗ B), extPowMap_top hN A, extPowMap_top hN B] at h
  have hx' := LinearMap.congr_fun h x
  simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply, smul_smul] at hx'
  exact smul_left_injective k hx hx'

end TopDegree

end Etingof.Problem2_11_3

-- The leaf names follow Mathlib conventions; the underscore comes solely from the stable
-- book-number namespace Problem2_11_3, which is part of this project's public API.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_11_3.TensorPow Etingof.Problem2_11_3.permAct
  Etingof.Problem2_11_3.symRelSubmodule Etingof.Problem2_11_3.extRelSubmodule
  Etingof.Problem2_11_3.SymPow Etingof.Problem2_11_3.ExtPow
  Etingof.Problem2_11_3.symTprod Etingof.Problem2_11_3.extTprod
  Etingof.Problem2_11_3.tensorPowMap Etingof.Problem2_11_3.symPowMap
  Etingof.Problem2_11_3.extPowMap Etingof.Problem2_11_3.extPowOfExteriorPower
  Etingof.Problem2_11_3.tensorPowToExteriorPower Etingof.Problem2_11_3.exteriorPowerEquiv
  Etingof.Problem2_11_3.extPowBasis

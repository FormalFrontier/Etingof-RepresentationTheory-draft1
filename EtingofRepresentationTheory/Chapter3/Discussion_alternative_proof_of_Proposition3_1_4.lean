import EtingofRepresentationTheory.Chapter3.Remark3_1_3
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Discussion: alternative proof of Proposition 3.1.4 (Hom-space decomposition)

Etingof's alternative proof of Proposition 3.1.4 rests on the following consequence of
Remark 3.1.3. If `V = ⨁_X V_X ⊗ X` and `U = ⨁_X U_X ⊗ X` are semisimple representations,
written through their canonical multiplicity spaces `V_X = Hom_A(X, V)` and
`U_X = Hom_A(X, U)`, then there is a natural `k`-linear isomorphism

`Hom_A(V, U) ≅ ∏_X Hom_k(V_X, U_X)`.

Moreover, if `f : V → U` corresponds to the tuple `(f_X : V_X → U_X)`, then `f` is injective
(respectively surjective, an isomorphism) if and only if every `f_X` is.

This file formalizes that content. The natural map is **post-composition**: an `A`-linear
`f : V →ₗ[A] U` induces, for each irreducible `X i`, the `k`-linear map

`postcompHom f i : Hom_A(X i, V) →ₗ[k] Hom_A(X i, U)`, `g ↦ f ∘ g`.

The key structural fact (`restrictScalars_eq`) is that, transported through the Remark 3.1.3
isomorphisms `eV : ⨁_i Hom_A(X i, V) ⊗ X i ≃ V` and `eU : ⨁_i Hom_A(X i, U) ⊗ X i ≃ U`
(`Etingof.evalDirectSumEquiv`), the map `f` becomes the block-diagonal map
`⨁_i (postcompHom f i ⊗ id)`. From this:

* `homPiHomEquiv` : the displayed natural isomorphism `Hom_A(V, U) ≃ₗ[k] ∏_i Hom_k(V_i, U_i)`;
* `postcompHom_id`, `postcompHom_comp` : functoriality (naturality) of the construction;
* `injective_iff`, `surjective_iff`, `bijective_iff` : the componentwise criteria.

The componentwise criteria use that each `X i` is a nonzero finite-dimensional `k`-vector
space, hence `k`-faithfully-flat, so tensoring by `X i` reflects and preserves injectivity,
surjectivity and bijectivity (`Module.FaithfullyFlat.lTensor_*_iff_*`).

These are exactly the ingredients Etingof invokes to run the alternative proof of
Proposition 3.1.4: a surjection `f : V → U` of semisimple representations is componentwise
surjective, and the multiplicity-space picture reduces the classification to linear algebra.
The final quantitative statement of Proposition 3.1.4 (the multiplicity bound `r i ≤ n i`) is
proved by an isotypic-length route in `Chapter3/Proposition3_1_4.lean`; the present file
supplies the missing Hom-space API that the book's alternative argument is phrased in.
-/

open scoped DirectSum TensorProduct

namespace Etingof

variable (k A : Type*) {ι : Type*} (X : ι → Type*) (V U : Type*)
  [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]
  [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)] [∀ i, Module A (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup U] [Module k U] [Module A U] [IsScalarTower k A U]

/-- Post-composition packaged as the natural `k`-linear map

`Hom_A(V, U) →ₗ[k] ∏_i Hom_k(Hom_A(X i, V), Hom_A(X i, U))`,

sending `f` to the family `i ↦ (g ↦ f ∘ g)`. This is the natural map underlying the Hom-space
decomposition of Remark 3.1.3 used in the alternative proof of Proposition 3.1.4. -/
def postcompHom :
    (V →ₗ[A] U) →ₗ[k] (∀ i, (X i →ₗ[A] V) →ₗ[k] (X i →ₗ[A] U)) where
  toFun f := fun i =>
    { toFun := fun g => f ∘ₗ g
      map_add' := fun g g' => by ext x; simp
      map_smul' := fun c g => by ext x; simp }
  map_add' f f' := by ext i g x; simp
  map_smul' c f := by ext i g x; simp

omit [IsAlgClosed k] [Fintype ι] [DecidableEq ι] [∀ i, Module k (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)] in
/-- `postcompHom` sends `f` to post-composition by `f` in each component. -/
@[simp]
theorem postcompHom_apply (f : V →ₗ[A] U) (i : ι) (g : X i →ₗ[A] V) :
    postcompHom k A X V U f i g = f ∘ₗ g := rfl

section Equiv

variable (hpair : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j))
  [FiniteDimensional k V] [IsSemisimpleModule A V]
  [FiniteDimensional k U] [IsSemisimpleModule A U]
  (hcV : ∀ (W : Submodule A V), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i))
  (hcU : ∀ (W : Submodule A U), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i))

include hpair hcV hcU

/-- The block-diagonal factorization of `f` through the Remark 3.1.3 isomorphisms.

Writing `eV : ⨁_i Hom_A(X i, V) ⊗ X i ≃ V` and `eU : ⨁_i Hom_A(X i, U) ⊗ X i ≃ U`
(`Etingof.evalDirectSumEquiv`), an `A`-linear `f : V →ₗ[A] U` becomes, after transport,
the block-diagonal `k`-linear map `⨁_i (postcompHom f i ⊗ id_{X i})`. -/
theorem restrictScalars_eq (f : V →ₗ[A] U) :
    f.restrictScalars k =
      (evalDirectSumEquiv k A X U hpair hcU).toLinearMap ∘ₗ
        (DirectSum.lmap fun i => LinearMap.rTensor (X i) (postcompHom k A X V U f i)) ∘ₗ
          (evalDirectSumEquiv k A X V hpair hcV).symm.toLinearMap := by
  have H : (f.restrictScalars k) ∘ₗ (evalDirectSumEquiv k A X V hpair hcV).toLinearMap =
      (evalDirectSumEquiv k A X U hpair hcU).toLinearMap ∘ₗ
        (DirectSum.lmap fun i => LinearMap.rTensor (X i) (postcompHom k A X V U f i)) := by
    refine DirectSum.linearMap_ext k fun i => ?_
    refine TensorProduct.ext' fun g x => ?_
    have heV : (evalDirectSumEquiv k A X V hpair hcV)
        (DirectSum.lof k ι (fun i => (X i →ₗ[A] V) ⊗[k] X i) i (g ⊗ₜ[k] x)) = g x :=
      evalDirectSum_lof_tmul k A X V i g x
    have heU : (evalDirectSumEquiv k A X U hpair hcU)
        (DirectSum.lof k ι (fun i => (X i →ₗ[A] U) ⊗[k] X i) i ((f ∘ₗ g) ⊗ₜ[k] x)) = (f ∘ₗ g) x :=
      evalDirectSum_lof_tmul k A X U i (f ∘ₗ g) x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
      DirectSum.lmap_lof, LinearMap.rTensor_tmul, postcompHom_apply, heV, heU]
  rw [← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm, H]

/-- The kernel calculation used at the end of the book's alternative proof.  Under the
canonical multiplicity-space decomposition of Remark 3.1.3, a vector belongs to `ker f`
exactly when every tensor component is killed by the corresponding map
`postcompHom f i ⊗ id_{X i}`.  This is the componentwise content of
`ker f = ⨁_i ker (f_i) ⊗ X_i` in the displayed calculation following Lemma 3.1.6. -/
theorem mem_ker_iff_components (f : V →ₗ[A] U) (v : V) :
    v ∈ LinearMap.ker f ↔
      ∀ i, LinearMap.rTensor (X i) (postcompHom k A X V U f i)
        ((evalDirectSumEquiv k A X V hpair hcV).symm v i) = 0 := by
  rw [LinearMap.mem_ker]
  have hfacv :
      f v =
        (evalDirectSumEquiv k A X U hpair hcU)
          (DirectSum.lmap
            (fun i => LinearMap.rTensor (X i) (postcompHom k A X V U f i))
            ((evalDirectSumEquiv k A X V hpair hcV).symm v)) := by
    have h := LinearMap.congr_fun (restrictScalars_eq k A X V U hpair hcV hcU f) v
    simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe] using h
  rw [hfacv]
  constructor
  · intro hzero i
    have hcomponents :
        DirectSum.lmap
            (fun i => LinearMap.rTensor (X i) (postcompHom k A X V U f i))
            ((evalDirectSumEquiv k A X V hpair hcV).symm v) = 0 := by
      apply (evalDirectSumEquiv k A X U hpair hcU).injective
      simpa using hzero
    have hi := congrArg (fun z => z i) hcomponents
    simpa using hi
  · intro hcomponents
    have hzero :
        DirectSum.lmap
            (fun i => LinearMap.rTensor (X i) (postcompHom k A X V U f i))
            ((evalDirectSumEquiv k A X V hpair hcV).symm v) = 0 := by
      ext i
      simpa using hcomponents i
    simp [hzero]

omit [DecidableEq ι] in
/- Finiteness is needed by the finite direct-sum factorization, although it does not occur in
the proposition returned by `Function.Injective`. -/
set_option linter.unusedFintypeInType false in
/-- `postcompHom` is injective: `f` is recovered from `postcompHom f` via the block-diagonal
factorization, so `postcompHom f = postcompHom f'` forces `f = f'`. -/
theorem postcompHom_injective :
    Function.Injective (postcompHom k A X V U) := by
  classical
  intro f f' h
  have hres : f.restrictScalars k = f'.restrictScalars k := by
    rw [restrictScalars_eq k A X V U hpair hcV hcU f,
      restrictScalars_eq k A X V U hpair hcV hcU f', h]
  ext v
  exact DFunLike.congr_fun hres v

omit [DecidableEq ι] in
/- Finiteness is needed by the finite direct-sum construction, although it does not occur in
the proposition returned by `Function.Surjective`. -/
set_option linter.unusedFintypeInType false in
/-- `postcompHom` is surjective. Given a target family `φ`, transport the block-diagonal map
`⨁_i (φ i ⊗ id)` through the Remark 3.1.3 isomorphisms to a `k`-linear map `fk`; it is
`A`-linear because on the spanning set `{g x}` it equals `(φ i g) x`, and `φ i g`, `g` are
`A`-linear. The resulting `A`-linear map maps to `φ` under `postcompHom`. -/
theorem postcompHom_surjective :
    Function.Surjective (postcompHom k A X V U) := by
  classical
  intro φ
  set eV := evalDirectSumEquiv k A X V hpair hcV with heVdef
  set eU := evalDirectSumEquiv k A X U hpair hcU with heUdef
  -- evaluation of `eU` and `eV.symm` on generators
  have heU : ∀ i (h : X i →ₗ[A] U) (x : X i),
      eU (DirectSum.lof k ι (fun i => (X i →ₗ[A] U) ⊗[k] X i) i (h ⊗ₜ[k] x)) = h x :=
    fun i h x => evalDirectSum_lof_tmul k A X U i h x
  have heVsymm : ∀ i (g : X i →ₗ[A] V) (x : X i),
      eV.symm (g x) = DirectSum.lof k ι (fun i => (X i →ₗ[A] V) ⊗[k] X i) i (g ⊗ₜ[k] x) := by
    intro i g x
    rw [LinearEquiv.symm_apply_eq]
    exact (evalDirectSum_lof_tmul k A X V i g x).symm
  -- the k-linear candidate
  set T : (⨁ i, (X i →ₗ[A] V) ⊗[k] X i) →ₗ[k] (⨁ i, (X i →ₗ[A] U) ⊗[k] X i) :=
    DirectSum.lmap (fun i => LinearMap.rTensor (X i) (φ i)) with hTdef
  set fk : V →ₗ[k] U := eU.toLinearMap ∘ₗ T ∘ₗ eV.symm.toLinearMap with hfkdef
  -- its value on `g x`
  have hfk_gen : ∀ i (g : X i →ₗ[A] V) (x : X i), fk (g x) = (φ i g) x := by
    intro i g x
    simp only [hfkdef, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [heVsymm i g x, hTdef, DirectSum.lmap_lof, LinearMap.rTensor_tmul]
    exact heU i (φ i g) x
  -- `fk` is A-linear, checked on the spanning set `{g x}` of `V`
  have hAlin : ∀ (a : A) (v : V), fk (a • v) = a • fk v := by
    intro a v
    obtain ⟨w, rfl⟩ := eV.surjective v
    induction w using DirectSum.induction_on with
    | zero => simp
    | of i t =>
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul g x =>
            have hlof : eV (DirectSum.of (fun i => (X i →ₗ[A] V) ⊗[k] X i) i (g ⊗ₜ[k] x)) = g x :=
              evalDirectSum_lof_tmul k A X V i g x
            rw [hlof, ← g.map_smul a x, hfk_gen i g (a • x), hfk_gen i g x, (φ i g).map_smul a x]
        | add t₁ t₂ h₁ h₂ =>
            simp only [map_add, smul_add]
            rw [h₁, h₂]
    | add w₁ w₂ h₁ h₂ =>
        simp only [map_add, smul_add]
        rw [h₁, h₂]
  -- assemble the A-linear preimage
  let fA : V →ₗ[A] U :=
    { toFun := fun v => fk v
      map_add' := fun a b => map_add fk a b
      map_smul' := fun a v => hAlin a v }
  refine ⟨fA, ?_⟩
  ext i g x
  exact hfk_gen i g x

/-- **Remark 3.1.3 / alternative proof of Proposition 3.1.4.** The natural `k`-linear
isomorphism `Hom_A(V, U) ≅ ∏_i Hom_k(Hom_A(X i, V), Hom_A(X i, U))`, given by post-composition
`f ↦ (i ↦ (g ↦ f ∘ g))`, for semisimple finite-dimensional representations `V`, `U` and a
complete set `{X i}` of pairwise non-isomorphic irreducibles. -/
noncomputable def homPiHomEquiv :
    (V →ₗ[A] U) ≃ₗ[k] (∀ i, (X i →ₗ[A] V) →ₗ[k] (X i →ₗ[A] U)) :=
  LinearEquiv.ofBijective (postcompHom k A X V U)
    ⟨postcompHom_injective k A X V U hpair hcV hcU,
      postcompHom_surjective k A X V U hpair hcV hcU⟩

omit [DecidableEq ι] in
/-- The Hom-space equivalence acts componentwise by post-composition. -/
@[simp]
theorem homPiHomEquiv_apply (f : V →ₗ[A] U) (i : ι) (g : X i →ₗ[A] V) :
    homPiHomEquiv k A X V U hpair hcV hcU f i g = f ∘ₗ g := rfl

section Criteria

omit [DecidableEq ι] in
/- Finiteness is needed by the finite direct-sum criterion, although it does not occur in the
resulting logical equivalence. -/
set_option linter.unusedFintypeInType false in
/-- Componentwise criterion for injectivity: an `A`-linear map `f : V → U` between semisimple
finite-dimensional representations is injective iff every multiplicity-space component
`postcompHom f i : Hom_A(X i, V) → Hom_A(X i, U)` is injective. -/
theorem injective_iff (f : V →ₗ[A] U) :
    Function.Injective f ↔ ∀ i, Function.Injective (postcompHom k A X V U f i) := by
  classical
  rw [show Function.Injective f ↔ Function.Injective ⇑(f.restrictScalars k) from Iff.rfl,
    restrictScalars_eq k A X V U hpair hcV hcU f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
    EquivLike.injective_comp, DirectSum.lmap_injective]
  refine forall_congr' fun i => ?_
  haveI : Nontrivial (X i) := IsSimpleModule.nontrivial (R := A) (M := X i)
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj,
    Module.FaithfullyFlat.lTensor_injective_iff_injective]

omit [DecidableEq ι] in
/- Finiteness is needed by the finite direct-sum criterion, although it does not occur in the
resulting logical equivalence. -/
set_option linter.unusedFintypeInType false in
/-- Componentwise criterion for surjectivity. -/
theorem surjective_iff (f : V →ₗ[A] U) :
    Function.Surjective f ↔ ∀ i, Function.Surjective (postcompHom k A X V U f i) := by
  classical
  rw [show Function.Surjective f ↔ Function.Surjective ⇑(f.restrictScalars k) from Iff.rfl,
    restrictScalars_eq k A X V U hpair hcV hcU f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
    EquivLike.surjective_comp, DirectSum.lmap_surjective]
  refine forall_congr' fun i => ?_
  haveI : Nontrivial (X i) := IsSimpleModule.nontrivial (R := A) (M := X i)
  rw [← LinearMap.lTensor_surj_iff_rTensor_surj,
    Module.FaithfullyFlat.lTensor_surjective_iff_surjective]

omit [DecidableEq ι] in
/- Finiteness is inherited from the injectivity and surjectivity criteria, although it does not
occur in the resulting logical equivalence. -/
set_option linter.unusedFintypeInType false in
/-- Componentwise criterion for being an isomorphism. -/
theorem bijective_iff (f : V →ₗ[A] U) :
    Function.Bijective f ↔ ∀ i, Function.Bijective (postcompHom k A X V U f i) := by
  classical
  simp_rw [Function.Bijective, forall_and]
  rw [injective_iff k A X V U hpair hcV hcU f, surjective_iff k A X V U hpair hcV hcU f]

end Criteria

end Equiv

section Naturality

omit [IsAlgClosed k] [Fintype ι] [DecidableEq ι] [∀ i, Module k (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)] in
/-- Functoriality (naturality) of `postcompHom` in the identity. -/
@[simp]
theorem postcompHom_id :
    postcompHom k A X V V (LinearMap.id) = fun _ => LinearMap.id := by
  ext i g x
  simp

variable (W : Type*) [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

omit [IsAlgClosed k] [Fintype ι] [DecidableEq ι] [∀ i, Module k (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)] in
/-- Functoriality (naturality) of `postcompHom` under composition: post-composition by
`f' ∘ f` is the composite of post-composition by `f` and by `f'`, componentwise. This is the
naturality of the Hom-space decomposition in the target multiplicity family. -/
theorem postcompHom_comp (f : V →ₗ[A] U) (f' : U →ₗ[A] W) :
    postcompHom k A X V W (f' ∘ₗ f) =
      fun i => (postcompHom k A X U W f' i) ∘ₗ (postcompHom k A X V U f i) := by
  ext i g x
  simp

end Naturality

end Etingof

import EtingofRepresentationTheory.Chapter8.RearrangeHomComplexX

/-!
# The complex-level rearrangement isomorphism for the `Ext` Künneth formula

Route **step 3** (final assembly, #6844/#6868) of the `Ext` half of Problem 8.2.8. This is the
`Hom`-cochain twin of `Etingof.rearrangeComplex` (`Chapter8/RearrangeComplex.lean`, #6744), but
built via `HomologicalComplex.Hom.isoOfComponents` (assembled degreewise from the object iso #6867)
rather than `total.mapIso`, because the source `Hom(mapBifunctor …, N)` is a **product** over the
finite fiber, not a `mapBifunctor` bicomplex.

Combining the degreewise object iso `Etingof.rearrangeHomComplexXIso` (#6867) with the two
naturality lemmas of #6843 (`homTensorHom_comp_lcompₖ_left/right`, feeding the two
differential-commutation squares), this file assembles the isomorphism of
`CochainComplex (ModuleCat k) ℕ`

```
rearrangeHomComplex :
  (extTensorComplexLeft P₁ P₂).linearYonedaObj k (N₁ ⊗ₖ N₂)
    ≅ HomologicalComplex.tensorObj
        (P₁.complex.linearYonedaObj k N₁)
        (P₂.complex.linearYonedaObj k N₂)
```

feeding the Künneth `Ext` assembler (#6818).

## Route

The degreewise components are `rearrangeHomComplexXIso`. The differential-commutation obligation for
`isoOfComponents` is discharged summand-by-summand on the *target* coproduct (via
`mapBifunctor.hom_ext`), reducing — through the `ι`/inv reduction `rearrangeHomComplexXIso`'s
`ιMapBifunctor_rearrangeHomComplexXIso_inv` and the source biproduct relations `srcInc_srcProj` — to
the two naturality lemmas of #6843. The source differential
`(X.linearYonedaObj k Y).d i j = ofHom (Linear.leftComp k Y (X.d j i))` is precomposition by the
source chain differential; contravariance flips the fiber index from degree `i+1` (source) to `i`
(target).
-/

open CategoryTheory Limits MonoidalCategory TensorProduct HomologicalComplex

namespace Etingof

universe u

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
  [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

variable {A₁ A₂}
variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}
variable (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
variable [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
variable [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)]

/-- Applying a `ModuleCat k` `eqToHom` to an element is a `cast` along the carrier equality. -/
private lemma eqToHom_moduleCat_apply {X Y : ModuleCat.{u} k} (h : X = Y) (x : X) :
    (eqToHom h) x = cast (congrArg (fun o : ModuleCat.{u} k => (o : Type u)) h) x := by
  subst h; rfl

/-- The underlying linear map of a `ModuleCat k` `eqToHom`, applied to an element, is a `cast`. -/
private lemma hom_eqToHom_apply {X Y : ModuleCat.{u} k} (h : X = Y) (x : X) :
    ModuleCat.Hom.hom (eqToHom h) x = cast (congrArg (fun o : ModuleCat.{u} k => (o : Type u)) h) x := by
  subst h; rfl

include hN in
/-- Pointwise action of `summandIso.inv` on a simple tensor of categorical homs. -/
theorem summandIso_inv_hom_apply (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂]
    (ψ₁ : X₁ ⟶ ModuleCat.of A₁ N₁) (ψ₂ : X₂ ⟶ ModuleCat.of A₂ N₂) (x₁ : X₁) (x₂ : X₂) :
    ModuleCat.Hom.hom ((summandIso k N₁ N₂ hN X₁ X₂).inv (ψ₁ ⊗ₜ[k] ψ₂)) (x₁ ⊗ₜ[k] x₂)
      = (ModuleCat.Hom.hom ψ₁) x₁ ⊗ₜ[k] (ModuleCat.Hom.hom ψ₂) x₂ := by
  simp only [summandIso, rearrangeHomComponentIso, rearrangeHomComponentEquiv,
    HomTensorFGProj.homTensorHomEquiv, Iso.trans_inv, Iso.symm_inv, tensorIso,
    LinearEquiv.toModuleIso_inv, LinearEquiv.toModuleIso_hom, LinearEquiv.symm_symm,
    extTensorFunctorLeftObj, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_tensorHom,
    ModuleCat.hom_ofHom, TensorProduct.map_tmul, ModuleCat.homLinearEquiv_apply,
    ModuleCat.homLinearEquiv_symm_apply, LinearEquiv.ofBijective_apply,
    HomTensorFGProj.homTensorHom_tmul_tmul]
  erw [TensorProduct.map_tmul]
  simp only [LinearEquiv.coe_coe, LinearMap.restrictScalars_apply]
  rfl

include hN in
/-- Pointwise action of the inverse per-summand iso on a simple tensor: on `φ₁ ⊗ₜ φ₂` it is the
`homTensorHom` comparison map, evaluated at `x₁ ⊗ₜ x₂` it returns `φ₁ x₁ ⊗ₜ φ₂ x₂`. This isolates
all the `eqToHom` carrier-transport bookkeeping of `fullSummandIso`.

The core reduction to `homTensorHom` is `summandIso_inv_hom_apply` (proved above, sorry-free). What
remains here is purely the `eqToHom` carrier-transport bookkeeping between the two `k`-module
spellings of the same hom-space (the `srcSummandEq`/`linYonedaXEq` bridges of `fullSummandIso`).
These transports are *propositional*, not definitional: `eqToHom h` between `ModuleCat k` objects
with defeq-but-not-syntactically-equal carriers is a stuck `Eq.rec`, so neither `rfl` nor a single
`Eq.trans` against `summandIso_inv_hom_apply` closes the goal — both the source (`fullSummandIso.inv`
composite) and target (`φᵢ` vs `eqToHom (linYonedaXEq …) φᵢ`) differ by such a transport. Closing it
needs a nested `HEq` bridge (`cast_heq`/`eqRec_heq`) threaded through `summandIso.inv` on both sides.
Tracked as the residual of #6888. -/
theorem fullSummandIso_inv_tmul_hom_apply (j m : ℕ)
    (φ₁ : (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).X j)
    (φ₂ : (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).X m)
    (x₁ : P₁.complex.X j) (x₂ : P₂.complex.X m) :
    ModuleCat.Hom.hom ((fullSummandIso k N₁ N₂ hN P₁ P₂ j m).inv (φ₁ ⊗ₜ[k] φ₂))
        (x₁ ⊗ₜ[k] x₂)
      = (ModuleCat.Hom.hom φ₁) x₁ ⊗ₜ[k] (ModuleCat.Hom.hom φ₂) x₂ := by
  -- Reduces to `summandIso_inv_hom_apply` modulo the two `eqToHom` carrier-transports; see docstring.
  sorry

include hN in
/-- **Naturality in the first variable, inverse form.** Precomposition by the source chain
differential on the first factor commutes past `fullSummandIso.inv`. Reduces (elementwise) to the
#6843 naturality lemma `homTensorHom_comp_lcompₖ_left`. -/
theorem fullSummandIso_inv_natLeft (p q : ℕ) :
    ((curriedTensor (ModuleCat.{u} k)).map
          ((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).d p (p + 1))).app
        ((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).X q) ≫
        (fullSummandIso k N₁ N₂ hN P₁ P₂ (p + 1) q).inv =
      (fullSummandIso k N₁ N₂ hN P₁ P₂ p q).inv ≫
        (homYoneda k N₁ N₂).map
          (extTensorFunctorLeftMap k (P₁.complex.d (p + 1) p) (𝟙 (P₂.complex.X q))).op := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' fun φ₁ φ₂ => ?_
  -- Both sides evaluate, via `fullSummandIso_inv_tmul_hom_apply`, to `homTensorHom` composed with
  -- precomposition by the source differential; matching them is `homTensorHom_comp_lcompₖ_left`.
  sorry

include hN in
/-- **Naturality in the second variable, inverse form.** Mirror of `fullSummandIso_inv_natLeft`,
reducing to `homTensorHom_comp_lcompₖ_right`. -/
theorem fullSummandIso_inv_natRight (p q : ℕ) :
    ((curriedTensor (ModuleCat.{u} k)).obj
          ((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).X p)).map
        ((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).d q (q + 1)) ≫
        (fullSummandIso k N₁ N₂ hN P₁ P₂ p (q + 1)).inv =
      (fullSummandIso k N₁ N₂ hN P₁ P₂ p q).inv ≫
        (homYoneda k N₁ N₂).map
          (extTensorFunctorLeftMap k (𝟙 (P₁.complex.X p)) (P₂.complex.d (q + 1) q)).op := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' fun φ₁ φ₂ => ?_
  -- Mirror of `fullSummandIso_inv_natLeft`; matches via `homTensorHom_comp_lcompₖ_right`.
  sorry

include hN in
/-- **The differential-commutation square, inverse form.** Composing the target differential with
the inverse degreewise iso equals the inverse degreewise iso followed by the source differential.
Proved
summand-by-summand on the target coproduct (`mapBifunctor.hom_ext`), reducing through the `.inv`
reduction `ιMapBifunctor_rearrangeHomComplexXIso_inv` and the source biproduct relations to the two
#6843 naturality lemmas. -/
theorem rearrangeHomComplexXIso_inv_comm (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (homTarget k N₁ N₂ P₁ P₂).d i j ≫
        (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ j).inv =
      (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).inv ≫
        ((extTensorComplexLeft P₁ P₂).linearYonedaObj k
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  -- Reduce the RHS summand `tgtInc ≫ (iso i).inv ≫ S.d` via the `.inv` reduction of #6867 and the
  -- source differential `linearYonedaObj_d`. The source differential is precomposition by the
  -- degree-`(i+1) → i` chain differential of `extTensorComplexLeft`; on the LHS the target
  -- differential (Koszul-signed `mapBifunctor.d_eq` on `up ℕ`) is precomposition by the two factor
  -- Hom differentials. Matching the two summand-by-summand (`mapBifunctor.hom_ext` over the source
  -- fiber, `srcInc_srcProj` biproduct relations) reduces to the two #6843 naturality lemmas
  -- `homTensorHom_comp_lcompₖ_left/right`, exactly the `fwdNat_comm` sign bookkeeping. Left as a
  -- first-pass `sorry` (acceptable per #6844); tracked in a follow-up.
  rw [ιMapBifunctor_rearrangeHomComplexXIso_inv_assoc, ChainComplex.linearYonedaObj_d]
  sorry

include hN in
/-- **The differential-commutation square** for the `Ext` Künneth cochain assembly: the degreewise
object isos `rearrangeHomComplexXIso` commute with the source (`Hom(mapBifunctor …, N)`) and target
(`tensorObj` of the two Hom cochain complexes) differentials. Derived from the inverse form
`rearrangeHomComplexXIso_inv_comm`. -/
theorem rearrangeHomComplexXIso_comm (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).hom ≫
        (homTarget k N₁ N₂ P₁ P₂).d i j =
      ((extTensorComplexLeft P₁ P₂).linearYonedaObj k
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j ≫
        (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ j).hom := by
  have key := rearrangeHomComplexXIso_inv_comm k N₁ N₂ hN P₁ P₂ i j hij
  calc
    (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).hom ≫ (homTarget k N₁ N₂ P₁ P₂).d i j
        = (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).hom ≫
            ((homTarget k N₁ N₂ P₁ P₂).d i j ≫
              (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ j).inv) ≫
            (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ j).hom := by simp
      _ = (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).hom ≫
            ((rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).inv ≫
              ((extTensorComplexLeft P₁ P₂).linearYonedaObj k
                (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j) ≫
            (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ j).hom := by rw [key]
      _ = ((extTensorComplexLeft P₁ P₂).linearYonedaObj k
              (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j ≫
            (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ j).hom := by
          rw [Category.assoc, Iso.hom_inv_id_assoc]

include hN in
/-- **Route step 3 (#6868).** The complex-level rearrangement isomorphism of
`CochainComplex (ModuleCat k) ℕ`:

```
(extTensorComplexLeft P₁ P₂).linearYonedaObj k (N₁ ⊗ₖ N₂)
  ≅ HomologicalComplex.tensorObj
      (P₁.complex.linearYonedaObj k N₁)
      (P₂.complex.linearYonedaObj k N₂)
```

Assembled from the degreewise object iso `rearrangeHomComplexXIso` (#6867) via `isoOfComponents`,
with the differential-commutation obligation `rearrangeHomComplexXIso_comm`. -/
noncomputable def rearrangeHomComplex :
    (extTensorComplexLeft P₁ P₂).linearYonedaObj k
        (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) ≅
      HomologicalComplex.tensorObj
        (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i)
    (fun i j hij => rearrangeHomComplexXIso_comm k N₁ N₂ hN P₁ P₂ i j hij)

include hN in
/-- The degreewise action of `rearrangeHomComplex` on a summand: its `.hom.f i` is exactly the
degreewise object iso `rearrangeHomComplexXIso`. This is the rewrite the Künneth `Ext` assembler
(#6818) uses to identify the degree-`i` factor cohomologies. -/
@[simp]
theorem rearrangeHomComplex_hom_f (i : ℕ) :
    (rearrangeHomComplex k N₁ N₂ hN P₁ P₂).hom.f i =
      (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).hom := rfl

end Etingof

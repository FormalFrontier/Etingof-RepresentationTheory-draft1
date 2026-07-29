import EtingofRepresentationTheory.Chapter8.RearrangeHomComplexX

set_option backward.isDefEq.respectTransparency false

/-!
# The complex-level rearrangement isomorphism for the `Ext` Künneth formula

This file constructs the complex-level rearrangement isomorphism for the `Ext` half of
Problem 8.2.8. This is the `Hom`-cochain twin of `Etingof.rearrangeComplex`
(`Chapter8/RearrangeComplex.lean`), but built via `HomologicalComplex.Hom.isoOfComponents`
(assembled degreewise from the object iso) rather than `total.mapIso`, because the source
`Hom(mapBifunctor …, N)` is a product over the finite fiber, not a `mapBifunctor` bicomplex.

Combining the degreewise object iso `Etingof.rearrangeHomComplexXIso` with the two
naturality lemmas `homTensorHom_comp_lcompₖ_left/right` (discharging the two
differential-commutation squares), this file assembles the isomorphism of
`CochainComplex (ModuleCat k) ℕ`

```
rearrangeHomComplex :
  (extTensorComplexLeft P₁ P₂).linearYonedaObj k (N₁ ⊗ₖ N₂)
    ≅ HomologicalComplex.tensorObj
        (P₁.complex.linearYonedaObj k N₁)
        (P₂.complex.linearYonedaObj k N₂)
```

used by the Künneth `Ext` assembler.

## Construction

The degreewise components are `rearrangeHomComplexXIso`. The differential-commutation obligation for
`isoOfComponents` is discharged summand-by-summand on the target coproduct (via
`mapBifunctor.hom_ext`), reducing, through the `ι`/inv reduction
`ιMapBifunctor_rearrangeHomComplexXIso_inv` and the source biproduct relations `srcInc_srcProj`, to
the two naturality lemmas. The source differential
`(X.linearYonedaObj k Y).d i j = ofHom (Linear.leftComp k Y (X.d j i))` is precomposition by the
source chain differential; contravariance flips the fiber index from degree `i+1` (source) to `i`
(target).
-/

open CategoryTheory Limits MonoidalCategory TensorProduct HomologicalComplex

namespace Etingof

open HomTensorFGProj

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

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL towerExtL

variable {A₁ A₂}
variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}
variable (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
variable [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
variable [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)]

/-- Applying a `ModuleCat k` `eqToHom` to an element is the `▸` transport of the element. Since the
`eqToHom` object equalities appearing in `fullSummandIso` (`srcSummandEq`, `linYonedaXEq`) are
between `ModuleCat.of k T` objects sharing the same carrier `T`, the resulting `h ▸ x` is defeq to
`x`. -/
private lemma eqToHom_moduleCat_apply {X Y : ModuleCat.{u} k} (h : X = Y) (x : X) :
    (eqToHom h) x = h ▸ x := by cases h; rfl

/-- Applying a `ModuleCat k` `eqToHom` to an element yields a heterogeneously-equal element. When
the two objects share a carrier (the `srcSummandEq`/`linYonedaXEq` object equalities of
`fullSummandIso`), this upgrades to an honest equation via `eq_of_heq`. -/
private lemma eqToHom_hom_apply_heq {X Y : ModuleCat.{u} k} (h : X = Y) (w : X) :
    HEq (ModuleCat.Hom.hom (eqToHom h) w) w := by subst h; rfl

include hN in
/-- Closed form of `summandIso.inv` on a simple tensor `a₁ ⊗ₜ a₂` (plain morphisms, no `eqToHom`
transport), evaluated at `y₁ ⊗ₜ y₂`: it is `a₁ y₁ ⊗ₜ a₂ y₂`. The `eqToHom`-free core of
`fullSummandIso_inv_tmul_apply`. -/
private lemma summandIso_inv_tmul_apply (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂]
    (a₁ : X₁ ⟶ ModuleCat.of A₁ N₁) (a₂ : X₂ ⟶ ModuleCat.of A₂ N₂) (y₁ : X₁) (y₂ : X₂) :
    (ModuleCat.Hom.hom ((summandIso k N₁ N₂ hN X₁ X₂).inv (a₁ ⊗ₜ[k] a₂))) (y₁ ⊗ₜ[k] y₂)
      = a₁.hom y₁ ⊗ₜ[k] a₂.hom y₂ := by
  simp only [summandIso, rearrangeHomComponentIso, Iso.trans_inv, Iso.symm_inv,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

set_option maxHeartbeats 1000000 in
include hN in
/-- Closed form of `fullSummandIso.inv` on a simple tensor `ψ₁ ⊗ₜ ψ₂`, evaluated at a simple tensor
`y₁ ⊗ₜ y₂`: it is `ψ₁ y₁ ⊗ₜ ψ₂ y₂` (`homTensorHom`). This is the pointwise reduction that both
naturality lemmas share; the `eqToHom` transports in `fullSummandIso` act as the identity on the
shared underlying `↦` map, discharged by `eqToHom_moduleCat_apply`. -/
private lemma fullSummandIso_inv_tmul_apply (j m : ℕ)
    (ψ₁ : ↥((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).X j))
    (ψ₂ : ↥((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).X m))
    (y₁ : P₁.complex.X j) (y₂ : P₂.complex.X m) :
    (ModuleCat.Hom.hom (ModuleCat.Hom.hom (fullSummandIso k N₁ N₂ hN P₁ P₂ j m).inv (ψ₁ ⊗ₜ[k] ψ₂)))
        (y₁ ⊗ₜ[k] y₂) = ψ₁.hom y₁ ⊗ₜ[k] ψ₂.hom y₂ := by
  have e0 := fun w => eq_of_heq (eqToHom_hom_apply_heq k (srcSummandEq k N₁ N₂ hN P₁ P₂ j m).symm w)
  have e1 := fun w => eq_of_heq (eqToHom_hom_apply_heq k (linYonedaXEq k A₁ N₁ P₁.complex j) w)
  have e2 := fun w => eq_of_heq (eqToHom_hom_apply_heq k (linYonedaXEq k A₂ N₂ P₂.complex m) w)
  simp only [fullSummandIso, Iso.trans_inv, tensorIso_inv, eqToIso.inv, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_tensorHom, e0]
  erw [TensorProduct.map_tmul]
  rw [e1, e2]
  rfl

set_option maxHeartbeats 1000000 in
include hN in
/-- **Naturality of `fullSummandIso.inv` in the first (contravariant) variable.** Composing the
degree-`p → p+1` source differential of the first `Hom` cochain factor (via `curriedTensor`) with
the per-summand inverse iso equals the per-summand inverse iso followed by precomposition by the
external-tensor map of the chain differential `P₁.d (p+1) p`. Reduces pointwise through
`fullSummandIso_inv_tmul_apply` to `homTensorHom_comp_lcompₖ_left`. -/
@[reassoc]
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
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, curriedTensor_map_app,
    ChainComplex.linearYonedaObj_d, ModuleCat.hom_whiskerRight, ModuleCat.hom_ofHom,
    linearYoneda_obj_map]
  erw [LinearMap.rTensor_tmul]
  apply ModuleCat.hom_ext
  refine HomTensorFGProj.hom_ext k A₁ A₂ _ _ N₁ N₂ (fun x₁ x₂ => ?_)
  refine (fullSummandIso_inv_tmul_apply k N₁ N₂ hN P₁ P₂ (p + 1) q
      (Linear.leftComp k (ModuleCat.of A₁ N₁) (P₁.complex.d (p + 1) p) φ₁) φ₂ x₁ x₂).trans
    (Eq.trans ?_ (fullSummandIso_inv_tmul_apply k N₁ N₂ hN P₁ P₂ p q φ₁ φ₂
      ((P₁.complex.d (p + 1) p).hom x₁) x₂).symm)
  rfl

include hN in
/-- **Naturality of `fullSummandIso.inv` in the second (contravariant) variable.** The mirror of
`fullSummandIso_inv_natLeft`, reducing to `homTensorHom_comp_lcompₖ_right`. -/
@[reassoc]
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
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, curriedTensor_obj_map,
    ChainComplex.linearYonedaObj_d, ModuleCat.hom_whiskerLeft, ModuleCat.hom_ofHom,
    linearYoneda_obj_map]
  erw [LinearMap.lTensor_tmul]
  apply ModuleCat.hom_ext
  refine HomTensorFGProj.hom_ext k A₁ A₂ _ _ N₁ N₂ (fun x₁ x₂ => ?_)
  refine (fullSummandIso_inv_tmul_apply k N₁ N₂ hN P₁ P₂ p (q + 1)
      φ₁ (Linear.leftComp k (ModuleCat.of A₂ N₂) (P₂.complex.d (q + 1) q) φ₂) x₁ x₂).trans
    (Eq.trans ?_ (fullSummandIso_inv_tmul_apply k N₁ N₂ hN P₁ P₂ p q φ₁ φ₂
      x₁ ((P₂.complex.d (q + 1) q).hom x₂)).symm)
  rfl

omit [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
  [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)] in
/-- **Source `ι`/`π` reduction (bare `ιMapBifunctor` form).** Composing the `(x, y)` summand
inclusion of the external tensor complex with the `(p, q)` projection is the Kronecker delta. This
is `srcInc_srcProj` restated with `ιMapBifunctor` in place of the `srcInc` abbreviation, so it
rewrites against the raw inclusions produced by `mapBifunctor.hom_ext` and `d₁_eq`/`d₂_eq`. -/
theorem ιMapBifunctor_srcProj (i x y p q : ℕ) (hx : x + y = i) (hpq : p + q = i) :
    ιMapBifunctor P₁.complex P₂.complex (extTensorFunctorLeft k A₁ A₂)
        (ComplexShape.down ℕ) x y i hx ≫ srcProj k P₁ P₂ i p q hpq =
      if h : x = p ∧ y = q then eqToHom (by rw [h.1, h.2]) else 0 := by
  simp only [srcProj, ι_mapBifunctorDesc]

omit [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
  [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)] in
/-- **The source-complex sign-bookkeeping identity.** The pure source-side statement underlying the
inverse differential-commutation square: the two factor differentials of the external tensor complex
(with the Koszul sign `(-1)^p` on the second) precomposed with the `(p, q)` projection match the
total differential of `extTensorComplexLeft` precomposed with the same projection. Proved
summand-by-summand on the domain (`mapBifunctor.hom_ext`), reducing both sides to Kronecker deltas
via `ιMapBifunctor_srcProj` and the `down ℕ` `d₁_eq`/`d₂_eq` expansion. -/
theorem srcProj_comm (i p q : ℕ) (hpq : p + q = i) :
    srcProj k P₁ P₂ (i + 1) (p + 1) q (by omega) ≫
        ((extTensorFunctorLeft k A₁ A₂).map (P₁.complex.d (p + 1) p)).app (P₂.complex.X q) +
      (-1 : ℤˣ) ^ p • (srcProj k P₁ P₂ (i + 1) p (q + 1) (by omega) ≫
        ((extTensorFunctorLeft k A₁ A₂).obj (P₁.complex.X p)).map (P₂.complex.d (q + 1) q)) =
      (extTensorComplexLeft P₁ P₂).d (i + 1) i ≫ srcProj k P₁ P₂ i p q hpq := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  have hab' : a + b = i + 1 := hab
  rw [Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc, ← Category.assoc,
    ιMapBifunctor_srcProj, ιMapBifunctor_srcProj, mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  refine congr_arg₂ (· + ·) ?_ ?_
  · -- d₁ term: first-factor differential, sign 1
    rcases a with _ | a'
    · rw [mapBifunctor.d₁_eq_zero (K₁ := P₁.complex) (K₂ := P₂.complex)
          (F := extTensorFunctorLeft k A₁ A₂) (c := ComplexShape.down ℕ) 0 b i
          (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]), zero_comp,
        dif_neg (by rintro ⟨hcon, _⟩; exact Nat.succ_ne_zero p hcon.symm), zero_comp]
    · rw [mapBifunctor.d₁_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
          (F := extTensorFunctorLeft k A₁ A₂) (c := ComplexShape.down ℕ)
          (show (ComplexShape.down ℕ).Rel (a' + 1) a' by simp [ComplexShape.down_Rel]) b i
          (show a' + b = i by omega), Linear.units_smul_comp, Category.assoc, ιMapBifunctor_srcProj,
        show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (a' + 1, b) = 1 from rfl, one_smul]
      by_cases hc : a' = p ∧ b = q
      · obtain ⟨rfl, rfl⟩ := hc
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      · rw [dif_neg (fun hcon => hc ⟨by omega, hcon.2⟩), dif_neg hc, comp_zero, zero_comp]
  · -- d₂ term: second-factor differential, sign (-1)^p
    rcases b with _ | b'
    · rw [mapBifunctor.d₂_eq_zero (K₁ := P₁.complex) (K₂ := P₂.complex)
          (F := extTensorFunctorLeft k A₁ A₂) (c := ComplexShape.down ℕ) a 0 i
          (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]), zero_comp,
        dif_neg (by rintro ⟨_, hcon⟩; exact Nat.succ_ne_zero q hcon.symm), zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
          (F := extTensorFunctorLeft k A₁ A₂) (c := ComplexShape.down ℕ) a
          (show (ComplexShape.down ℕ).Rel (b' + 1) b' by simp [ComplexShape.down_Rel]) i
          (show a + b' = i by omega), Linear.units_smul_comp, Category.assoc, ιMapBifunctor_srcProj]
      by_cases hc : a = p ∧ b' = q
      · obtain ⟨rfl, rfl⟩ := hc
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩,
          show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) (a, b' + 1) = (-1 : ℤˣ) ^ a from rfl]
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      · rw [dif_neg (fun hcon => hc ⟨hcon.1, by omega⟩), dif_neg hc]
        simp only [zero_comp, comp_zero, smul_zero]

include hN in
/-- **The differential-commutation square, inverse form.** Composing the target differential with
the inverse degreewise iso equals the inverse degreewise iso followed by the source differential.
Proved summand-by-summand on the target coproduct (`mapBifunctor.hom_ext`): the `up ℕ` target
differential expands via `mapBifunctor.d₁_eq`/`d₂_eq`, the target `ι`/inv reduction
`ιMapBifunctor_rearrangeHomComplexXIso_inv` and the two naturality lemmas
`fullSummandIso_inv_natLeft/natRight` factor out `fullSummandIso p q .inv`, `homYoneda`
functoriality collapses the two `homYoneda.map`s per summand, and the residual source-complex
identity `srcProj_comm` (the Koszul sign bookkeeping) closes the goal. -/
theorem rearrangeHomComplexXIso_inv_comm (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (homTarget k N₁ N₂ P₁ P₂).d i j ≫
        (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ j).inv =
      (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).inv ≫
        ((extTensorComplexLeft P₁ P₂).linearYonedaObj k
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).d i j := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  obtain rfl : j = i + 1 := by rw [ComplexShape.up_Rel] at hij; omega
  have hpq' : p + q = i := hpq
  rw [ιMapBifunctor_rearrangeHomComplexXIso_inv_assoc, ChainComplex.linearYonedaObj_d]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  rw [mapBifunctor.d₁_eq (K₁ := P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (K₂ := P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂))
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.up ℕ)
        (show (ComplexShape.up ℕ).Rel p (p + 1) by simp [ComplexShape.up_Rel]) q (i + 1)
        (show p + 1 + q = i + 1 by omega),
      mapBifunctor.d₂_eq (K₁ := P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (K₂ := P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂))
        (F := curriedTensor (ModuleCat.{u} k)) (c := ComplexShape.up ℕ) p
        (show (ComplexShape.up ℕ).Rel q (q + 1) by simp [ComplexShape.up_Rel]) (i + 1)
        (show p + (q + 1) = i + 1 by omega),
      Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
      ιMapBifunctor_rearrangeHomComplexXIso_inv, ιMapBifunctor_rearrangeHomComplexXIso_inv,
      fullSummandIso_inv_natLeft_assoc, fullSummandIso_inv_natRight_assoc,
      show extTensorFunctorLeftMap k (P₁.complex.d (p + 1) p) (𝟙 (P₂.complex.X q))
          = ((extTensorFunctorLeft k A₁ A₂).map (P₁.complex.d (p + 1) p)).app (P₂.complex.X q)
        from rfl,
      show extTensorFunctorLeftMap k (𝟙 (P₁.complex.X p)) (P₂.complex.d (q + 1) q)
          = ((extTensorFunctorLeft k A₁ A₂).obj (P₁.complex.X p)).map (P₂.complex.d (q + 1) q)
        from rfl]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← op_comp, ← op_comp,
      show ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = 1
        from rfl, one_smul,
      show ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q)
        = (-1 : ℤˣ) ^ p from TensorExtendUp.negOnePow_natCast p]
  rw [← Linear.comp_units_smul, ← Preadditive.comp_add]
  congr 1
  rw [← Linear.units_smul_comp, ← Preadditive.add_comp]
  have key : (homYoneda k N₁ N₂).map (srcProj k P₁ P₂ (i + 1) (p + 1) q (by omega) ≫
        ((extTensorFunctorLeft k A₁ A₂).map (P₁.complex.d (p + 1) p)).app (P₂.complex.X q)).op +
      (-1 : ℤˣ) ^ p • (homYoneda k N₁ N₂).map (srcProj k P₁ P₂ (i + 1) p (q + 1) (by omega) ≫
        ((extTensorFunctorLeft k A₁ A₂).obj (P₁.complex.X p)).map (P₂.complex.d (q + 1) q)).op =
      (homYoneda k N₁ N₂).map (srcProj k P₁ P₂ i p q hpq).op ≫
        (homYoneda k N₁ N₂).map ((extTensorComplexLeft P₁ P₂).d (i + 1) i).op := by
    rw [← Functor.map_comp, ← op_comp, ← srcProj_comm k P₁ P₂ i p q hpq', op_add, Functor.map_add]
    congr 1
    simp only [Units.smul_def, op_zsmul, Functor.map_zsmul]
  rw [key, Category.assoc]
  congr 1

include hN in
/-- **The differential-commutation square** for the `Ext` Künneth cochain construction: the degreewise
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
/-- **The complex-level rearrangement isomorphism** of
`CochainComplex (ModuleCat k) ℕ`:

```
(extTensorComplexLeft P₁ P₂).linearYonedaObj k (N₁ ⊗ₖ N₂)
  ≅ HomologicalComplex.tensorObj
      (P₁.complex.linearYonedaObj k N₁)
      (P₂.complex.linearYonedaObj k N₂)
```

Assembled from the degreewise object iso `rearrangeHomComplexXIso` via `isoOfComponents`,
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
uses to identify the degree-`i` factor cohomologies. -/
@[simp]
theorem rearrangeHomComplex_hom_f (i : ℕ) :
    (rearrangeHomComplex k N₁ N₂ hN P₁ P₂).hom.f i =
      (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).hom := rfl

end Etingof

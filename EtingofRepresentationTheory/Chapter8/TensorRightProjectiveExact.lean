import EtingofRepresentationTheory.Chapter8.TensorProjectiveExact

set_option backward.isDefEq.respectTransparency false

/-!
# Tensoring with a projective left module is exact (flatness of projectives, first argument)

The functor `Etingof.tensorRightFunctor A Y : ModuleCat Aᵐᵒᵖ ⥤ AddCommGrpCat`, `M ↦ M ⊗_A Y`
(Definition 8.2.3), sends short exact sequences of right `A`-modules to short exact sequences of
abelian groups whenever the left `A`-module `Y` is projective. This is the mirror image of
`Etingof.tensorLeftFunctor_map_shortExact` (`TensorProjectiveExact.lean`), which fixes a projective
right module and varies the left module; here we fix a projective left module `Y` and vary the
right module `M`. It is the first-argument flatness input the balancing theorem
(Problem 8.2.6(iv)) needs.

## Proof

This mirrors `TensorProjectiveExact.lean`. The varying factor is now the first tensor factor
`M` (the short exact sequence of right modules), so the natural isomorphisms are built with the
first-factor tensor-hom uncurry `homEquivInvFun`, and functoriality in the
fixed projective second factor `Y` is `tensorRightNatTrans`. `Y` projective in `ModuleCat A` is a
retract of a free module `X →₀ A`.

1. **Unit case.** `tensorOver A A M ≅ M` naturally in `M` (the right unitor `M ⊗_A A ≅ M`,
   `m ⊗ a ↦ aᵒᵖ • m`). So `tensorRightFunctor A A` is naturally isomorphic to
   `forget₂ (ModuleCat Aᵐᵒᵖ) AddCommGrpCat`, which is exact.
2. **Free case.** `tensorOver A (X →₀ A) M ≅ (X →₀ M)` naturally in `M`, identifying
   `tensorRightFunctor A (X →₀ A)` with `forget₂ ⋙ (X →₀ -)`; the latter is exact.
3. **Retract case.** A retract of an exact functor preserves short exactness; short exactness
   transfers from the free case along the retract of `Y`.
-/

open CategoryTheory Limits TensorProduct MulOpposite

namespace Etingof

universe u

variable (A : Type u) [Ring A]

/-! ### Unit case: `M ⊗_A A ≅ M` -/

/-- The right-`A`-linear (left-`Aᵐᵒᵖ`-linear) map `M →ₗ (A →+ M)`, `m ↦ (a ↦ aᵒᵖ • m)`, used to
build the right unitor `M ⊗_A A ≅ M`. -/
noncomputable def unitorΦR (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    M →ₗ[Aᵐᵒᵖ] (A →+ M) where
  toFun m :=
    { toFun := fun a => MulOpposite.op a • m
      map_zero' := by rw [MulOpposite.op_zero, zero_smul]
      map_add' := fun a a' => by rw [MulOpposite.op_add, add_smul] }
  map_add' m m' := by ext a; simp [smul_add]
  map_smul' x m := by
    ext a
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, RingHom.id_apply, homMopSMul_apply]
    rw [smul_smul, smul_eq_mul, MulOpposite.op_mul, MulOpposite.op_unop]

@[simp] lemma unitorΦR_apply (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] (m : M) (a : A) :
    unitorΦR A M m a = MulOpposite.op a • m := rfl

/-- The forward map of the right unitor `M ⊗_A A →+ M`, `m ⊗ a ↦ aᵒᵖ • m`. -/
noncomputable def unitorHomR (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    tensorOver A A M →+ M :=
  homEquivInvFun (unitorΦR A M)

@[simp] lemma unitorHomR_mk (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] (m : M) (a : A) :
    unitorHomR A M ((m ⊗ₜ[ℤ] a : TensorProduct ℤ M A) : tensorOver A A M) = MulOpposite.op a • m :=
  rfl

/-- The inverse map of the right unitor `M →+ M ⊗_A A`, `m ↦ m ⊗ 1`. -/
noncomputable def unitorInvR (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    M →+ tensorOver A A M where
  toFun m := ((m ⊗ₜ[ℤ] (1 : A) : TensorProduct ℤ M A) : tensorOver A A M)
  map_zero' := by simp
  map_add' m m' := by
    rw [add_tmul]
    exact map_add (QuotientAddGroup.mk' _) _ _

/-- The right unitor `M ⊗_A A ≅ M` as an additive equivalence. -/
noncomputable def unitorEquivR (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    tensorOver A A M ≃+ M where
  toFun := unitorHomR A M
  invFun := unitorInvR A M
  left_inv := by
    have h : (unitorInvR A M).comp (unitorHomR A M) = AddMonoidHom.id _ := by
      apply tensorOver_hom_ext
      intro m a
      rw [AddMonoidHom.comp_apply, unitorHomR_mk, AddMonoidHom.id_apply]
      change (((MulOpposite.op a • m) ⊗ₜ[ℤ] (1 : A) : TensorProduct ℤ M A) : tensorOver A A M) = _
      rw [mk_smul_tmul (MulOpposite.op a) m 1, MulOpposite.unop_op, smul_eq_mul, mul_one]
    intro z
    rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
  right_inv m := by
    change unitorHomR A M ((m ⊗ₜ[ℤ] (1 : A) : TensorProduct ℤ M A) : tensorOver A A M) = m
    rw [unitorHomR_mk, MulOpposite.op_one, one_smul]
  map_add' := map_add _

@[simp] lemma unitorEquivR_apply (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] (m : M) (a : A) :
    unitorEquivR A M ((m ⊗ₜ[ℤ] a : TensorProduct ℤ M A) : tensorOver A A M)
      = MulOpposite.op a • m := rfl

/-- The natural isomorphism `tensorRightFunctor A A ≅ forget₂ (ModuleCat Aᵐᵒᵖ) AddCommGrpCat`
witnessing the right unitor `M ⊗_A A ≅ M`. -/
noncomputable def unitorNatIsoR :
    tensorRightFunctor A A ≅ forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun M => AddEquiv.toAddCommGrpIso (unitorEquivR A M))
    (by
      intro M M' f
      apply AddCommGrpCat.hom_ext
      apply tensorOver_hom_ext
      intro m a
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        AddCommGrpCat.hom_ofHom, AddEquiv.toAddCommGrpIso_hom, AddEquiv.coe_toAddMonoidHom,
        ModuleCat.forget₂_map]
      exact (map_smul f.hom (MulOpposite.op a) m).symm)

/-- **Unit case.** Tensoring a short exact sequence with the regular left module `A` is short
exact: `tensorRightFunctor A A ≅ forget₂`, and the forgetful functor `ModuleCat Aᵐᵒᵖ ⥤
AddCommGrpCat` is exact. -/
lemma unit_map_shortExactR {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    (S.map (tensorRightFunctor A A)).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (unitorNatIsoR A)).symm
    (hS.map_of_exact (forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u}))

/-! ### Functoriality of `tensorRightFunctor` in the left module -/

/-- The bifunctor `Y ↦ (M ↦ M ⊗_A Y)` from left `A`-modules to functors `ModuleCat Aᵐᵒᵖ ⥤
AddCommGrpCat`. Its value at `Y` is `tensorRightFunctor A Y`, and it is functorial in `Y` via
`tensorRightNatTrans`. -/
noncomputable def tensorRightBifunctor :
    ModuleCat.{u} A ⥤ (ModuleCat.{u} Aᵐᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj Y := tensorRightFunctor A Y
  map {Y Y'} g := tensorRightNatTrans A g.hom
  map_id Y := by
    refine NatTrans.ext (funext fun M => ?_)
    apply AddCommGrpCat.hom_ext
    apply tensorOver_hom_ext
    intro m y
    rfl
  map_comp {Y Y' Y''} g g' := by
    refine NatTrans.ext (funext fun M => ?_)
    apply AddCommGrpCat.hom_ext
    apply tensorOver_hom_ext
    intro m y
    rfl

/-- A retract `P ◁ F` of left `A`-modules induces a retract of short complexes
`S.map (tensorRightFunctor A P) ◁ S.map (tensorRightFunctor A F)`, natural in `M`. -/
noncomputable def mapRetractR {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} {P F : ModuleCat.{u} A}
    (h : Retract P F) :
    Retract (S.map (tensorRightFunctor A P)) (S.map (tensorRightFunctor A F)) :=
  let hF : Retract (tensorRightFunctor A P) (tensorRightFunctor A F) :=
    h.map (tensorRightBifunctor A)
  { i := S.mapNatTrans hF.i
    r := S.mapNatTrans hF.r
    retract := ShortComplex.hom_ext _ _
      (NatTrans.congr_app hF.retract S.X₁)
      (NatTrans.congr_app hF.retract S.X₂)
      (NatTrans.congr_app hF.retract S.X₃) }

/-! ### Free case: `M ⊗_A (X →₀ A) ≅ (X →₀ M)`

The functor `tensorRightFunctor A ((free A).obj X)` (tensoring with the free left module
`X →₀ A = ⊕_X A`) is naturally isomorphic to `forget₂ ⋙ (X →₀ -)`. The endofunctor `X →₀ -` of
abelian groups is exact, so the composite preserves short exactness. -/

/-- The right-`A`-linear map `M →ₗ ((X →₀ A) →+ (X →₀ M))`, `m ↦ (single x a ↦ single x (aᵒᵖ • m))`,
built by applying `unitorΦR A M m` coordinatewise. Uncurried it is the forward map of
`(X →₀ A) ⊗ M ≅ (X →₀ M)`. -/
noncomputable def freeΦR (X M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    M →ₗ[Aᵐᵒᵖ] ((X →₀ A) →+ (X →₀ M)) where
  toFun m := Finsupp.mapRange.addMonoidHom (unitorΦR A M m)
  map_add' m m' := by
    apply Finsupp.addHom_ext
    intro x a
    simp [Finsupp.mapRange.addMonoidHom, Finsupp.mapRange_single]
  map_smul' x m := by
    apply Finsupp.addHom_ext
    intro y a
    simp only [Finsupp.mapRange.addMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Finsupp.mapRange_single, unitorΦR_apply, RingHom.id_apply, homMopSMul_apply,
      Finsupp.smul_single]
    rw [smul_smul, smul_eq_mul, MulOpposite.op_mul, MulOpposite.op_unop]

@[simp] lemma freeΦR_single_apply (X M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (m : M) (x : X) (a : A) :
    freeΦR A X M m (Finsupp.single x a) = Finsupp.single x (MulOpposite.op a • m) := by
  simp [freeΦR, Finsupp.mapRange.addMonoidHom, Finsupp.mapRange_single]

/-- The inverse map `M →+ (X →₀ A) ⊗_A M`, `m ↦ m ⊗ (single x 1)`, for a fixed `x`. -/
noncomputable def freeInvAuxR (X M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] (x : X) :
    M →+ tensorOver A (X →₀ A) M where
  toFun m := ((m ⊗ₜ[ℤ] Finsupp.single x (1 : A) :
    TensorProduct ℤ M (X →₀ A)) : tensorOver A (X →₀ A) M)
  map_zero' := by simp
  map_add' m m' := by rw [add_tmul]; exact map_add (QuotientAddGroup.mk' _) _ _

/-- The isomorphism `M ⊗_A (X →₀ A) ≃+ (X →₀ M)`, `m ⊗ single x a ↦ single x (aᵒᵖ • m)`. -/
noncomputable def freeEquivR (X M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    tensorOver A (X →₀ A) M ≃+ (X →₀ M) where
  toFun := homEquivInvFun (freeΦR A X M)
  invFun := Finsupp.liftAddHom (fun x => freeInvAuxR A X M x)
  left_inv := by
    have h : (Finsupp.liftAddHom (fun x => freeInvAuxR A X M x)).comp
        (homEquivInvFun (freeΦR A X M)) = AddMonoidHom.id _ := by
      apply tensorOver_hom_ext
      intro m p
      rw [AddMonoidHom.comp_apply, homEquivInvFun_mk, AddMonoidHom.id_apply]
      induction p using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq =>
        rw [show freeΦR A X M m (p + q) = freeΦR A X M m p + freeΦR A X M m q from map_add _ p q,
          map_add, hp, hq, tmul_add]
        exact (map_add (QuotientAddGroup.mk' _) _ _).symm
      | single x a =>
        rw [freeΦR_single_apply]
        change Finsupp.liftAddHom (fun x => freeInvAuxR A X M x) (Finsupp.single x _) = _
        rw [Finsupp.liftAddHom_apply_single]
        change (((MulOpposite.op a • m) ⊗ₜ[ℤ] Finsupp.single x (1 : A) :
            TensorProduct ℤ M (X →₀ A)) : tensorOver A (X →₀ A) M) = _
        rw [mk_smul_tmul (MulOpposite.op a) m (Finsupp.single x 1), MulOpposite.unop_op,
          Finsupp.smul_single, smul_eq_mul, mul_one]
    intro z
    rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
  right_inv := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | single x m =>
      rw [Finsupp.liftAddHom_apply_single]
      change homEquivInvFun (freeΦR A X M) ((m ⊗ₜ[ℤ] Finsupp.single x (1 : A) :
          TensorProduct ℤ M (X →₀ A)) : tensorOver A (X →₀ A) M) = _
      rw [homEquivInvFun_mk, freeΦR_single_apply, MulOpposite.op_one, one_smul]
  map_add' := map_add _

@[simp] lemma freeEquivR_mk (X M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M]
    (m : M) (p : X →₀ A) :
    freeEquivR A X M ((m ⊗ₜ[ℤ] p : TensorProduct ℤ M (X →₀ A)) : tensorOver A (X →₀ A) M)
      = freeΦR A X M m p :=
  rfl

/-- Naturality lemma for `freeNatIsoR`: an `Aᵐᵒᵖ`-linear `f : M →ₗ M'` commutes with `freeΦR`. -/
lemma mapRange_freeΦR (X : Type u) {M M' : Type u} [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup M'] [Module Aᵐᵒᵖ M'] (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (p : X →₀ A) :
    Finsupp.mapRange.addMonoidHom f.toAddMonoidHom (freeΦR A X M m p) = freeΦR A X M' (f m) p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [show freeΦR A X M m (p + q) = freeΦR A X M m p + freeΦR A X M m q from map_add _ p q,
      show freeΦR A X M' (f m) (p + q) = freeΦR A X M' (f m) p + freeΦR A X M' (f m) q from
        map_add _ p q, map_add, hp, hq]
  | single x a =>
    rw [freeΦR_single_apply, freeΦR_single_apply]
    change Finsupp.mapRange f.toAddMonoidHom (map_zero _) (Finsupp.single x _) = _
    rw [Finsupp.mapRange_single]
    exact congrArg (Finsupp.single x) (f.map_smul (MulOpposite.op a) m)

/-- The natural isomorphism `tensorRightFunctor A (X →₀ A) ≅ forget₂ ⋙ (X →₀ -)`. -/
noncomputable def freeNatIsoR (X : Type u) :
    tensorRightFunctor A ((ModuleCat.free A).obj X) ≅
      forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u} ⋙ finsuppFunctor X :=
  NatIso.ofComponents (fun M => AddEquiv.toAddCommGrpIso (freeEquivR A X M))
    (by
      intro M M' f
      apply AddCommGrpCat.hom_ext
      apply tensorOver_hom_ext
      intro m p
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        AddCommGrpCat.hom_ofHom, AddEquiv.toAddCommGrpIso_hom, AddEquiv.coe_toAddMonoidHom,
        Functor.comp_map, ModuleCat.forget₂_map]
      exact (mapRange_freeΦR A X f.hom m p).symm)

/-- **Free case.** Tensoring a short exact sequence with a free left module `X →₀ A` is short
exact.

`tensorOver A (X →₀ A) M ≅ (X →₀ M)` naturally in `M` (`freeNatIsoR`), identifying
`tensorRightFunctor A ((free A).obj X)` with `forget₂ ⋙ (X →₀ -)`; the latter is exact because
`forget₂` is exact and `X →₀ -` is exact (`finsupp_map_shortExact`). -/
lemma free_map_shortExactR (X : Type u)
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    (S.map (tensorRightFunctor A ((ModuleCat.free A).obj X))).ShortExact := by
  have hforget : (S.map (forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u})).ShortExact :=
    hS.map_of_exact (forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u})
  have hfs : (S.map (forget₂ (ModuleCat.{u} Aᵐᵒᵖ) AddCommGrpCat.{u} ⋙
      finsuppFunctor X)).ShortExact :=
    finsupp_map_shortExact X hforget
  exact ShortComplex.shortExact_of_iso (S.mapNatIso (freeNatIsoR A X)).symm hfs

/-- **First-argument flatness of a projective left module.** Tensoring a short exact sequence of
right `A`-modules with a projective left `A`-module `Y` is short exact: `- ⊗_A Y` preserves short
exactness. This is the first-argument flatness input the balancing theorem
(Problem 8.2.6(iv)) depends on.

`Y` projective is a retract of the free module `↑Y →₀ A` (the counit epimorphism of the
free/forget adjunction, split by projectivity); short exactness transfers from the free case along
the retract (`mapRetractR` + `shortExact_of_retract`). -/
theorem tensorRightFunctor_map_shortExact (Y : ModuleCat.{u} A) [Projective Y]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    (S.map (tensorRightFunctor A Y)).ShortExact := by
  let ε : (ModuleCat.free A).obj ((forget (ModuleCat.{u} A)).obj Y) ⟶ Y :=
    (ModuleCat.adj A).counit.app Y
  have h : Retract Y ((ModuleCat.free A).obj ((forget (ModuleCat.{u} A)).obj Y)) :=
    { i := Projective.factorThru (𝟙 Y) ε
      r := ε
      retract := Projective.factorThru_comp (𝟙 Y) ε }
  exact shortExact_of_retract (mapRetractR A h) (free_map_shortExactR A _ hS)

end Etingof

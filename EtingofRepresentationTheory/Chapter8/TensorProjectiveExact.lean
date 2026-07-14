import EtingofRepresentationTheory.Chapter8.Problem8_2_6
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.Retract

/-!
# Tensoring with a projective right module is exact (flatness of projectives)

The functor `Etingof.tensorLeftFunctor A P : ModuleCat A ⥤ AddCommGrpCat`, `N ↦ P ⊗_A N`
(Problem 8.2.6, `Problem8_2_6.lean`), sends short exact sequences of left `A`-modules to short
exact sequences of abelian groups whenever the right `A`-module `P` is **projective**. This is the
flatness input the `Tor` long exact sequence in the second argument (Problem 8.2.6(iii)) and the
balancing theorem (Problem 8.2.6(iv), #6583) depend on.

## Proof route

`P` projective in `ModuleCat Aᵐᵒᵖ` is a retract of a free module `⊕_ι Aᵐᵒᵖ`.

1. **Unit case.** `tensorOver A N (of Aᵐᵒᵖ Aᵐᵒᵖ) ≅ N` naturally in `N` (the left unitor
   `Aᵐᵒᵖ ⊗_A N ≅ N`, `x ⊗ n ↦ x.unop • n`). So `tensorLeftFunctor A (of Aᵐᵒᵖ)` is naturally
   isomorphic to `forget₂ (ModuleCat A) AddCommGrpCat`, which is exact.
2. **Free case.** A coproduct of exact functors is exact.
3. **Retract case.** A retract of an exact functor preserves short exactness (mono/epi/exact all
   transfer along a retract of short complexes).
-/

open CategoryTheory Limits TensorProduct MulOpposite

namespace Etingof

universe u

variable (A : Type u) [Ring A]

/-! ### `ShortExact` is stable under retracts -/

/-- A short complex `T` that is a retract of a short exact complex `U` is itself short exact.
Monomorphisms, epimorphisms, and exactness (vanishing of homology) all transfer along the
retract. -/
lemma shortExact_of_retract {D : Type*} [Category.{u} D] [Abelian D]
    {T U : ShortComplex D} (h : Retract T U) (hU : U.ShortExact) : T.ShortExact := by
  have e₁ : h.i.τ₁ ≫ h.r.τ₁ = 𝟙 _ := by
    rw [← ShortComplex.comp_τ₁, h.retract, ShortComplex.id_τ₁]
  have e₂ : h.i.τ₂ ≫ h.r.τ₂ = 𝟙 _ := by
    rw [← ShortComplex.comp_τ₂, h.retract, ShortComplex.id_τ₂]
  have e₃ : h.i.τ₃ ≫ h.r.τ₃ = 𝟙 _ := by
    rw [← ShortComplex.comp_τ₃, h.retract, ShortComplex.id_τ₃]
  have hf : RetractArrow T.f U.f :=
    { i := Arrow.homMk h.i.τ₁ h.i.τ₂ h.i.comm₁₂
      r := Arrow.homMk h.r.τ₁ h.r.τ₂ h.r.comm₁₂
      retract := Arrow.hom_ext _ _ e₁ e₂ }
  have hg : RetractArrow T.g U.g :=
    { i := Arrow.homMk h.i.τ₂ h.i.τ₃ h.i.comm₂₃
      r := Arrow.homMk h.r.τ₂ h.r.τ₃ h.r.comm₂₃
      retract := Arrow.hom_ext _ _ e₂ e₃ }
  have hexact : T.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    have hz : IsZero U.homology := by
      rw [← ShortComplex.exact_iff_isZero_homology]; exact hU.exact
    have hr : Retract T.homology U.homology := h.map (ShortComplex.homologyFunctor D)
    rw [IsZero.iff_id_eq_zero, ← hr.retract, hz.eq_of_tgt hr.i 0, Limits.zero_comp]
  have hmono : Mono T.f :=
    MorphismProperty.of_retract (P := MorphismProperty.monomorphisms D) hf hU.mono_f
  have hepi : Epi T.g :=
    MorphismProperty.of_retract (P := MorphismProperty.epimorphisms D) hg hU.epi_g
  exact ShortComplex.ShortExact.mk' hexact hmono hepi

/-! ### Unit case: `Aᵐᵒᵖ ⊗_A N ≅ N` -/

/-- The right-`Aᵐᵒᵖ`-linear map `Aᵐᵒᵖ →ₗ (N →+ N)`, `x ↦ (n ↦ x.unop • n)`, used to build the
left unitor `Aᵐᵒᵖ ⊗_A N ≅ N`. -/
noncomputable def unitorΦ (N : Type u) [AddCommGroup N] [Module A N] :
    Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] (N →+ N) where
  toFun x := DistribSMul.toAddMonoidHom N x.unop
  map_add' x y := by ext n; simp [MulOpposite.unop_add, add_smul]
  map_smul' a x := by
    ext n
    simp only [DistribSMul.toAddMonoidHom_apply, RingHom.id_apply, homMopSMul_apply]
    rw [smul_eq_mul, MulOpposite.unop_mul, mul_smul]

@[simp] lemma unitorΦ_apply (N : Type u) [AddCommGroup N] [Module A N] (x : Aᵐᵒᵖ) (n : N) :
    unitorΦ A N x n = x.unop • n := rfl

/-- The forward map of the left unitor `Aᵐᵒᵖ ⊗_A N →+ N`, `x ⊗ n ↦ x.unop • n`. -/
noncomputable def unitorHom (N : Type u) [AddCommGroup N] [Module A N] :
    tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) →+ N :=
  homEquivInvFun (unitorΦ A N)

@[simp] lemma unitorHom_mk (N : Type u) [AddCommGroup N] [Module A N] (x : Aᵐᵒᵖ) (n : N) :
    unitorHom A N ((x ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) : tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))
      = x.unop • n := rfl

/-- The inverse map of the left unitor `N →+ Aᵐᵒᵖ ⊗_A N`, `n ↦ 1 ⊗ n`. -/
noncomputable def unitorInv (N : Type u) [AddCommGroup N] [Module A N] :
    N →+ tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) where
  toFun n := ((1 ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) : tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))
  map_zero' := by simp
  map_add' n n' := by
    rw [tmul_add]
    exact map_add (QuotientAddGroup.mk' _) _ _

/-- The left unitor `Aᵐᵒᵖ ⊗_A N ≅ N` as an additive equivalence. -/
noncomputable def unitorEquiv (N : Type u) [AddCommGroup N] [Module A N] :
    tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) ≃+ N where
  toFun := unitorHom A N
  invFun := unitorInv A N
  left_inv := by
    have h : (unitorInv A N).comp (unitorHom A N) = AddMonoidHom.id _ := by
      apply tensorOver_hom_ext
      intro x n
      rw [AddMonoidHom.comp_apply, unitorHom_mk, AddMonoidHom.id_apply]
      change ((1 ⊗ₜ[ℤ] (x.unop • n) : TensorProduct ℤ Aᵐᵒᵖ N) :
          tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) = _
      rw [← mk_smul_tmul x 1 n, smul_eq_mul, mul_one]
    intro z
    rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
  right_inv n := by
    change unitorHom A N ((1 ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) :
      tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) = n
    rw [unitorHom_mk, MulOpposite.unop_one, one_smul]
  map_add' := map_add _

@[simp] lemma unitorEquiv_apply (N : Type u) [AddCommGroup N] [Module A N] (x : Aᵐᵒᵖ) (n : N) :
    unitorEquiv A N ((x ⊗ₜ[ℤ] n : TensorProduct ℤ Aᵐᵒᵖ N) :
      tensorOver A N (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) = x.unop • n := rfl

/-- The natural isomorphism `tensorLeftFunctor A (of Aᵐᵒᵖ) ≅ forget₂ (ModuleCat A) AddCommGrpCat`
witnessing the left unitor `Aᵐᵒᵖ ⊗_A N ≅ N`. -/
noncomputable def unitorNatIso :
    tensorLeftFunctor A (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) ≅ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun N => AddEquiv.toAddCommGrpIso (unitorEquiv A N))
    (by
      intro N N' g
      apply AddCommGrpCat.hom_ext
      apply tensorOver_hom_ext
      intro x n
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        tensorLeftFunctor, AddCommGrpCat.hom_ofHom, AddEquiv.toAddCommGrpIso_hom,
        ModuleCat.forget₂_map]
      rw [AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_toAddMonoidHom, tensorSndMap_mk]
      exact (map_smul g.hom x.unop n).symm)

/-- **Unit case.** Tensoring a short exact sequence with the regular right module `Aᵐᵒᵖ` (i.e.
`A` as a right `A`-module) is short exact: `tensorLeftFunctor A (of Aᵐᵒᵖ) ≅ forget₂`, and the
forgetful functor `ModuleCat A ⥤ AddCommGrpCat` is exact. -/
lemma unit_map_shortExact {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (S.map (tensorLeftFunctor A (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (unitorNatIso A)).symm
    (hS.map_of_exact (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))

/-! ### Functoriality of `tensorLeftFunctor` in the right module -/

/-- A right `A`-module map `f : M ⟶ M'` induces a natural transformation
`tensorLeftFunctor A M ⟶ tensorLeftFunctor A M'`, applying `f` to the left tensor factor. Its
components are `tensorRightMap`. -/
noncomputable def tensorLeftNatTrans {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    tensorLeftFunctor A M ⟶ tensorLeftFunctor A M' where
  app N := AddCommGrpCat.ofHom (tensorRightMap A N f)
  naturality {N N'} g := by
    apply AddCommGrpCat.hom_ext
    apply tensorOver_hom_ext
    intro m n
    rfl

/-- The bifunctor `M ↦ (N ↦ M ⊗_A N)` from right `A`-modules to functors `ModuleCat A ⥤
AddCommGrpCat`. Its value at `M` is `tensorLeftFunctor A M`, and it is functorial in `M` via
`tensorLeftNatTrans`. -/
noncomputable def tensorBifunctor :
    ModuleCat.{u} Aᵐᵒᵖ ⥤ (ModuleCat.{u} A ⥤ AddCommGrpCat.{u}) where
  obj M := tensorLeftFunctor A M
  map f := tensorLeftNatTrans A f
  map_id M := by
    refine NatTrans.ext (funext fun N => ?_)
    apply AddCommGrpCat.hom_ext
    apply tensorOver_hom_ext
    intro m n
    rfl
  map_comp {M M' M''} f f' := by
    refine NatTrans.ext (funext fun N => ?_)
    apply AddCommGrpCat.hom_ext
    apply tensorOver_hom_ext
    intro m n
    rfl

/-- A retract `P ◁ F` of right `A`-modules induces a retract of short complexes
`S.map (tensorLeftFunctor A P) ◁ S.map (tensorLeftFunctor A F)`, natural in `N`. -/
noncomputable def mapRetract {S : ShortComplex (ModuleCat.{u} A)} {P F : ModuleCat.{u} Aᵐᵒᵖ}
    (h : Retract P F) :
    Retract (S.map (tensorLeftFunctor A P)) (S.map (tensorLeftFunctor A F)) :=
  let hF : Retract (tensorLeftFunctor A P) (tensorLeftFunctor A F) := h.map (tensorBifunctor A)
  { i := S.mapNatTrans hF.i
    r := S.mapNatTrans hF.r
    retract := ShortComplex.hom_ext _ _
      (NatTrans.congr_app hF.retract S.X₁)
      (NatTrans.congr_app hF.retract S.X₂)
      (NatTrans.congr_app hF.retract S.X₃) }

/-! ### Free case and assembly -/

/-- **Free case.** Tensoring a short exact sequence with a free right module `X →₀ Aᵐᵒᵖ`
(a coproduct of copies of the regular module `Aᵐᵒᵖ`) is short exact.

Intended proof route (#6587 residual): `tensorOver A N (X →₀ Aᵐᵒᵖ) ≅ (X →₀ N)` naturally in `N`
— from the unit iso `Aᵐᵒᵖ ⊗_A N ≅ N` (`unitorNatIso`) and the commutation of `⊗_A` with the
coproduct `X →₀ Aᵐᵒᵖ = ⊕_X Aᵐᵒᵖ` (`tensorRightFunctor A N` is a left adjoint, `tensorHomAdjunction`,
so preserves coproducts). This identifies `tensorLeftFunctor A ((free Aᵐᵒᵖ).obj X)` with
`forget₂ ⋙ (X →₀ -)`, which is exact because `X →₀ -` (a coproduct) is an exact functor of
abelian groups (AB4/AB5). -/
lemma free_map_shortExact (X : Type u)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (S.map (tensorLeftFunctor A ((ModuleCat.free Aᵐᵒᵖ).obj X))).ShortExact := by
  sorry

/-- **Problem 8.2.6 flatness crux (#6587).** Tensoring a short exact sequence of left `A`-modules
with a *projective* right `A`-module `P` is short exact: `P ⊗_A -` preserves short exactness. This
is the flatness input the `Tor` long exact sequence in the second argument (Problem 8.2.6(iii)) and
the balancing theorem (Problem 8.2.6(iv), #6583) depend on.

`P` projective is a retract of the free module `↑P →₀ Aᵐᵒᵖ` (the counit epimorphism of the
free/forget adjunction, split by projectivity); short exactness transfers from the free case along
the retract (`mapRetract` + `shortExact_of_retract`). -/
theorem tensorLeftFunctor_map_shortExact (P : ModuleCat.{u} Aᵐᵒᵖ) [Projective P]
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (S.map (tensorLeftFunctor A P)).ShortExact := by
  let ε : (ModuleCat.free Aᵐᵒᵖ).obj ((forget (ModuleCat.{u} Aᵐᵒᵖ)).obj P) ⟶ P :=
    (ModuleCat.adj Aᵐᵒᵖ).counit.app P
  have h : Retract P ((ModuleCat.free Aᵐᵒᵖ).obj ((forget (ModuleCat.{u} Aᵐᵒᵖ)).obj P)) :=
    { i := Projective.factorThru (𝟙 P) ε
      r := ε
      retract := Projective.factorThru_comp (𝟙 P) ε }
  exact shortExact_of_retract (mapRetract A h) (free_map_shortExact A _ hS)

end Etingof

import EtingofRepresentationTheory.Chapter8.Problem8_2_6_Core
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Retract
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Tensoring with a projective right module is exact (flatness of projectives)

The functor `Etingof.tensorLeftFunctor A P : ModuleCat A ⥤ AddCommGrpCat`, `N ↦ P ⊗_A N`
(Problem 8.2.6, `Problem8_2_6.lean`), sends short exact sequences of left `A`-modules to short
exact sequences of abelian groups whenever the right `A`-module `P` is projective. This is the
flatness input the `Tor` long exact sequence in the second argument (Problem 8.2.6(iii)) and the
balancing theorem (Problem 8.2.6(iv)) depend on.

## Proof

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

/-! ### Free case: `(X →₀ Aᵐᵒᵖ) ⊗_A N ≅ (X →₀ N)`

The functor `tensorLeftFunctor A ((free Aᵐᵒᵖ).obj X)` (tensoring with the free right module
`X →₀ Aᵐᵒᵖ = ⊕_X Aᵐᵒᵖ`) is naturally isomorphic to `forget₂ ⋙ (X →₀ -)`. The endofunctor
`X →₀ -` of abelian groups is exact, so the composite preserves short exactness. -/

/-- The endofunctor `B ↦ (X →₀ B)` of abelian groups, acting on morphisms by `Finsupp.mapRange`.
It is exact (`finsupp_map_shortExact`). -/
noncomputable def finsuppFunctor (X : Type u) : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj B := AddCommGrpCat.of (X →₀ B)
  map {B B'} g := AddCommGrpCat.ofHom (Finsupp.mapRange.addMonoidHom g.hom)
  map_id B := by
    apply AddCommGrpCat.hom_ext
    simp only [AddCommGrpCat.hom_ofHom, AddCommGrpCat.hom_id, Finsupp.mapRange.addMonoidHom_id]
  map_comp {B B' B''} g h := by
    apply AddCommGrpCat.hom_ext
    simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
      Finsupp.mapRange.addMonoidHom_comp]

@[simp] lemma finsuppFunctor_map_apply (X : Type u) {B B' : AddCommGrpCat.{u}} (g : B ⟶ B')
    (p : X →₀ B) :
    ((finsuppFunctor X).map g).hom p = Finsupp.mapRange.addMonoidHom g.hom p :=
  rfl

instance (X : Type u) : (finsuppFunctor X).PreservesZeroMorphisms where
  map_zero B B' := by
    apply AddCommGrpCat.hom_ext
    change Finsupp.mapRange.addMonoidHom (0 : ↑B →+ ↑B') = 0
    apply Finsupp.addHom_ext
    intro x b
    simp [Finsupp.mapRange.addMonoidHom, Finsupp.mapRange_single]

/-- **Exactness of `X →₀ -`.** Applying `finsuppFunctor X` to a short exact sequence of abelian
groups yields a short exact sequence: `Finsupp.mapRange` preserves injections, surjections, and
exactness (checked coordinatewise). -/
lemma finsupp_map_shortExact (X : Type u) {T : ShortComplex AddCommGrpCat.{u}}
    (hT : T.ShortExact) : (T.map (finsuppFunctor X)).ShortExact := by
  have hf : Function.Injective T.f.hom := by
    have := hT.mono_f; rwa [AddCommGrpCat.mono_iff_injective] at this
  have hg : Function.Surjective T.g.hom := by
    have := hT.epi_g; rwa [AddCommGrpCat.epi_iff_surjective] at this
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.ab_exact_iff]
    intro p hp
    change X →₀ ↑T.X₂ at p
    change Finsupp.mapRange.addMonoidHom T.g.hom p = 0 at hp
    have hpx : ∀ x, T.g.hom (p x) = 0 := by
      intro x
      have hx := DFunLike.congr_fun hp x
      simpa [Finsupp.mapRange_apply] using hx
    have hchoose : ∀ x, ∃ y, T.f.hom y = p x := fun x =>
      T.ab_exact_iff.mp hT.exact (p x) (hpx x)
    choose c hc using hchoose
    refine ⟨∑ x ∈ p.support, Finsupp.single x (c x), ?_⟩
    change Finsupp.mapRange.addMonoidHom T.f.hom (∑ x ∈ p.support, Finsupp.single x (c x)) = p
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun x _ => by
      change Finsupp.mapRange T.f.hom (map_zero _) (Finsupp.single x (c x)) = Finsupp.single x (p x)
      rw [Finsupp.mapRange_single, hc])]
    exact Finsupp.sum_single p
  · rw [AddCommGrpCat.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) hf
  · rw [AddCommGrpCat.epi_iff_surjective]
    exact Finsupp.mapRange_surjective _ (map_zero _) hg

/-- The right-`Aᵐᵒᵖ`-linear map `(X →₀ Aᵐᵒᵖ) →ₗ (N →+ (X →₀ N))` sending
`single x a ↦ (n ↦ single x (a.unop • n))`. Built via `Finsupp.lift` from `x ↦ singleAddHom x`;
uncurried it is the forward map of `(X →₀ Aᵐᵒᵖ) ⊗_A N ≅ (X →₀ N)`. -/
noncomputable def freeΦ (X N : Type u) [AddCommGroup N] [Module A N] :
    (X →₀ Aᵐᵒᵖ) →ₗ[Aᵐᵒᵖ] (N →+ (X →₀ N)) :=
  Finsupp.lift (N →+ (X →₀ N)) Aᵐᵒᵖ X (fun x => Finsupp.singleAddHom x)

lemma freeΦ_single (X N : Type u) [AddCommGroup N] [Module A N] (x : X) (a : Aᵐᵒᵖ) :
    freeΦ A X N (Finsupp.single x a) = a • Finsupp.singleAddHom x := by
  simp only [freeΦ, Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul]

@[simp] lemma freeΦ_single_apply (X N : Type u) [AddCommGroup N] [Module A N]
    (x : X) (a : Aᵐᵒᵖ) (n : N) :
    freeΦ A X N (Finsupp.single x a) n = Finsupp.single x (a.unop • n) := by
  rw [freeΦ_single, homMopSMul_apply]; rfl

/-- The inverse map `N →+ (X →₀ Aᵐᵒᵖ) ⊗_A N`, `n ↦ (single x 1) ⊗ n`, for a fixed `x`. -/
noncomputable def freeInvAux (X N : Type u) [AddCommGroup N] [Module A N] (x : X) :
    N →+ tensorOver A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ)) where
  toFun n := ((Finsupp.single x (1 : Aᵐᵒᵖ) ⊗ₜ[ℤ] n :
    TensorProduct ℤ (X →₀ Aᵐᵒᵖ) N) : tensorOver A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ)))
  map_zero' := by simp
  map_add' n n' := by rw [tmul_add]; exact map_add (QuotientAddGroup.mk' _) _ _

/-- The isomorphism `(X →₀ Aᵐᵒᵖ) ⊗_A N ≃+ (X →₀ N)`, `single x a ⊗ n ↦ single x (a.unop • n)`. -/
noncomputable def freeEquiv (X N : Type u) [AddCommGroup N] [Module A N] :
    tensorOver A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ)) ≃+ (X →₀ N) where
  toFun := homEquivInvFun (freeΦ A X N)
  invFun := Finsupp.liftAddHom (fun x => freeInvAux A X N x)
  left_inv := by
    have h : (Finsupp.liftAddHom (fun x => freeInvAux A X N x)).comp
        (homEquivInvFun (freeΦ A X N)) = AddMonoidHom.id _ := by
      apply tensorOver_hom_ext
      intro m n
      rw [AddMonoidHom.comp_apply, homEquivInvFun_mk, AddMonoidHom.id_apply]
      induction m using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq =>
        rw [show freeΦ A X N (p + q) n = freeΦ A X N p n + freeΦ A X N q n by rw [map_add]; rfl,
          map_add, hp, hq, add_tmul]
        exact (map_add (QuotientAddGroup.mk' _) _ _).symm
      | single x a =>
        rw [freeΦ_single_apply]
        change Finsupp.liftAddHom (fun x => freeInvAux A X N x) (Finsupp.single x (a.unop • n)) = _
        rw [Finsupp.liftAddHom_apply_single]
        change ((Finsupp.single x (1 : Aᵐᵒᵖ) ⊗ₜ[ℤ] (a.unop • n) :
            TensorProduct ℤ (X →₀ Aᵐᵒᵖ) N) : tensorOver A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ))) = _
        rw [← mk_smul_tmul a (Finsupp.single x 1) n, Finsupp.smul_single, smul_eq_mul, mul_one]
    intro z
    rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]
  right_inv := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | single x n =>
      rw [Finsupp.liftAddHom_apply_single]
      change homEquivInvFun (freeΦ A X N) ((Finsupp.single x (1 : Aᵐᵒᵖ) ⊗ₜ[ℤ] n :
          TensorProduct ℤ (X →₀ Aᵐᵒᵖ) N) : tensorOver A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ))) = _
      rw [homEquivInvFun_mk, freeΦ_single_apply, MulOpposite.unop_one, one_smul]
  map_add' := map_add _

@[simp] lemma freeEquiv_mk (X N : Type u) [AddCommGroup N] [Module A N]
    (m : X →₀ Aᵐᵒᵖ) (n : N) :
    freeEquiv A X N ((m ⊗ₜ[ℤ] n : TensorProduct ℤ (X →₀ Aᵐᵒᵖ) N) :
      tensorOver A N (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ))) = freeΦ A X N m n :=
  rfl

/-- Naturality lemma for `freeNatIso`: an `A`-linear `g : N →ₗ N'` commutes with `freeΦ`. -/
lemma mapRange_freeΦ (X : Type u) {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') (m : X →₀ Aᵐᵒᵖ) (n : N) :
    Finsupp.mapRange.addMonoidHom g.toAddMonoidHom (freeΦ A X N m n) = freeΦ A X N' m (g n) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [show freeΦ A X N (p + q) n = freeΦ A X N p n + freeΦ A X N q n by rw [map_add]; rfl,
      show freeΦ A X N' (p + q) (g n) = freeΦ A X N' p (g n) + freeΦ A X N' q (g n) by
        rw [map_add]; rfl,
      map_add, hp, hq]
  | single x a =>
    rw [freeΦ_single_apply, freeΦ_single_apply]
    change Finsupp.mapRange g.toAddMonoidHom (map_zero _) (Finsupp.single x (a.unop • n)) = _
    rw [Finsupp.mapRange_single]
    exact congrArg (Finsupp.single x) (g.map_smul a.unop n)

/-- The natural isomorphism `tensorLeftFunctor A (X →₀ Aᵐᵒᵖ) ≅ forget₂ ⋙ (X →₀ -)`. -/
noncomputable def freeNatIso (X : Type u) :
    tensorLeftFunctor A (ModuleCat.of Aᵐᵒᵖ (X →₀ Aᵐᵒᵖ)) ≅
      forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ finsuppFunctor X :=
  NatIso.ofComponents (fun N => AddEquiv.toAddCommGrpIso (freeEquiv A X N))
    (by
      intro N N' g
      apply AddCommGrpCat.hom_ext
      apply tensorOver_hom_ext
      intro m n
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
        tensorLeftFunctor, AddCommGrpCat.hom_ofHom, AddEquiv.toAddCommGrpIso_hom,
        AddEquiv.coe_toAddMonoidHom, Functor.comp_map, ModuleCat.forget₂_map]
      exact (mapRange_freeΦ A X g.hom m n).symm)

/-- **Free case.** Tensoring a short exact sequence with a free right module `X →₀ Aᵐᵒᵖ`
(a coproduct of copies of the regular module `Aᵐᵒᵖ`) is short exact.

`tensorOver A N (X →₀ Aᵐᵒᵖ) ≅ (X →₀ N)` naturally in `N` (`freeNatIso`), identifying
`tensorLeftFunctor A ((free Aᵐᵒᵖ).obj X)` with `forget₂ ⋙ (X →₀ -)`; the latter is exact because
`forget₂` is exact and `X →₀ -` is exact (`finsupp_map_shortExact`). -/
lemma free_map_shortExact (X : Type u)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (S.map (tensorLeftFunctor A ((ModuleCat.free Aᵐᵒᵖ).obj X))).ShortExact := by
  have hforget : (S.map (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).ShortExact :=
    hS.map_of_exact (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
  have hfs : (S.map (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ⋙ finsuppFunctor X)).ShortExact :=
    finsupp_map_shortExact X hforget
  exact ShortComplex.shortExact_of_iso (S.mapNatIso (freeNatIso A X)).symm hfs

/-- **Problem 8.2.6 flatness.** Tensoring a short exact sequence of left `A`-modules
with a projective right `A`-module `P` is short exact: `P ⊗_A -` preserves short exactness. This
is the flatness input the `Tor` long exact sequence in the second argument (Problem 8.2.6(iii)) and
the balancing theorem (Problem 8.2.6(iv)) depend on.

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

/-- **Higher `Tor` (balancing side) vanishes on projective right modules.** The `(n+1)`-st left
derived functor of `P ⊗_A -` (`tensorLeftFunctor A P`) vanishes at every left `A`-module `N` when
the right module `P` is projective. Since `P ⊗_A -` is exact (`tensorLeftFunctor_map_shortExact`),
applying it to a projective resolution of `N` keeps the resolution exact in positive degrees, so its
homology (the derived functor) vanishes above degree `0`. This is the balancing-side vanishing
input to the balancing theorem (Problem 8.2.6(iv)), matching the `Etingof.Tor`-side vanishing
`Functor.isZero_leftDerived_obj_projective_succ`. -/
lemma isZero_tensorLeftFunctor_leftDerived_succ
    (P : ModuleCat.{u} Aᵐᵒᵖ) [Projective P]
    (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ) :
    IsZero ((Functor.leftDerived (tensorLeftFunctor A P) (n + 1)).obj (ModuleCat.of A N)) := by
  -- `P ⊗_A -` is exact, hence preserves homology.
  haveI : (tensorLeftFunctor A P).PreservesHomology :=
    ((Functor.exact_tfae (tensorLeftFunctor A P)).out 0 2).mp
      (fun _ hS => tensorLeftFunctor_map_shortExact A P hS)
  -- Compute the derived functor from a projective resolution of `N`.
  let R : ProjectiveResolution (ModuleCat.of A N) := ProjectiveResolution.of _
  refine IsZero.of_iso ?_ (R.isoLeftDerivedObj (tensorLeftFunctor A P) (n + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  -- The resolution is exact in positive degrees; an exact functor preserves that exactness.
  have hex : (R.complex.sc (n + 1)).Exact := by
    have := R.complex_exactAt_succ n
    rwa [HomologicalComplex.exactAt_iff] at this
  exact hex.map (tensorLeftFunctor A P)

end Etingof

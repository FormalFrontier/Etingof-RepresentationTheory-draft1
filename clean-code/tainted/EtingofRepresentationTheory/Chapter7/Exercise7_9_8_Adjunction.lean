import EtingofRepresentationTheory.Chapter6.Definition6_6_3_Functor
import EtingofRepresentationTheory.Chapter6.Definition6_6_4_Functor
import EtingofRepresentationTheory.Chapter7.Exercise7_9_7
import EtingofRepresentationTheory.Chapter7.Exercise7_9_8

/-!
# Exercise 7.9.8: the reflection-functor adjunction

This file packages the componentwise hom-set equivalence from `Exercise7_9_8.lean` as the
categorical adjunction `F_i^- ⊣ F_i^+`.  The right adjoint includes the canonical transport
from the twice-reversed quiver back to the original quiver.  Naturality is proved through
the shared reduced-data model used by the componentwise construction.
-/

noncomputable section

open CategoryTheory

namespace Etingof.QuiverRepresentation

/-- Transport a morphism of representations along an equality of quiver instances. -/
def transportHom
    {k Q : Type*} [CommSemiring k] {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    {X Y : @Etingof.QuiverRepresentation k Q _ I₁}
    (f : @Etingof.QuiverRepresentationHom k Q _ I₁ X Y) :
    @Etingof.QuiverRepresentationHom k Q _ I₂ (h ▸ X) (h ▸ Y) := by
  subst h
  exact f

/-- Transport representations functorially along an equality of quiver instances. -/
def transportFunctor
    {k Q : Type*} [CommSemiring k] {I₁ I₂ : Quiver Q} (h : I₁ = I₂) :
    @Etingof.QuiverRepresentation k Q _ I₁ ⥤ @Etingof.QuiverRepresentation k Q _ I₂ where
  obj X := h ▸ X
  map f := transportHom h f
  map_id X := by subst h; rfl
  map_comp f g := by subst h; rfl

@[simp]
theorem transportFunctor_obj
    {k Q : Type*} [CommSemiring k] {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    (X : @Etingof.QuiverRepresentation k Q _ I₁) :
    (transportFunctor h).obj X = h ▸ X := by
  subst h
  rfl

/-- The vertex map of a transported morphism is the original vertex map, through the
canonical transport charts. -/
theorem objTransportEquiv_map_app
    {k Q : Type*} [CommSemiring k] {I₁ I₂ : Quiver Q} (h : I₁ = I₂)
    {X Y : @Etingof.QuiverRepresentation k Q _ I₁} (f : X ⟶ Y) (v : Q)
    (x : @Etingof.QuiverRepresentation.obj k Q _ I₂ ((transportFunctor h).obj X) v) :
    objTransportEquiv h Y v (((transportFunctor h).map f).app v x) =
      @Etingof.QuiverRepresentationHom.app k Q _ I₁ X Y f v
        (objTransportEquiv h X v x) := by
  subst h
  rfl

/-- Functorial transport from the twice-reversed quiver back to the original quiver. -/
def transportReversedTwiceFunctor
    {k Q : Type*} [CommSemiring k] [DecidableEq Q] [Quiver Q] (i : Q) :
    @Etingof.QuiverRepresentation k Q _
        (@Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i) ⥤
      Etingof.QuiverRepresentation k Q :=
  transportFunctor (Etingof.reversedAtVertex_twice Q i)

@[simp]
theorem transportReversedTwiceFunctor_obj
    {k Q : Type*} [CommSemiring k] [DecidableEq Q] [Quiver Q] (i : Q)
    (X : @Etingof.QuiverRepresentation k Q _
      (@Etingof.reversedAtVertex Q _ (Etingof.reversedAtVertex Q i) i)) :
    (transportReversedTwiceFunctor i).obj X = transportReversedTwice X :=
  transportFunctor_obj (Etingof.reversedAtVertex_twice Q i) X

end Etingof.QuiverRepresentation

namespace Etingof

variable {k Q : Type*} [CommRing k] [DecidableEq Q] [instQ : Quiver Q]
  {i : Q} (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]

/-- `F_i^- : Rep(Q) ⥤ Rep(Q̄_i)`, with the source hypothesis fixed. -/
abbrev reflectionFunctorMinusAdjunctionLeft :
    Etingof.QuiverRepresentation k Q ⥤
      @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i) :=
  Etingof.reflectionFunctorMinusFunctor k Q i hi

/-- `F_i^+ : Rep(Q̄_i) ⥤ Rep(Q)`, including transport through double reversal. -/
abbrev reflectionFunctorPlusAdjunctionRight :
    @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i) ⥤
      Etingof.QuiverRepresentation k Q :=
  (@Etingof.reflectionFunctorPlusFunctor k _ Q _ (Etingof.reversedAtVertex Q i) i
      (Etingof.isSource_reversedAtVertex_isSink hi)) ⋙
    Etingof.QuiverRepresentation.transportReversedTwiceFunctor i

/-- Away from `i`, this is the canonical chart from the transported value of `F_i^+ W`
back to `W`. It is the chart used by the reduced-data hom equivalence. -/
def reflectionPlusTransportEquiv
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
    (v : Q) (hv : v ≠ i) :
    @Etingof.QuiverRepresentation.obj k Q _ instQ
        ((reflectionFunctorPlusAdjunctionRight hi).obj W) v ≃ₗ[k]
      @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i) W v :=
  (Etingof.QuiverRepresentation.transportReversedTwiceEquiv
      (@Etingof.reflectionFunctorPlus k _ Q _ (Etingof.reversedAtVertex Q i) i
        (Etingof.isSource_reversedAtVertex_isSink hi) W) v).trans
    (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _ (Etingof.reversedAtVertex Q i) i
      (Etingof.isSource_reversedAtVertex_isSink hi) W v hv)

/-- The componentwise equivalence from Exercise 7.9.8, now exposed as the hom equivalence
between the actual functors. -/
def reflectionFunctorHomEquiv
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)) :
    ((reflectionFunctorMinusAdjunctionLeft hi).obj V ⟶ W) ≃
      (V ⟶ (reflectionFunctorPlusAdjunctionRight hi).obj W) :=
  (Etingof.homFMinusEquivReducedEquiv hi V W).trans
    (Etingof.homTransportPlusEquivReducedEquiv hi V W).symm

@[simp]
theorem homFMinusEquivReducedEquiv_apply_h
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
    (f : (reflectionFunctorMinusAdjunctionLeft hi).obj V ⟶ W)
    (v : Q) (hv : v ≠ i) :
    ((Etingof.homFMinusEquivReducedEquiv hi V W) f).h v hv =
      (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
          _ _ f v).comp
        (Etingof.reflFunctorMinus_equivAt_ne hi V v hv).symm.toLinearMap := by
  rfl

@[simp]
theorem homFMinusEquivReducedEquiv_symm_apply_app_ne
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
    (r : Etingof.AdjReducedData hi V W) (v : Q) (hv : v ≠ i) :
    (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i) _ _
        ((Etingof.homFMinusEquivReducedEquiv hi V W).symm r) v) =
      (r.h v hv).comp (Etingof.reflFunctorMinus_equivAt_ne hi V v hv).toLinearMap := by
  ext x
  simp [Etingof.homFMinusEquivReducedEquiv, hv]

@[simp]
theorem homTransportPlusEquivReducedEquiv_apply_h
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
    (g : V ⟶ (reflectionFunctorPlusAdjunctionRight hi).obj W)
    (v : Q) (hv : v ≠ i) :
    ((Etingof.homTransportPlusEquivReducedEquiv hi V W) g).h v hv =
      (reflectionPlusTransportEquiv hi W v hv).toLinearMap.comp (g.app v) := by
  rfl

@[simp]
theorem homTransportPlusEquivReducedEquiv_symm_apply_app_ne
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
    (r : Etingof.AdjReducedData hi V W) (v : Q) (hv : v ≠ i) :
    (((Etingof.homTransportPlusEquivReducedEquiv hi V W).symm r).app v) =
      (reflectionPlusTransportEquiv hi W v hv).symm.toLinearMap.comp (r.h v hv) := by
  ext x
  simp only [Etingof.homTransportPlusEquivReducedEquiv, ne_eq, LinearEquiv.trans_symm,
    eq_mpr_eq_cast, cast_eq, Equiv.symm_mk, Equiv.coe_fn_mk, hv, ↓reduceDIte,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply]
  change _ = (reflectionPlusTransportEquiv hi W v hv).symm (r.h v hv x)
  rfl

omit [Fintype (Etingof.ArrowsOutOf Q i)] in
/-- The transport chart intertwines the morphism action of the right-adjoint functor
with the original component map away from the reflected vertex. -/
theorem reflectionPlusTransportEquiv_map_app
    {W W' : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)}
    (g : W ⟶ W') (v : Q) (hv : v ≠ i)
    (x : @Etingof.QuiverRepresentation.obj k Q _ instQ
      ((reflectionFunctorPlusAdjunctionRight hi).obj W) v) :
    reflectionPlusTransportEquiv hi W' v hv
        (((reflectionFunctorPlusAdjunctionRight hi).map g).app v x) =
      (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
        W W' g v) (reflectionPlusTransportEquiv hi W v hv x) := by
  let hi' := Etingof.isSource_reversedAtVertex_isSink hi
  let h := Etingof.reversedAtVertex_twice Q i
  change (@Etingof.reflFunctorPlus_equivAt_ne k _ Q _
      (Etingof.reversedAtVertex Q i) i hi' W' v hv)
      (Etingof.QuiverRepresentation.objTransportEquiv h _ v
        ((@Etingof.QuiverRepresentationHom.app k Q _ instQ _ _
          ((Etingof.QuiverRepresentation.transportFunctor h).map
            (@Etingof.reflectionFunctorPlusMap k _ Q _
              (Etingof.reversedAtVertex Q i) i hi' W W' g)) v) x)) =
    (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
      W W' g v)
      ((@Etingof.reflFunctorPlus_equivAt_ne k _ Q _
        (Etingof.reversedAtVertex Q i) i hi' W v hv)
        (Etingof.QuiverRepresentation.objTransportEquiv h _ v x))
  rw [Etingof.QuiverRepresentation.objTransportEquiv_map_app]
  exact @Etingof.reflectionFunctorPlusMap_app_ne k _ Q _
    (Etingof.reversedAtVertex Q i) i
    (Etingof.isSource_reversedAtVertex_isSink hi) W W' g v hv _

/-- The forward hom equivalence agrees with the original componentwise construction away
from the reflected vertex. -/
theorem reflectionFunctorHomEquiv_apply_app_ne
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
    (f : (reflectionFunctorMinusAdjunctionLeft hi).obj V ⟶ W)
    (v : Q) (hv : v ≠ i) (x : V.obj v) :
    reflectionPlusTransportEquiv hi W v hv
        ((reflectionFunctorHomEquiv hi V W f).app v x) =
      (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
        _ _ f v) ((Etingof.reflFunctorMinus_equivAt_ne hi V v hv).symm x) := by
  change reflectionPlusTransportEquiv hi W v hv
      (((Etingof.homTransportPlusEquivReducedEquiv hi V W).symm
        ((Etingof.homFMinusEquivReducedEquiv hi V W) f)).app v x) = _
  rw [homTransportPlusEquivReducedEquiv_symm_apply_app_ne hi V W _ v hv]
  rw [homFMinusEquivReducedEquiv_apply_h]
  change reflectionPlusTransportEquiv hi W v hv
      ((reflectionPlusTransportEquiv hi W v hv).symm
        ((@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
          _ _ f v) ((Etingof.reflFunctorMinus_equivAt_ne hi V v hv).symm x))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The inverse hom equivalence agrees with the original componentwise construction away
from the reflected vertex. -/
theorem reflectionFunctorHomEquiv_symm_apply_app_ne
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
    (g : V ⟶ (reflectionFunctorPlusAdjunctionRight hi).obj W)
    (v : Q) (hv : v ≠ i)
    (x : @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi V) v) :
    (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i) _ _
      ((reflectionFunctorHomEquiv hi V W).symm g) v) x =
      reflectionPlusTransportEquiv hi W v hv
        (g.app v (Etingof.reflFunctorMinus_equivAt_ne hi V v hv x)) := by
  change (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
      _ _ ((Etingof.homFMinusEquivReducedEquiv hi V W).symm
        ((Etingof.homTransportPlusEquivReducedEquiv hi V W) g)) v) x = _
  rw [homFMinusEquivReducedEquiv_symm_apply_app_ne hi V W _ v hv]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    homTransportPlusEquivReducedEquiv_apply_h]

/-- The map of the left-adjoint functor is the original vertex map in the standard
off-vertex charts. -/
theorem reflectionFunctorMinusAdjunctionLeft_map_app_ne
    {V' V : Etingof.QuiverRepresentation k Q} (f : V' ⟶ V)
    (v : Q) (hv : v ≠ i)
    (x : @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      ((reflectionFunctorMinusAdjunctionLeft hi).obj V') v) :
    Etingof.reflFunctorMinus_equivAt_ne hi V v hv
        ((@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i) _ _
          ((reflectionFunctorMinusAdjunctionLeft hi).map f) v) x) =
      f.app v (Etingof.reflFunctorMinus_equivAt_ne hi V' v hv x) :=
  Etingof.reflectionFunctorMinusMap_app_ne hi f v hv x

/-- Naturality of the componentwise hom equivalence in the representation variable. -/
theorem reflectionFunctorHomEquiv_naturality_left_symm
    {V' V : Etingof.QuiverRepresentation k Q}
    {W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)}
    (f : V' ⟶ V) (g : V ⟶ (reflectionFunctorPlusAdjunctionRight hi).obj W) :
    (reflectionFunctorHomEquiv hi V' W).symm (f ≫ g) =
      (reflectionFunctorMinusAdjunctionLeft hi).map f ≫
      (reflectionFunctorHomEquiv hi V W).symm g := by
  dsimp only [reflectionFunctorMinusAdjunctionLeft]
  apply (Etingof.homFMinusEquivReducedEquiv hi V' W).injective
  apply Etingof.AdjReducedData.ext
  funext v hv
  apply LinearMap.ext
  intro x
  rw [homFMinusEquivReducedEquiv_apply_h hi V' W _ v hv,
    homFMinusEquivReducedEquiv_apply_h hi V' W _ v hv]
  simp only [LinearMap.comp_apply,
    Etingof.QuiverRepresentation.comp_app]
  rw [reflectionFunctorHomEquiv_symm_apply_app_ne hi V' W (f ≫ g) v hv,
    reflectionFunctorHomEquiv_symm_apply_app_ne hi V W g v hv]
  rw [reflectionFunctorMinusAdjunctionLeft_map_app_ne]
  simp

/-- Naturality of the componentwise hom equivalence in the reflected representation variable. -/
theorem reflectionFunctorHomEquiv_naturality_right
    {V : Etingof.QuiverRepresentation k Q}
    {W W' : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)}
    (f : (reflectionFunctorMinusAdjunctionLeft hi).obj V ⟶ W) (g : W ⟶ W') :
    reflectionFunctorHomEquiv hi V W' (f ≫ g) =
      reflectionFunctorHomEquiv hi V W f ≫
        (reflectionFunctorPlusAdjunctionRight hi).map g := by
  dsimp only [reflectionFunctorPlusAdjunctionRight]
  apply (Etingof.homTransportPlusEquivReducedEquiv hi V W').injective
  apply Etingof.AdjReducedData.ext
  funext v hv
  apply LinearMap.ext
  intro x
  rw [homTransportPlusEquivReducedEquiv_apply_h,
    homTransportPlusEquivReducedEquiv_apply_h]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Etingof.QuiverRepresentation.comp_app]
  rw [reflectionFunctorHomEquiv_apply_app_ne,
    reflectionPlusTransportEquiv_map_app,
    reflectionFunctorHomEquiv_apply_app_ne]
  rfl

/-- The natural hom-set equivalence underlying the reflection-functor adjunction. -/
def reflectionFunctorCoreHomEquiv :
    CategoryTheory.Adjunction.CoreHomEquiv
      (reflectionFunctorMinusAdjunctionLeft (k := k) hi)
      (reflectionFunctorPlusAdjunctionRight (k := k) hi) where
  homEquiv := reflectionFunctorHomEquiv (k := k) (Q := Q) hi
  homEquiv_naturality_left_symm :=
    reflectionFunctorHomEquiv_naturality_left_symm (k := k) (Q := Q) hi
  homEquiv_naturality_right :=
    reflectionFunctorHomEquiv_naturality_right (k := k) (Q := Q) hi

/-- Exercise 7.9.8(a): the negative reflection functor is left adjoint to the
positive reflection functor (transported through double reversal). -/
def reflectionFunctorAdjunction :
    reflectionFunctorMinusAdjunctionLeft (k := k) hi ⊣
      reflectionFunctorPlusAdjunctionRight (k := k) hi :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    (reflectionFunctorCoreHomEquiv (k := k) (Q := Q) hi)

/-- The adjunction's hom equivalence is definitionally the componentwise equivalence
constructed above. -/
@[simp]
theorem reflectionFunctorAdjunction_homEquiv
    (V : Etingof.QuiverRepresentation k Q)
    (W : @Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i)) :
    (reflectionFunctorAdjunction (k := k) (Q := Q) hi).homEquiv V W =
      reflectionFunctorHomEquiv (k := k) hi V W := by
  rw [reflectionFunctorAdjunction, CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Exercise 7.9.8(b), left-adjoint half: `F_i^-` is right exact. -/
theorem reflectionFunctorMinus_rightExact :
    Etingof.RightExactFunctor (reflectionFunctorMinusAdjunctionLeft (k := k) hi) := by
  haveI := (reflectionFunctorAdjunction (k := k) (Q := Q) hi).leftAdjoint_preservesColimits
  infer_instance

set_option linter.unusedFintypeInType false in
/-- Exercise 7.9.8(b), right-adjoint half: `F_i^+` is left exact. -/
theorem reflectionFunctorPlus_leftExact :
    Etingof.LeftExactFunctor (reflectionFunctorPlusAdjunctionRight (k := k) hi) := by
  haveI := (reflectionFunctorAdjunction (k := k) (Q := Q) hi).rightAdjoint_preservesLimits
  infer_instance

/-- Exercise 7.9.8(b): the two exactness consequences of the reflection-functor
adjunction. This is the general categorical content of Exercise 7.9.7 and does not
require separately installing abelian-category instances for quiver representations. -/
theorem Exercise7_9_8_exactness :
    Etingof.RightExactFunctor (reflectionFunctorMinusAdjunctionLeft (k := k) hi) ∧
      Etingof.LeftExactFunctor (reflectionFunctorPlusAdjunctionRight (k := k) hi) :=
  ⟨reflectionFunctorMinus_rightExact (k := k) hi,
    reflectionFunctorPlus_leftExact (k := k) hi⟩

end Etingof

end

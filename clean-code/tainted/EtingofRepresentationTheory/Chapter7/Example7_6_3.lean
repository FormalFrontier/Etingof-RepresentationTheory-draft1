import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.FDRep
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import EtingofRepresentationTheory.Chapter2.Problem2_14_3

/-!
# Example 7.6.3: Examples of Adjoint Functors

1. For a finite dimensional representation V of a group G or Lie algebra g,
   V ⊗ - and V* ⊗ - are adjoint functors on the category of representations.
2. Res_K^G is left adjoint to Ind_K^G (Frobenius reciprocity).
3. The Lie algebra functor L : Assoc_k → Lie_k has a left adjoint: the universal
   enveloping algebra functor U.
4. GL₁ : Assoc_k → Groups (A ↦ A×) has left adjoint G ↦ k[G].
5. The tensor algebra functor V ↦ TV is left adjoint to the forgetful functor
   Assoc_k → Vect_k. Similarly, symmetric algebra for commutative algebras.

## Mathlib correspondence

* (1) The category `FDRep k G` of finite dimensional representations is rigid, so
  for each object `V` the functor `tensorLeft V` (i.e. `V ⊗ -`) has both a left and
  a right adjoint, given by tensoring with the dual `Vᘁ` (`= V*`). Both adjunctions
  come from `CategoryTheory.tensorLeftAdjunction` applied to the exact pairings of
  the rigid structure. This is the precise sense in which `V* ⊗ -` is biadjoint to
  `V ⊗ -`.
* (2) Mathlib provides Frobenius reciprocity in *both* adjoint directions. The
  standard hom-set form `Hom_G(Ind M, N) ≅ Hom_K(M, Res N)` is `Rep.indResAdjunction`
  (`Ind ⊣ Res`). The book states the *opposite* direction, `Res ⊣ Ind`; for a
  finite index subgroup `Ind ≅ Coind`, so `Res` is also left adjoint to `Ind`, and
  this is `Rep.resIndAdjunction`. Both are recorded below.
* (3) `Etingof.universalEnvelopingAdjunction` packages the universal property as the
  genuine adjunction `U ⊣ L` between bundled Lie algebras and associative algebras.
* (4) `Etingof.groupAlgebraAdjunction` packages `k[-] ⊣ GL₁`.
* (5) `Etingof.tensorAlgebraAdjunction` and `Etingof.symmetricAlgebraAdjunction`
  package the tensor- and symmetric-algebra adjunctions. Their categorical Hom
  equivalences are natural in both variables by construction.

For Lie-algebra representations, this file supplies `Etingof.FDLieRep`, its tensoring
functors, the natural adjunction `Etingof.tensorLieRightAdjunction`, and the reverse
adjunction `Etingof.tensorLieLeftAdjunction` transported through double duality. Thus
tensoring with `V` and tensoring with `V⁺` are genuinely biadjoint.
-/

open CategoryTheory MonoidalCategory

universe u v

-- v4.31: `LieRing.ofAssociativeRing` is no longer a global instance (only file-local in Mathlib);
-- re-enable it locally so the Lie structure on `End`/`Module.End` is found.
attribute [local instance] LieRing.ofAssociativeRing

/-! ## (1) Tensoring with `V` and with its dual `V*` are biadjoint

For a finite dimensional representation `V`, `V ⊗ -` has `V* ⊗ -` as both a left and
a right adjoint. We work in `FDRep k G`, which is a rigid monoidal category, and use
the right dual `Vᘁ` as the formalization of `V*`. -/

/-- One half of Example 7.6.3(1): for a finite dimensional representation `V`, the
functor `V* ⊗ -` is left adjoint to `V ⊗ -`. Here `Vᘁ` is the dual representation. -/
noncomputable def Etingof.tensor_dual_adjunction_left
    (k : Type u) (G : Type v) [Field k] [Group G] (V : FDRep k G) :
    tensorLeft (Vᘁ) ⊣ tensorLeft V :=
  tensorLeftAdjunction V Vᘁ

/-- The other half of Example 7.6.3(1): for a finite dimensional representation `V`, the
functor `V ⊗ -` is left adjoint to `V* ⊗ -`. Equivalently, `V* ⊗ -` is *right* adjoint
to `V ⊗ -`. Combined with `tensor_dual_adjunction_left`, this shows `V* ⊗ -` is biadjoint
to `V ⊗ -`. -/
noncomputable def Etingof.tensor_dual_adjunction_right
    (k : Type u) (G : Type v) [Field k] [Group G] (V : FDRep k G) :
    tensorLeft V ⊣ tensorLeft (Vᘁ) :=
  haveI : ExactPairing (Vᘁ) V := BraidedCategory.exactPairing_swap V Vᘁ
  tensorLeftAdjunction (Vᘁ) V

/-! ### Finite-dimensional Lie-algebra representations

Mathlib currently treats Lie modules through typeclasses rather than a bundled
representation category. The following category and functorial constructions make the
finite-dimensional part of Example 7.6.3(1) precise. The final Hom equivalence is the
expected right-adjoint equivalence on objects. The evaluation identities proved below make
it natural in both variables and promote it to both directions of the tensor/dual
biadjunction.
-/

namespace Etingof

/-- The category of finite-dimensional representations of a Lie algebra `L` over a field `k`. -/
structure FDLieRep (k : Type u) [Field k] (L : Type u) [LieRing L] [LieAlgebra k L] where
  /-- The underlying vector space. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module k carrier]
  [lieRingModule : LieRingModule L carrier]
  [lieModule : LieModule k L carrier]
  [finiteDimensional : FiniteDimensional k carrier]

namespace FDLieRep

variable (k : Type u) [Field k] (L : Type u) [LieRing L] [LieAlgebra k L]

attribute [instance] addCommGroup module lieRingModule lieModule finiteDimensional

instance : CoeSort (FDLieRep k L) (Type u) := ⟨carrier⟩

/-- Bundle a finite-dimensional Lie module as an object of `FDLieRep`. -/
abbrev of (V : Type u) [AddCommGroup V] [Module k V] [LieRingModule L V]
    [LieModule k L V] [FiniteDimensional k V] : FDLieRep k L := ⟨V⟩

/-- Morphisms in `FDLieRep` are Lie-module homomorphisms. -/
structure Hom (V W : FDLieRep k L) where
  /-- The underlying Lie-module homomorphism. -/
  hom : V →ₗ⁅k,L⁆ W

instance : Category (FDLieRep k L) where
  Hom := Hom k L
  id _ := ⟨LieModuleHom.id⟩
  comp f g := ⟨g.hom.comp f.hom⟩

/-- Bundle a Lie-module homomorphism as a morphism in `FDLieRep`. -/
abbrev ofHom {V W : Type u} [AddCommGroup V] [Module k V] [LieRingModule L V]
    [LieModule k L V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [LieRingModule L W] [LieModule k L W] [FiniteDimensional k W]
    (f : V →ₗ⁅k,L⁆ W) : of k L V ⟶ of k L W := ⟨f⟩

/-- Two morphisms in `FDLieRep` are equal when their Lie-module maps are equal. -/
theorem hom_ext {V W : FDLieRep k L} {f g : V ⟶ W} (h : f.hom = g.hom) : f = g := by
  match f, g with
  | ⟨f⟩, ⟨g⟩ =>
    cases h
    rfl

@[simp] theorem hom_id (V : FDLieRep k L) : (𝟙 V : V ⟶ V).hom = LieModuleHom.id := rfl

@[simp] theorem hom_comp {U V W : FDLieRep k L} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

end FDLieRep

variable {k : Type u} [Field k] {L : Type u} [LieRing L] [LieAlgebra k L]

/-- The tensor symmetry is an equivalence of Lie modules for the diagonal action. -/
noncomputable def lieTensorComm (V W : FDLieRep k L) :
    TensorProduct k V W ≃ₗ⁅k,L⁆ TensorProduct k W V :=
  { TensorProduct.comm k V W with
    map_lie' := by
      intro x t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul v w => simp [TensorProduct.LieModule.lie_tmul_right, add_comm]
      | add a b ha hb =>
        calc
          (TensorProduct.comm k V W) ⁅x, a + b⁆ =
              (TensorProduct.comm k V W) (⁅x, a⁆ + ⁅x, b⁆) := by rw [lie_add]
          _ = (TensorProduct.comm k V W) ⁅x, a⁆ +
              (TensorProduct.comm k V W) ⁅x, b⁆ := map_add _ _ _
          _ = ⁅x, (TensorProduct.comm k V W) a⁆ +
              ⁅x, (TensorProduct.comm k V W) b⁆ :=
            congrArg₂ (fun p q ↦ p + q) ha hb
          _ = ⁅x, (TensorProduct.comm k V W) a + (TensorProduct.comm k V W) b⁆ := by
            rw [lie_add]
          _ = ⁅x, (TensorProduct.comm k V W) (a + b)⁆ := by rw [map_add] }

@[simp]
theorem lieTensorComm_tmul (V W : FDLieRep k L) (v : V) (w : W) :
    lieTensorComm V W (v ⊗ₜ[k] w) = w ⊗ₜ[k] v := rfl

@[simp]
theorem lieTensorComm_symm_tmul (V W : FDLieRep k L) (w : W) (v : V) :
    (lieTensorComm V W).symm (w ⊗ₜ[k] v) = v ⊗ₜ[k] w := rfl

@[simp]
theorem tensorProductLieMap_tmul {A B C D : Type u}
    [AddCommGroup A] [Module k A] [LieRingModule L A] [LieModule k L A]
    [AddCommGroup B] [Module k B] [LieRingModule L B] [LieModule k L B]
    [AddCommGroup C] [Module k C] [LieRingModule L C] [LieModule k L C]
    [AddCommGroup D] [Module k D] [LieRingModule L D] [LieModule k L D]
    (f : LieModuleHom k L A C) (g : LieModuleHom k L B D) (a : A) (b : B) :
    TensorProduct.LieModule.map f g (a ⊗ₜ[k] b) = f a ⊗ₜ[k] g b := rfl

/-- A finite-dimensional Lie module is Lie-equivariantly isomorphic to its double dual. -/
noncomputable def lieDoubleDualEquiv (V : FDLieRep k L) :
    V ≃ₗ⁅k,L⁆ Module.Dual k (Module.Dual k V) :=
  { Module.evalEquiv k V with
    map_lie' := by
      intro x v
      ext f
      simp }

/-- Tensoring on the left by a fixed finite-dimensional Lie representation. -/
def tensorLieLeftFunctor (V : FDLieRep k L) : FDLieRep k L ⥤ FDLieRep k L where
  obj W := FDLieRep.of k L (TensorProduct k V W)
  map f := FDLieRep.ofHom k L (TensorProduct.LieModule.map LieModuleHom.id f.hom)
  map_id W := by
    apply FDLieRep.hom_ext
    apply LieModuleHom.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
  map_comp f g := by
    apply FDLieRep.hom_ext
    apply LieModuleHom.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb

/-- The contragredient dual of a finite-dimensional Lie representation. -/
noncomputable def lieDual (V : FDLieRep k L) : FDLieRep k L :=
  FDLieRep.of k L (Module.Dual k V)

/-- Precomposition by a Lie-module equivalence, as an equivalence of Hom spaces. -/
def lieCongrHomLeft {A B C : Type u}
    [AddCommGroup A] [Module k A] [LieRingModule L A] [LieModule k L A]
    [AddCommGroup B] [Module k B] [LieRingModule L B] [LieModule k L B]
    [AddCommGroup C] [Module k C] [LieRingModule L C] [LieModule k L C]
    (e : A ≃ₗ⁅k,L⁆ B) : (A →ₗ⁅k,L⁆ C) ≃ₗ[k] (B →ₗ⁅k,L⁆ C) where
  toFun f := f.comp (e.symm : B →ₗ⁅k,L⁆ A)
  invFun g := g.comp (e : A →ₗ⁅k,L⁆ B)
  map_add' f g := by ext; simp [LieModuleHom.comp_apply]
  map_smul' c f := by ext; simp [LieModuleHom.comp_apply]
  left_inv f := by ext; simp [LieModuleHom.comp_apply]
  right_inv g := by ext; simp [LieModuleHom.comp_apply]

/-- The finite-dimensional Lie-equivariant tensor–dual Hom equivalence
`Hom(V ⊗ W, U) ≃ Hom(W, V* ⊗ U)`.

This is the objectwise Hom equivalence underlying the expected adjunction
`V ⊗ - ⊣ V* ⊗ -`. -/
noncomputable def tensorLieRightHomLinearEquiv (V W U : FDLieRep k L) :
    (TensorProduct k V W →ₗ⁅k,L⁆ U) ≃ₗ[k]
      (W →ₗ⁅k,L⁆ TensorProduct k (Module.Dual k V) U) :=
  (lieCongrHomLeft (lieTensorComm V W)).trans
    ((TensorProduct.LieModule.liftLie k L W V U).symm.trans
      ((Problem2_14_3.congrHomRight
          (Problem2_14_3.dualHomEquiv (k := k) (L := L) (W := V) (U := U))).trans
        (Problem2_14_3.congrHomRight (lieTensorComm (FDLieRep.of k L U) (lieDual V)))))

/-- The categorical form of `tensorLieRightHomLinearEquiv`, on objects of `FDLieRep`. -/
noncomputable def tensorLieRightHomEquiv (V W U : FDLieRep k L) :
    ((tensorLieLeftFunctor V).obj W ⟶ U) ≃
      (W ⟶ (tensorLieLeftFunctor (lieDual V)).obj U) where
  toFun f := FDLieRep.ofHom k L (tensorLieRightHomLinearEquiv V W U f.hom)
  invFun g := FDLieRep.ofHom k L ((tensorLieRightHomLinearEquiv V W U).symm g.hom)
  left_inv f := by
    apply FDLieRep.hom_ext
    exact (tensorLieRightHomLinearEquiv V W U).symm_apply_apply f.hom
  right_inv g := by
    apply FDLieRep.hom_ext
    exact (tensorLieRightHomLinearEquiv V W U).apply_symm_apply g.hom

/-- Evaluation formula for the inverse tensor-dual Hom equivalence. -/
theorem tensorLieRightHomLinearEquiv_symm_apply_tmul (V W U : FDLieRep k L)
    (g : LieModuleHom k L W (TensorProduct k (Module.Dual k V) U))
    (v : V) (w : W) :
    (tensorLieRightHomLinearEquiv V W U).symm g (v ⊗ₜ[k] w) =
      dualTensorHom k V U (g w) v := by
  simp only [tensorLieRightHomLinearEquiv, lieCongrHomLeft,
    Problem2_14_3.congrHomRight, Problem2_14_3.dualHomEquiv,
    dualTensorHomEquiv, LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm,
    TensorProduct.comm_symm, LieModuleEquiv.symm_symm, LinearEquiv.symm_mk,
    LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.coe_mk, LieModuleHom.comp_apply,
    LieModuleEquiv.coe_coe, lieTensorComm_tmul,
    TensorProduct.LieModule.liftLie_apply, LieModuleHom.coe_mk,
    LinearEquiv.coe_coe, dualTensorHomEquivOfBasis_apply]
  congr 2
  exact (lieTensorComm (FDLieRep.of k L U) (lieDual V)).apply_symm_apply (g w)

/-- The forward tensor-dual Hom equivalence is characterized by evaluation. -/
theorem dualTensorHom_tensorLieRightHomLinearEquiv_apply (V W U : FDLieRep k L)
    (f : LieModuleHom k L (TensorProduct k V W) U) (w : W) (v : V) :
    dualTensorHom k V U ((tensorLieRightHomLinearEquiv V W U f) w) v =
      f (v ⊗ₜ[k] w) := by
  rw [← tensorLieRightHomLinearEquiv_symm_apply_tmul V W U
      (tensorLieRightHomLinearEquiv V W U f) v w,
    LinearEquiv.symm_apply_apply]

/-- Postcomposition commutes with the canonical evaluation map
`V⁺ ⊗ A → Hom(V,A)`. -/
theorem dualTensorHom_map_right {A B : Type u} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] (V : FDLieRep k L)
    (g : A →ₗ[k] B) (t : TensorProduct k (Module.Dual k V) A) (v : V) :
    dualTensorHom k V B (TensorProduct.map LinearMap.id g t) v =
      g (dualTensorHom k V A t v) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul f a => simp [dualTensorHom_apply]

/-- Tensoring by Lie-isomorphic left factors gives naturally isomorphic functors. -/
noncomputable def tensorLieLeftFunctorIso {V V' : FDLieRep k L}
    (e : LieModuleEquiv k L V V') : tensorLieLeftFunctor V ≅ tensorLieLeftFunctor V' :=
  NatIso.ofComponents
    (fun W =>
      { hom := FDLieRep.ofHom k L (TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id)
        inv := FDLieRep.ofHom k L
          (TensorProduct.LieModule.map e.symm.toLieModuleHom LieModuleHom.id)
        hom_inv_id := by
          apply FDLieRep.hom_ext
          apply LieModuleHom.ext
          intro t
          change TensorProduct.LieModule.map e.symm.toLieModuleHom LieModuleHom.id
              (TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id t) = t
          induction t using TensorProduct.induction_on with
          | zero => simp
          | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
          | tmul v w => simp
        inv_hom_id := by
          apply FDLieRep.hom_ext
          apply LieModuleHom.ext
          intro t
          change TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id
              (TensorProduct.LieModule.map e.symm.toLieModuleHom LieModuleHom.id t) = t
          induction t using TensorProduct.induction_on with
          | zero => simp
          | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
          | tmul v w => simp })
    (fun f => by
      apply FDLieRep.hom_ext
      apply LieModuleHom.ext
      intro t
      change TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id
          (TensorProduct.LieModule.map LieModuleHom.id f.hom t) =
        TensorProduct.LieModule.map LieModuleHom.id f.hom
          (TensorProduct.LieModule.map e.toLieModuleHom LieModuleHom.id t)
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
      | tmul v w => simp)

/-- The genuine finite-dimensional Lie-representation adjunction
`V ⊗ - ⊣ V⁺ ⊗ -`, natural in both module variables. -/
noncomputable def tensorLieRightAdjunction (V : FDLieRep k L) :
    tensorLieLeftFunctor V ⊣ tensorLieLeftFunctor (lieDual V) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := tensorLieRightHomEquiv V
    homEquiv_naturality_left_symm := by
      intro W' W U f g
      apply FDLieRep.hom_ext
      apply LieModuleHom.ext
      intro t
      change ((tensorLieRightHomLinearEquiv V W' U).symm (g.hom.comp f.hom)) t =
        ((tensorLieRightHomLinearEquiv V W U).symm g.hom)
          (TensorProduct.LieModule.map LieModuleHom.id f.hom t)
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb
      | tmul v w =>
        simp [tensorLieRightHomLinearEquiv_symm_apply_tmul]
        rfl
    homEquiv_naturality_right := by
      intro W U U' f g
      apply FDLieRep.hom_ext
      apply LieModuleHom.ext
      intro w
      change tensorLieRightHomLinearEquiv V W U' (g.hom.comp f.hom) w =
        TensorProduct.LieModule.map LieModuleHom.id g.hom
          (tensorLieRightHomLinearEquiv V W U f.hom w)
      apply (dualTensorHomEquiv k V U').injective
      apply LinearMap.ext
      intro v
      simp only [dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply]
      rw [dualTensorHom_tensorLieRightHomLinearEquiv_apply]
      change g.hom (f.hom (v ⊗ₜ[k] w)) =
        dualTensorHom k V U'
          (TensorProduct.map LinearMap.id g.hom.toLinearMap
            (tensorLieRightHomLinearEquiv V W U f.hom w)) v
      rw [dualTensorHom_map_right, dualTensorHom_tensorLieRightHomLinearEquiv_apply]
      rfl
  }

/-- The reverse adjunction `V⁺ ⊗ - ⊣ V ⊗ -`, obtained from the preceding
adjunction for `V⁺` and the Lie-equivariant double-dual equivalence. Together with
`tensorLieRightAdjunction`, this is the finite-dimensional Lie tensor/dual biadjunction. -/
noncomputable def tensorLieLeftAdjunction (V : FDLieRep k L) :
    tensorLieLeftFunctor (lieDual V) ⊣ tensorLieLeftFunctor V :=
  (tensorLieRightAdjunction (lieDual V)).ofNatIsoRight
    (tensorLieLeftFunctorIso (lieDoubleDualEquiv V).symm)

end Etingof

/-! ## (2) Frobenius reciprocity -/

/-- Frobenius reciprocity, standard direction: induction is left adjoint to restriction
for representations. (Etingof Example 7.6.3(2))

Given a group homomorphism `φ : G →* H` over a commutative ring `k`, the induction
functor `Rep.indFunctor k φ` is left adjoint to the restriction functor `Rep.resFunctor φ`.
This is the usual hom-set form `Hom_H(Ind M, N) ≅ Hom_G(M, Res N)`.

Note the book (Example 7.6.3(2)) states the *opposite* adjoint direction, `Res ⊣ Ind`;
see `Etingof.frobenius_reciprocity_res_ind`. For a finite index subgroup both hold because
`Ind ≅ Coind`. -/
noncomputable def Etingof.frobenius_reciprocity
    (k : Type u) {G H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H) :
    Rep.indFunctor k φ ⊣ Rep.resFunctor φ :=
  Rep.indResAdjunction k φ

/-- Frobenius reciprocity, the direction stated in the book: restriction is left adjoint
to induction for a finite index subgroup. (Etingof Example 7.6.3(2))

For a finite index subgroup `S ≤ G`, the restriction functor `Rep.resFunctor S.subtype`
is left adjoint to the induction functor `Rep.indFunctor k S.subtype`. This is exactly
the book's statement "`Res_K^G` is left adjoint to `Ind_K^G`": it holds because for a
finite index subgroup induction and coinduction agree (`Ind ≅ Coind`), and `Res` is
always left adjoint to `Coind`. -/
noncomputable def Etingof.frobenius_reciprocity_res_ind
    (k : Type u) {G : Type v} [CommRing k] [Group G] (S : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel S)] [S.FiniteIndex] :
    Rep.resFunctor S.subtype ⊣ Rep.indFunctor k S.subtype :=
  Rep.resIndAdjunction k S

/-! ## (3) Universal enveloping algebra -/

/-- The universal enveloping algebra functor is left adjoint to the "underlying
Lie algebra" functor, in the sense that Lie algebra homomorphisms L → A correspond
bijectively to algebra homomorphisms U(L) → A. (Etingof Example 7.6.3(3))

This captures the adjunction at the level of hom-sets via an equivalence. -/
def Etingof.uea_adjunction
    (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]
    (A : Type*) [Ring A] [Algebra R A] :
    (L →ₗ⁅R⁆ A) ≃ (UniversalEnvelopingAlgebra R L →ₐ[R] A) :=
  UniversalEnvelopingAlgebra.lift R

/-! ## (4) Group algebra -/

/-- The group algebra functor `G ↦ k[G]` is left adjoint to the functor
`GL₁ : Assoc_k → Groups`, `A ↦ A×`. (Etingof Example 7.6.3(4))

Concretely, for a group `G` and a `k`-algebra `A`, group homomorphisms `G → GL₁(A) = Aˣ`
correspond bijectively to `k`-algebra homomorphisms `k[G] → A`. The bijection sends a
group hom to its extension by linearity (`MonoidAlgebra.lift`); a monoid hom out of a
group automatically lands in the units, which is what relates `G →* Aˣ` to `G →* A`. -/
noncomputable def Etingof.group_algebra_adjunction
    (k : Type*) [CommRing k] (G : Type*) [Group G] (A : Type*) [Ring A] [Algebra k A] :
    (G →* Aˣ) ≃ (MonoidAlgebra k G →ₐ[k] A) :=
  let unitsEquiv : (G →* Aˣ) ≃ (G →* A) :=
    { toFun := fun f => (Units.coeHom A).comp f
      invFun := fun f => f.toHomUnits
      left_inv := fun f => by ext g; simp
      right_inv := fun f => by ext g; simp }
  unitsEquiv.trans (MonoidAlgebra.lift k A G)

/-! ## (5) Tensor and symmetric algebras -/

/-- The tensor algebra functor `V ↦ TV` is left adjoint to the forgetful functor
`Assoc_k → Vect_k`. (Etingof Example 7.6.3(5))

For a `k`-module `V` and a `k`-algebra `A`, linear maps `V → A` correspond bijectively to
`k`-algebra homomorphisms `TV → A`. -/
def Etingof.tensor_algebra_adjunction
    (k : Type*) [CommRing k] (V : Type*) [AddCommMonoid V] [Module k V]
    (A : Type*) [Semiring A] [Algebra k A] :
    (V →ₗ[k] A) ≃ (TensorAlgebra k V →ₐ[k] A) :=
  TensorAlgebra.lift k

/-- The symmetric algebra functor `V ↦ SV` is left adjoint to the forgetful functor
`Comm_k → Vect_k`. (Etingof Example 7.6.3(5))

For a `k`-module `V` and a commutative `k`-algebra `A`, linear maps `V → A` correspond
bijectively to `k`-algebra homomorphisms `SV → A`. -/
def Etingof.symmetric_algebra_adjunction
    (k : Type*) [CommRing k] (V : Type*) [AddCommMonoid V] [Module k V]
    (A : Type*) [CommSemiring A] [Algebra k A] :
    (V →ₗ[k] A) ≃ (SymmetricAlgebra k V →ₐ[k] A) :=
  SymmetricAlgebra.lift

/-! ## Genuine categorical adjunctions for (3)–(5) -/

namespace Etingof

/-! ### Universal enveloping algebra -/

/-- The bundled category of Lie algebras over `R`, with Lie algebra homomorphisms. -/
structure LieAlgCat (R : Type u) [CommRing R] where
  /-- The underlying type. -/
  carrier : Type u
  [lieRing : LieRing carrier]
  [lieAlgebra : LieAlgebra R carrier]

namespace LieAlgCat

variable (R : Type u) [CommRing R]

attribute [instance] lieRing lieAlgebra

instance : CoeSort (LieAlgCat R) (Type u) := ⟨carrier⟩

/-- Bundle a Lie algebra as an object of `LieAlgCat`. -/
abbrev of (L : Type u) [LieRing L] [LieAlgebra R L] : LieAlgCat R := ⟨L⟩

/-- Morphisms of bundled Lie algebras. -/
structure Hom (L M : LieAlgCat R) where
  /-- The underlying Lie algebra homomorphism. -/
  hom : L →ₗ⁅R⁆ M

instance : Category (LieAlgCat R) where
  Hom := Hom R
  id L := ⟨LieHom.id⟩
  comp f g := ⟨g.hom.comp f.hom⟩

@[simp] theorem hom_id (L : LieAlgCat R) : (𝟙 L : L ⟶ L).hom = LieHom.id := rfl

@[simp] theorem hom_comp {L M N : LieAlgCat R} (f : L ⟶ M) (g : M ⟶ N) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- Bundle a Lie algebra homomorphism as a morphism in `LieAlgCat`. -/
abbrev ofHom {L M : Type u} [LieRing L] [LieAlgebra R L]
    [LieRing M] [LieAlgebra R M] (f : L →ₗ⁅R⁆ M) : of R L ⟶ of R M := ⟨f⟩

/-- Extensionality for morphisms of bundled Lie algebras. -/
theorem hom_ext {L M : LieAlgCat R} {f g : L ⟶ M} (h : f.hom = g.hom) : f = g := by
  match f, g with
  | ⟨f⟩, ⟨g⟩ =>
    cases h
    rfl

end LieAlgCat

/-- Send an associative algebra to its commutator Lie algebra. -/
def commutatorLieFunctor (R : Type u) [CommRing R] : AlgCat.{u} R ⥤ LieAlgCat R where
  obj A := LieAlgCat.of R A
  map f := LieAlgCat.ofHom R f.hom.toLieHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The universal enveloping algebra as a functor from Lie algebras to associative algebras. -/
def universalEnvelopingFunctor (R : Type u) [CommRing R] : LieAlgCat R ⥤ AlgCat.{u} R where
  obj L := AlgCat.of R (UniversalEnvelopingAlgebra R L)
  map f := AlgCat.ofHom <| UniversalEnvelopingAlgebra.lift R <|
    (UniversalEnvelopingAlgebra.ι R).comp f.hom
  map_id L := by
    apply AlgCat.hom_ext
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x
    simp
  map_comp f g := by
    apply AlgCat.hom_ext
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x
    simp

/-- The natural Hom equivalence for universal enveloping algebras. -/
def ueaCategoricalHomEquiv (R : Type u) [CommRing R]
    (L : LieAlgCat R) (A : AlgCat.{u} R) :
    ((universalEnvelopingFunctor R).obj L ⟶ A) ≃ (L ⟶ (commutatorLieFunctor R).obj A) where
  toFun f := LieAlgCat.ofHom R ((UniversalEnvelopingAlgebra.lift (A := A) R).symm f.hom)
  invFun g := AlgCat.ofHom ((UniversalEnvelopingAlgebra.lift (A := A) R) g.hom)
  left_inv f := by
    apply AlgCat.hom_ext
    exact (UniversalEnvelopingAlgebra.lift (A := A) R).apply_symm_apply f.hom
  right_inv g := by
    apply LieAlgCat.hom_ext
    exact (UniversalEnvelopingAlgebra.lift (A := A) R).symm_apply_apply g.hom

/-- The genuine adjunction `U ⊣ L` of Example 7.6.3(3). -/
def universalEnvelopingAdjunction (R : Type u) [CommRing R] :
    universalEnvelopingFunctor R ⊣ commutatorLieFunctor R :=
  Adjunction.mkOfHomEquiv {
    homEquiv := ueaCategoricalHomEquiv R
    homEquiv_naturality_left_symm := by
      intro L' L A f g
      apply AlgCat.hom_ext
      change UniversalEnvelopingAlgebra.lift (A := A) R (f ≫ g).hom =
        (UniversalEnvelopingAlgebra.lift (A := A) R g.hom).comp
          (UniversalEnvelopingAlgebra.lift R
            ((UniversalEnvelopingAlgebra.ι R).comp f.hom))
      apply UniversalEnvelopingAlgebra.hom_ext
      ext x
      simp
      rfl
    homEquiv_naturality_right := by
      intro L A A' f g
      apply LieAlgCat.hom_ext
      change (g.hom.comp f.hom).toLieHom.comp (UniversalEnvelopingAlgebra.ι R) =
        g.hom.toLieHom.comp (f.hom.toLieHom.comp (UniversalEnvelopingAlgebra.ι R))
      rfl
  }

/-- The old pointwise UEA equivalence is exactly a component of the categorical one. -/
@[simp] theorem ueaCategoricalHomEquiv_symm_hom
    (R : Type u) [CommRing R] (L A : Type u) [LieRing L] [LieAlgebra R L]
    [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A) :
    ((ueaCategoricalHomEquiv R (LieAlgCat.of R L) (AlgCat.of R A)).symm
      (LieAlgCat.ofHom R f)).hom = uea_adjunction R L A f := rfl

/-! ### Group algebra and units -/

/-- The group-algebra functor `G ↦ k[G]`. -/
noncomputable def groupAlgebraFunctor (k : Type u) [CommRing k] :
    GrpCat.{u} ⥤ AlgCat.{u} k where
  obj G := AlgCat.of k (MonoidAlgebra k G)
  map f := AlgCat.ofHom (MonoidAlgebra.mapDomainAlgHom k k f.hom)
  map_id G := by
    apply AlgCat.hom_ext
    simp
  map_comp f g := by
    apply AlgCat.hom_ext
    simp

/-- The units functor `A ↦ Aˣ`. -/
def unitsFunctor (k : Type u) [CommRing k] : AlgCat.{u} k ⥤ GrpCat.{u} where
  obj A := GrpCat.of Aˣ
  map f := GrpCat.ofHom (Units.map f.hom.toMonoidHom)
  map_id A := by
    apply GrpCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    ext x
    rfl

/-- The natural Hom equivalence between maps out of a group algebra and maps into units. -/
noncomputable def groupAlgebraCategoricalHomEquiv (k : Type u) [CommRing k]
    (G : GrpCat.{u}) (A : AlgCat.{u} k) :
    ((groupAlgebraFunctor k).obj G ⟶ A) ≃ (G ⟶ (unitsFunctor k).obj A) where
  toFun f := GrpCat.ofHom ((group_algebra_adjunction k G A).symm f.hom)
  invFun g := AlgCat.ofHom (group_algebra_adjunction k G A g.hom)
  left_inv f := by
    apply AlgCat.hom_ext
    exact (group_algebra_adjunction k G A).apply_symm_apply f.hom
  right_inv g := by
    apply GrpCat.hom_ext
    exact (group_algebra_adjunction k G A).symm_apply_apply g.hom

/-- The genuine adjunction `k[-] ⊣ GL₁` of Example 7.6.3(4). -/
noncomputable def groupAlgebraAdjunction (k : Type u) [CommRing k] :
    groupAlgebraFunctor k ⊣ unitsFunctor k :=
  Adjunction.mkOfHomEquiv {
    homEquiv := groupAlgebraCategoricalHomEquiv k
    homEquiv_naturality_left_symm := by
      intro G' G A f g
      apply AlgCat.hom_ext
      change MonoidAlgebra.lift k A G'
          ((Units.coeHom A).comp (g.hom.comp f.hom)) =
        (MonoidAlgebra.lift k A G ((Units.coeHom A).comp g.hom)).comp
          (MonoidAlgebra.mapDomainAlgHom k k f.hom)
      apply MonoidAlgebra.algHom_ext
      · intro x
        simp
        rfl
      · ext
    homEquiv_naturality_right := by
      intro G A A' f g
      apply GrpCat.hom_ext
      ext x
      apply Units.ext
      rfl
  }

/-- The old pointwise group-algebra equivalence is a component of the categorical one. -/
@[simp] theorem groupAlgebraCategoricalHomEquiv_symm_hom
    (k : Type u) [CommRing k] (G A : Type u) [Group G] [Ring A] [Algebra k A]
    (f : G →* Aˣ) :
    ((groupAlgebraCategoricalHomEquiv k (GrpCat.of G) (AlgCat.of k A)).symm
      (GrpCat.ofHom f)).hom = group_algebra_adjunction k G A f := rfl

/-! ### Tensor and symmetric algebras -/

/-- The tensor-algebra functor from modules to associative algebras. -/
def tensorAlgebraFunctor (k : Type u) [CommRing k] : ModuleCat.{u} k ⥤ AlgCat.{u} k where
  obj V := AlgCat.of k (TensorAlgebra k V)
  map f := AlgCat.ofHom <| TensorAlgebra.lift k <| (TensorAlgebra.ι k).comp f.hom
  map_id V := by
    apply AlgCat.hom_ext
    apply TensorAlgebra.hom_ext
    ext x
    simp
  map_comp f g := by
    apply AlgCat.hom_ext
    apply TensorAlgebra.hom_ext
    ext x
    simp

/-- The natural Hom equivalence for the tensor algebra. -/
def tensorAlgebraCategoricalHomEquiv (k : Type u) [CommRing k]
    (V : ModuleCat.{u} k) (A : AlgCat.{u} k) :
    ((tensorAlgebraFunctor k).obj V ⟶ A) ≃
      (V ⟶ (forget₂ (AlgCat.{u} k) (ModuleCat.{u} k)).obj A) where
  toFun f := ModuleCat.ofHom ((TensorAlgebra.lift k).symm f.hom)
  invFun g := AlgCat.ofHom (TensorAlgebra.lift (A := A) k g.hom)
  left_inv f := by
    apply AlgCat.hom_ext
    exact (TensorAlgebra.lift k).apply_symm_apply f.hom
  right_inv g := by
    apply ModuleCat.hom_ext
    exact (TensorAlgebra.lift (A := A) k).symm_apply_apply g.hom

/-- The genuine tensor-algebra/forgetful adjunction of Example 7.6.3(5). -/
def tensorAlgebraAdjunction (k : Type u) [CommRing k] :
    tensorAlgebraFunctor k ⊣ forget₂ (AlgCat.{u} k) (ModuleCat.{u} k) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := tensorAlgebraCategoricalHomEquiv k
    homEquiv_naturality_left_symm := by
      intro V' V A f g
      apply AlgCat.hom_ext
      change TensorAlgebra.lift (A := A) k (g.hom.comp f.hom) =
        (TensorAlgebra.lift (A := A) k g.hom).comp
          (TensorAlgebra.lift k ((TensorAlgebra.ι k).comp f.hom))
      apply TensorAlgebra.hom_ext
      ext x
      simp
    homEquiv_naturality_right := by
      intro V A A' f g
      apply ModuleCat.hom_ext
      change (g.hom.comp f.hom).toLinearMap.comp (TensorAlgebra.ι k) =
        g.hom.toLinearMap.comp (f.hom.toLinearMap.comp (TensorAlgebra.ι k))
      rfl
  }

/-- The old pointwise tensor-algebra equivalence is a component of the categorical one. -/
@[simp] theorem tensorAlgebraCategoricalHomEquiv_symm_hom
    (k : Type u) [CommRing k] (V A : Type u) [AddCommGroup V] [Module k V]
    [Ring A] [Algebra k A] (f : V →ₗ[k] A) :
    ((tensorAlgebraCategoricalHomEquiv k (ModuleCat.of k V) (AlgCat.of k A)).symm
      (ModuleCat.ofHom f)).hom = tensor_algebra_adjunction k V A f := rfl

/-- The forgetful functor from commutative `k`-algebras to `k`-modules. -/
def commAlgForgetModuleFunctor (k : Type u) [CommRing k] :
    CommAlgCat.{u} k ⥤ ModuleCat.{u} k :=
  forget₂ (CommAlgCat.{u} k) (AlgCat.{u} k) ⋙
    forget₂ (AlgCat.{u} k) (ModuleCat.{u} k)

/-- The symmetric-algebra functor from modules to commutative algebras. -/
def symmetricAlgebraFunctor (k : Type u) [CommRing k] :
    ModuleCat.{u} k ⥤ CommAlgCat.{u} k where
  obj V := CommAlgCat.of k (SymmetricAlgebra k V)
  map f := CommAlgCat.ofHom <| SymmetricAlgebra.lift <|
    (SymmetricAlgebra.ι k _).comp f.hom
  map_id V := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    ext x
    simp
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    ext x
    simp

/-- The natural Hom equivalence for the symmetric algebra. -/
def symmetricAlgebraCategoricalHomEquiv (k : Type u) [CommRing k]
    (V : ModuleCat.{u} k) (A : CommAlgCat.{u} k) :
    ((symmetricAlgebraFunctor k).obj V ⟶ A) ≃
      (V ⟶ (commAlgForgetModuleFunctor k).obj A) where
  toFun f := ModuleCat.ofHom (f.hom.toLinearMap.comp (SymmetricAlgebra.ι k V))
  invFun g := CommAlgCat.ofHom (SymmetricAlgebra.lift (A := A) g.hom)
  left_inv f := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    simp
    rfl
  right_inv g := by
    apply ModuleCat.hom_ext
    ext x
    change SymmetricAlgebra.lift (A := A) g.hom (SymmetricAlgebra.ι k V x) = g.hom x
    simp
    rfl

/-- The genuine symmetric-algebra/forgetful adjunction of Example 7.6.3(5). -/
def symmetricAlgebraAdjunction (k : Type u) [CommRing k] :
    symmetricAlgebraFunctor k ⊣ commAlgForgetModuleFunctor k :=
  Adjunction.mkOfHomEquiv {
    homEquiv := symmetricAlgebraCategoricalHomEquiv k
    homEquiv_naturality_left_symm := by
      intro V' V A f g
      apply CommAlgCat.hom_ext
      change SymmetricAlgebra.lift (A := A) (g.hom.comp f.hom) =
        (SymmetricAlgebra.lift (A := A) g.hom).comp
          (SymmetricAlgebra.lift ((SymmetricAlgebra.ι k V).comp f.hom))
      apply SymmetricAlgebra.algHom_ext
      ext x
      simp
      rfl
    homEquiv_naturality_right := by
      intro V A A' f g
      apply ModuleCat.hom_ext
      rfl
  }

/-- The old pointwise symmetric-algebra equivalence is a component of the categorical one. -/
@[simp] theorem symmetricAlgebraCategoricalHomEquiv_symm_hom
    (k : Type u) [CommRing k] (V A : Type u) [AddCommGroup V] [Module k V]
    [CommRing A] [Algebra k A] (f : V →ₗ[k] A) :
    ((symmetricAlgebraCategoricalHomEquiv k (ModuleCat.of k V) (CommAlgCat.of k A)).symm
      (ModuleCat.ofHom f)).hom = symmetric_algebra_adjunction k V A f := rfl

end Etingof

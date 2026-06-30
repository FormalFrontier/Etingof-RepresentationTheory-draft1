import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.FdRep
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

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
* (3) The UEA universal property is captured by `UniversalEnvelopingAlgebra.lift`.
* (4) The group algebra universal property is `MonoidAlgebra.lift`.
* (5) The tensor and symmetric algebra universal properties are `TensorAlgebra.lift`
  and `SymmetricAlgebra.lift`.
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

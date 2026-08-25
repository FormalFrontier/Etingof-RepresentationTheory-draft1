import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.DirectSum.Finsupp
import EtingofRepresentationTheory.Chapter8.Problem8_2_7

/-!
# Categorical direct-sum decomposition of finitely generated modules over a PID

`Problem8_2_7.lean` computes `Tor` and `Ext` for the two building blocks of the structure
theorem over a PID: a **free** generator `A` and a pair of **cyclic** modules `A ⧸ (f)`.
Assembling those building blocks into the computation for arbitrary finitely generated modules
needs the structure theorem in *categorical* form: the decomposition of a finitely generated
module `M` over a PID has to be available as a biproduct decomposition of the corresponding
object of `ModuleCat A` (for `Ext`, and for the second argument of `Tor`) and of
`ModuleCat Aᵐᵒᵖ` (for the first argument of `Tor`, whose right-module argument lives there).

Mathlib's structure theorem `Module.equiv_free_prod_directSum` is stated for plain modules, as an
isomorphism `M ≃ₗ[A] (Fin n →₀ A) × ⨁ i, A ⧸ A ∙ (p i ^ e i)`. This file repackages it:

* `Etingof.PIDDecomposition A M` bundles the data of such a decomposition — a free rank, a finite
  index type for the cyclic summands, their generators, and a plain `A`-linear isomorphism onto
  the *product* form `(Fin n → A) × ((i : ι) → A ⧸ (dᵢ))`.
* `Etingof.exists_pidDecomposition`: every finitely generated module over a PID has one.
* `PIDDecomposition.summand` is the single family of summands indexed by `Fin n ⊕ ι` (the free
  summands `A` followed by the cyclic ones), as objects of `ModuleCat A`;
  `PIDDecomposition.equivDirectSum` and `PIDDecomposition.biproductIso` give the decomposition as
  a `DirectSum` isomorphism and as an isomorphism onto the categorical biproduct.
* `PIDDecomposition.mopSummand` and `PIDDecomposition.mopBiproductIso` are the same statements in
  `ModuleCat Aᵐᵒᵖ`, obtained by transporting along restriction of scalars for the ring
  isomorphism `Aᵐᵒᵖ ≃+* A` (available because `A` is commutative). This is the `local instance`
  idiom of `Problem8_2_7.lean` in functorial form: `Etingof.mopOf A M` is `M` with the right
  `A`-action `op a • x = a • x`.
* Bridge isomorphisms identifying the summands with the shapes used by `Problem8_2_7.lean`:
  `Etingof.intCyclicIso` for `ℤ ⧸ (a) ≅ ZMod a` (and `Etingof.mopIntCyclicIso` for its right-module
  form), while over `k[X]` the cyclic summand `k[X] ⧸ Ideal.span {f}` is *literally* the module
  `PolyGcd` uses, so `Etingof.mopPolyCyclicIso` only has to match up the right-module structures.

Everything except the bridges is proved for an arbitrary PID `A`; the `ℤ` and `k[X]` cases of
Problem 8.2.7 are instances.

## Worked examples

`Etingof.exampleIntProdZMod4` decomposes `ℤ × ZMod 4` as one free summand plus one cyclic summand
`ℤ ⧸ (4)`, and `Etingof.exampleZModSix` decomposes `ZMod 6` as a single cyclic summand `ℤ ⧸ (6)`;
the `example`s next to them check that the derived `DirectSum`, biproduct and right-module
biproduct forms, and the `ZMod` bridge, are usable in practice.
-/

namespace Etingof

open CategoryTheory Limits

universe u

/-! ### Right modules over a commutative ring

For a commutative ring `A` the ring isomorphism `Aᵐᵒᵖ ≃+* A` turns any `A`-module into a right
`A`-module, i.e. an `Aᵐᵒᵖ`-module. `Problem8_2_7.lean` does this by hand with `local instance`s
(`mopZMod`, `mopPolyQuot`); here we package the same construction functorially so that it can be
applied to a whole biproduct decomposition at once. -/

/-- The ring isomorphism `Aᵐᵒᵖ ≃+* A` for a commutative ring `A`. -/
def mopRingEquiv (A : Type u) [CommRing A] : Aᵐᵒᵖ ≃+* A where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := mul_comm _ _
  map_add' _ _ := rfl

@[simp] lemma mopRingEquiv_apply (A : Type u) [CommRing A] (x : Aᵐᵒᵖ) :
    mopRingEquiv A x = MulOpposite.unop x := rfl

lemma mopRingEquiv_toRingHom (A : Type u) [CommRing A] :
    (mopRingEquiv A).toRingHom = (RingHom.id A).fromOpposite fun x y => mul_comm x y := rfl

/-- Restriction of scalars along `Aᵐᵒᵖ ≃+* A`: it sends an `A`-module to the same abelian group
with the right `A`-action `op a • x = a • x`. This is the functorial form of the `local instance`s
`Etingof.mopZMod` and `Etingof.mopPolyQuot` of `Problem8_2_7.lean`. -/
noncomputable def mopFunctor (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.restrictScalars (mopRingEquiv A).toRingHom

/-- An `A`-module `M` viewed as a right `A`-module, i.e. as an object of `ModuleCat Aᵐᵒᵖ`. -/
noncomputable def mopOf (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M] :
    ModuleCat.{u} Aᵐᵒᵖ :=
  (mopFunctor A).obj (ModuleCat.of A M)

/-- The right-module structure carried by `mopOf A M` is the one `Problem8_2_7.lean` builds by
hand, `Module.compHom` along `(RingHom.id A).fromOpposite` — the `local instance`s
`Etingof.mopZMod` and `Etingof.mopPolyQuot`. So the objects are equal, not merely isomorphic, and
the bridges below can be stated with the ad-hoc instances of `Problem8_2_7.lean` in scope. -/
lemma mopOf_eq_of_compHom (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M] :
    letI : Module Aᵐᵒᵖ M := Module.compHom M ((RingHom.id A).fromOpposite fun x y => mul_comm x y)
    mopOf A M = ModuleCat.of Aᵐᵒᵖ M := rfl

instance (A : Type u) [CommRing A] : (mopFunctor A).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars _).Additive

instance (A : Type u) [CommRing A] : (mopFunctor A).IsEquivalence :=
  inferInstanceAs (ModuleCat.restrictScalars (mopRingEquiv A).toRingHom).IsEquivalence

instance (A : Type u) [CommRing A] {J : Type u} [Finite J] (f : J → ModuleCat.{u} A) :
    PreservesBiproduct f (mopFunctor A) :=
  preservesBiproduct_of_preservesProduct _

/-! ### Packaging the structure theorem -/

/-- A decomposition of a module `M` over a commutative ring `A` into a finite free part of rank
`freeRank` together with finitely many cyclic modules `A ⧸ (gen i)`. Over a PID every finitely
generated module has one (`Etingof.exists_pidDecomposition`), by the structure theorem. -/
structure PIDDecomposition (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M]
    [Module A M] where
  /-- The rank of the free part. -/
  freeRank : ℕ
  /-- The index type of the cyclic torsion summands. -/
  torsionIndex : Type u
  /-- The index type of the cyclic summands is finite. -/
  torsionFintype : Fintype torsionIndex
  /-- The index type of the cyclic summands has decidable equality (used to form direct sums). -/
  torsionDecEq : DecidableEq torsionIndex
  /-- The generator of the annihilator of the `i`-th cyclic summand. -/
  gen : torsionIndex → A
  /-- The decomposition itself, as a plain `A`-linear isomorphism onto the product of the free
  part and the cyclic parts. -/
  equivProd :
    M ≃ₗ[A] ((Fin freeRank → A) × ((i : torsionIndex) → A ⧸ Ideal.span {gen i}))

namespace PIDDecomposition

attribute [instance] torsionFintype torsionDecEq

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

/-- The index type of the summands of a decomposition: `freeRank` free summands followed by the
cyclic summands. -/
protected abbrev index (D : PIDDecomposition A M) : Type u := Fin D.freeRank ⊕ D.torsionIndex

/-- The family of summands of a decomposition, as objects of `ModuleCat A`: the free summands
`A` in the `Sum.inl` positions, the cyclic summands `A ⧸ (gen i)` in the `Sum.inr` positions. -/
def summand (D : PIDDecomposition A M) : D.index → ModuleCat.{u} A :=
  Sum.elim (fun _ => ModuleCat.of A A) fun i => ModuleCat.of A (A ⧸ Ideal.span {D.gen i})

@[simp] lemma summand_inl (D : PIDDecomposition A M) (i : Fin D.freeRank) :
    D.summand (Sum.inl i) = ModuleCat.of A A := rfl

@[simp] lemma summand_inr (D : PIDDecomposition A M) (i : D.torsionIndex) :
    D.summand (Sum.inr i) = ModuleCat.of A (A ⧸ Ideal.span {D.gen i}) := rfl

open DirectSum in
/-- The decomposition as an isomorphism onto the direct sum of the summands. -/
noncomputable def equivDirectSum (D : PIDDecomposition A M) :
    M ≃ₗ[A] ⨁ j, (D.summand j : Type u) :=
  D.equivProd ≪≫ₗ
    (LinearEquiv.sumPiEquivProdPi A (Fin D.freeRank) D.torsionIndex
      (fun j => (D.summand j : Type u))).symm ≪≫ₗ
    (DirectSum.linearEquivFunOnFintype A D.index (fun j => (D.summand j : Type u))).symm

/-- The decomposition as an isomorphism onto the categorical biproduct in `ModuleCat A`. -/
noncomputable def biproductIso (D : PIDDecomposition A M) :
    ModuleCat.of A M ≅ biproduct D.summand :=
  D.equivDirectSum.toModuleIso ≪≫ (ModuleCat.coprodIsoDirectSum D.summand).symm ≪≫
    (biproduct.isoCoproduct D.summand).symm

/-! ### The right-module (`ModuleCat Aᵐᵒᵖ`) form -/

/-- The family of summands of a decomposition, as objects of `ModuleCat Aᵐᵒᵖ`: the right regular
module `A` in the `Sum.inl` positions, the cyclic right modules `A ⧸ (gen i)` in the `Sum.inr`
positions. -/
noncomputable def mopSummand (D : PIDDecomposition A M) : D.index → ModuleCat.{u} Aᵐᵒᵖ :=
  (mopFunctor A).obj ∘ D.summand

@[simp] lemma mopSummand_inl (D : PIDDecomposition A M) (i : Fin D.freeRank) :
    D.mopSummand (Sum.inl i) = mopOf A A := rfl

@[simp] lemma mopSummand_inr (D : PIDDecomposition A M) (i : D.torsionIndex) :
    D.mopSummand (Sum.inr i) = mopOf A (A ⧸ Ideal.span {D.gen i}) := rfl

/-- The decomposition of `M` as a right `A`-module, as an isomorphism onto the categorical
biproduct in `ModuleCat Aᵐᵒᵖ`. -/
noncomputable def mopBiproductIso (D : PIDDecomposition A M) :
    mopOf A M ≅ biproduct D.mopSummand :=
  (mopFunctor A).mapIso D.biproductIso ≪≫ (mopFunctor A).mapBiproduct D.summand

/-! ### Existence -/

end PIDDecomposition

/-- **Structure theorem, packaged.** Every finitely generated module over a PID admits a
decomposition into a free part and finitely many cyclic parts. This is
`Module.equiv_free_prod_directSum` with the free part and the torsion part turned into plain
`Pi` types. -/
theorem exists_pidDecomposition (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Nonempty (PIDDecomposition A M) := by
  classical
  obtain ⟨n, ι, hι, p, -, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum A M
  refine ⟨{ freeRank := n
            torsionIndex := ι
            torsionFintype := hι
            torsionDecEq := Classical.decEq ι
            gen := fun i => p i ^ e i
            equivProd := f ≪≫ₗ ?_ }⟩
  exact LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite A A (Fin n))
    (DirectSum.linearEquivFunOnFintype A ι fun i => A ⧸ Ideal.span {p i ^ e i})

/-- **Problem 8.2.7(i)**: every finitely generated abelian group decomposes into a free part and
cyclic parts `ℤ ⧸ (d)`. -/
theorem exists_pidDecomposition_int (M : Type) [AddCommGroup M] [Module.Finite ℤ M] :
    Nonempty (PIDDecomposition ℤ M) :=
  exists_pidDecomposition ℤ M

open Polynomial in
/-- **Problem 8.2.7(ii)**: every finitely generated `k[X]`-module decomposes into a free part and
cyclic parts `k[X] ⧸ (f)`. -/
theorem exists_pidDecomposition_polynomial {k : Type u} [Field k] (M : Type u) [AddCommGroup M]
    [Module k[X] M] [Module.Finite k[X] M] : Nonempty (PIDDecomposition k[X] M) :=
  exists_pidDecomposition k[X] M

/-! ### Bridges to the cyclic modules of `Problem8_2_7.lean`

The right-module statements of `Problem8_2_7.lean` are phrased with its own `local instance`s
`Etingof.mopZMod` and `Etingof.mopPolyQuot`; we put those back in scope so that the bridges below
land on exactly the objects those theorems talk about. By `Etingof.mopOf_eq_of_compHom` this is the
same right-module structure as the one `mopOf` produces. -/

attribute [local instance] mopZMod mopPolyQuot

/-- The cyclic `ℤ`-module `ℤ ⧸ (a)` is `ZMod a` (for `a : ℕ`), the shape used by the `ZModGcd`
building blocks of `Problem8_2_7.lean`. -/
noncomputable def intCyclicEquiv (a : ℕ) : (ℤ ⧸ Ideal.span {(a : ℤ)}) ≃ₗ[ℤ] ZMod a :=
  (Int.quotientSpanNatEquivZMod a).toAddEquiv.toIntLinearEquiv

/-- Bridge: the cyclic summand `ℤ ⧸ (a)` of a decomposition is isomorphic, in `ModuleCat ℤ`, to
the module `ZMod a` used by `Problem_8_2_7_i_ext_*`. -/
noncomputable def intCyclicIso (a : ℕ) :
    ModuleCat.of ℤ (ℤ ⧸ Ideal.span {(a : ℤ)}) ≅ ModuleCat.of ℤ (ZMod a) :=
  (intCyclicEquiv a).toModuleIso

/-- Bridge: the right-module cyclic summand `ℤ ⧸ (a)` is isomorphic, in `ModuleCat ℤᵐᵒᵖ`, to the
right module `ZMod a` used by `Problem_8_2_7_i_tor_*` (whose right action is the `local instance`
`Etingof.mopZMod`). -/
noncomputable def mopIntCyclicIso (a : ℕ) :
    mopOf ℤ (ℤ ⧸ Ideal.span {(a : ℤ)}) ≅ ModuleCat.of ℤᵐᵒᵖ (ZMod a) :=
  (mopFunctor ℤ).mapIso (intCyclicIso a)

/-- Bridge: the free summand, as a right module, is the right regular module `A` used by
`Problem_8_2_7_i_tor_free_vanish` and `Problem_8_2_7_ii_tor_free_vanish`. -/
noncomputable def mopSelfIso (A : Type u) [CommRing A] : mopOf A A ≅ ModuleCat.of Aᵐᵒᵖ A where
  hom := ConcreteCategory.ofHom (C := ModuleCat Aᵐᵒᵖ)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' c x := mul_comm (MulOpposite.unop c) x }
  inv := ConcreteCategory.ofHom (C := ModuleCat Aᵐᵒᵖ)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' c x := mul_comm x (MulOpposite.unop c) }
  hom_inv_id := rfl
  inv_hom_id := rfl

open Polynomial in
/-- Bridge: over `k[X]` the cyclic summand `k[X] ⧸ (f)` is literally the module used by the
`PolyGcd` building blocks of `Problem8_2_7.lean`; only the right-module structures have to be
matched up. -/
noncomputable def mopPolyCyclicIso {k : Type u} [Field k] (f : k[X]) :
    mopOf k[X] (k[X] ⧸ Ideal.span {f}) ≅ ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {f}) :=
  Iso.refl _

/-! ### Worked examples -/

/-- Worked example: `ℤ × ZMod 4` decomposes as one free summand `ℤ` plus one cyclic summand
`ℤ ⧸ (4)`. -/
noncomputable def exampleIntProdZMod4 : PIDDecomposition ℤ (ℤ × ZMod 4) where
  freeRank := 1
  torsionIndex := Fin 1
  torsionFintype := inferInstance
  torsionDecEq := inferInstance
  gen _ := ((4 : ℕ) : ℤ)
  equivProd :=
    LinearEquiv.prodCongr (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
      ((intCyclicEquiv 4).symm ≪≫ₗ
        (LinearEquiv.piUnique ℤ fun _ : Fin 1 => ℤ ⧸ Ideal.span {((4 : ℕ) : ℤ)}).symm)

/-- Worked example: `ZMod 6` decomposes as the single cyclic summand `ℤ ⧸ (6)`, with no free
part. -/
noncomputable def exampleZModSix : PIDDecomposition ℤ (ZMod 6) where
  freeRank := 0
  torsionIndex := Fin 1
  torsionFintype := inferInstance
  torsionDecEq := inferInstance
  gen _ := ((6 : ℕ) : ℤ)
  equivProd :=
    (intCyclicEquiv 6).symm ≪≫ₗ
      (LinearEquiv.piUnique ℤ fun _ : Fin 1 => ℤ ⧸ Ideal.span {((6 : ℕ) : ℤ)}).symm ≪≫ₗ
      (LinearEquiv.uniqueProd (R := ℤ) (M₂ := Fin 0 → ℤ)).symm

noncomputable section Examples

-- The two summands of the first example are the free module `ℤ` and the cyclic module `ℤ ⧸ (4)`.
example : exampleIntProdZMod4.summand (Sum.inl (0 : Fin 1)) = ModuleCat.of ℤ ℤ := rfl

example : exampleIntProdZMod4.summand (Sum.inr (0 : Fin 1))
    = ModuleCat.of ℤ (ℤ ⧸ Ideal.span {((4 : ℕ) : ℤ)}) := rfl

-- The derived forms are available: a biproduct isomorphism in `ModuleCat ℤ` (the shape `Ext`
-- consumes) and one in `ModuleCat ℤᵐᵒᵖ` (the shape the first argument of `Tor` consumes).
example : ModuleCat.of ℤ (ℤ × ZMod 4) ≅ biproduct exampleIntProdZMod4.summand :=
  exampleIntProdZMod4.biproductIso

example : mopOf ℤ (ℤ × ZMod 4) ≅ biproduct exampleIntProdZMod4.mopSummand :=
  exampleIntProdZMod4.mopBiproductIso

-- The bridges turn the cyclic summand into the `ZMod`-shaped module the `Problem8_2_7` building
-- blocks are stated for, and the free summand into the right regular module.
example : exampleIntProdZMod4.summand (Sum.inr (0 : Fin 1)) ≅ ModuleCat.of ℤ (ZMod 4) :=
  intCyclicIso 4

example : exampleIntProdZMod4.mopSummand (Sum.inr (0 : Fin 1)) ≅ ModuleCat.of ℤᵐᵒᵖ (ZMod 4) :=
  mopIntCyclicIso 4

example : exampleIntProdZMod4.mopSummand (Sum.inl (0 : Fin 1)) ≅ ModuleCat.of ℤᵐᵒᵖ ℤ :=
  mopSelfIso ℤ

-- `ZMod 6` decomposes with no free summands at all.
example : exampleZModSix.index ≃ Fin 1 := Equiv.emptySum (Fin 0) (Fin 1)

end Examples

end Etingof

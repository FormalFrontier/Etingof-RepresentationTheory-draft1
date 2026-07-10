import Mathlib
import EtingofRepresentationTheory.Chapter7.Introduction_7_4

/-!
# Exercise 4.2.3: fewer irreducibles than conjugacy classes in the modular case

**Exercise 4.2.3.** Show that if `|G| = 0` in `k`, then the number of isomorphism
classes of irreducible representations of `G` over `k` is strictly less than the
number of conjugacy classes in `G`.

*Hint.* Let `P = ∑_{g ∈ G} g ∈ k[G]`. Then `P² = 0`. So `P` has zero trace in every
finite-dimensional representation of `G` over `k`.

## Formalization

The number of conjugacy classes of `G` is `Nat.card (ConjClasses G)`.

The "number of isomorphism classes of irreducible representations of `G` over `k`" is
`Nat.card (IrrepClasses k G)`, where `IrrepClasses k G` is the type of isomorphism
classes of objects of the full subcategory of `FDRep k G` spanned by the simple
(irreducible) representations. This is the genuine set of irreducibles up to
isomorphism, obtained via the isomorphism-class setoid on a category
(`CategoryTheory.isIsomorphicSetoid`).

The hypothesis "`|G| = 0` in `k`" is `(Fintype.card G : k) = 0`, i.e. the characteristic
of `k` divides `|G|`.

This is a statement-pass formalization: the statement is fixed faithfully and the proof
is deferred (`sorry`). The mathematical content is that in the modular case the element
`P = ∑_g g` is nonzero, central, nilpotent (`P² = |G| · P = 0`), and hence lies in the
Jacobson radical of `k[G]`; the group algebra is therefore not semisimple, so the number
of simple modules is strictly smaller than the dimension of its centre, which equals the
number of conjugacy classes.
-/

open CategoryTheory

namespace Etingof

/-- The type of isomorphism classes of irreducible (simple) representations of `G` over
`k`: isomorphism classes of objects in the full subcategory of `FDRep k G` on the simple
objects. -/
def IrrepClasses (k G : Type*) [Field k] [Monoid G] : Type _ :=
  Quotient (isIsomorphicSetoid
    (ObjectProperty.FullSubcategory (fun V : FDRep k G => Simple V)))

/-! ### The group sum `P = ∑_g g` and non-semisimplicity in the modular case

In the modular case (`|G| = 0` in `k`) the element `P = ∑_{g ∈ G} g` of the group
algebra `k[G]` is a nonzero, central, nilpotent element: `P² = |G| · P = 0`. Its
existence shows that `k[G]` is **not** semisimple — a nonzero central nilpotent lies in
the Jacobson radical, which vanishes for a semisimple ring. This is the algebraic core of
Exercise 4.2.3; the counting comparison
`Nat.card (IrrepClasses k G) < Nat.card (ConjClasses G)` builds on top of it. -/

section GroupSum

variable (k G : Type*) [Field k] [Group G] [Fintype G]

/-- The sum `P = ∑_{g ∈ G} g` of all group elements, viewed in the group algebra `k[G]`. -/
noncomputable def groupSum : MonoidAlgebra k G := ∑ g : G, MonoidAlgebra.single g (1 : k)

variable {k G}

omit [Group G] in
/-- Every coefficient of `P = ∑_g g` equals `1`. -/
@[simp] lemma groupSum_apply (x : G) : (groupSum k G) x = 1 := by
  classical
  rw [groupSum, Finset.sum_apply',
    Finset.sum_eq_single x (fun b _ hb => by simp [hb])
      (fun hx => absurd (Finset.mem_univ x) hx)]
  simp

/-- Left-multiplying `P` by a group element fixes it: `g · P = P`. -/
lemma single_mul_groupSum (g : G) :
    MonoidAlgebra.single g (1 : k) * groupSum k G = groupSum k G := by
  simp only [groupSum, Finset.mul_sum, MonoidAlgebra.single_mul_single, one_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

/-- Right-multiplying `P` by a group element fixes it: `P · g = P`. -/
lemma groupSum_mul_single (g : G) :
    groupSum k G * MonoidAlgebra.single g (1 : k) = groupSum k G := by
  simp only [groupSum, Finset.sum_mul, MonoidAlgebra.single_mul_single, mul_one]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

/-- `P = ∑_g g` is central in `k[G]`. -/
lemma groupSum_mem_center :
    groupSum k G ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | hM g =>
    rw [show (MonoidAlgebra.of k G g : MonoidAlgebra k G) = MonoidAlgebra.single g 1 from rfl,
      single_mul_groupSum, groupSum_mul_single]
  | hadd x y hx hy => rw [add_mul, mul_add, hx, hy]
  | hsmul r x hx => rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, hx]

/-- In the modular case `|G| = 0` the group sum squares to zero: `P² = |G| · P = 0`. -/
lemma groupSum_mul_self (hcard : (Fintype.card G : k) = 0) :
    groupSum k G * groupSum k G = 0 := by
  have hdef : groupSum k G = ∑ g : G, MonoidAlgebra.single g (1 : k) := rfl
  calc groupSum k G * groupSum k G
      = ∑ g : G, MonoidAlgebra.single g (1 : k) * groupSum k G := by rw [← Finset.sum_mul, ← hdef]
    _ = ∑ _g : G, groupSum k G := by simp only [single_mul_groupSum]
    _ = 0 := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, hcard, zero_smul]

/-- In the modular case the group sum is nilpotent. -/
lemma groupSum_isNilpotent (hcard : (Fintype.card G : k) = 0) :
    IsNilpotent (groupSum k G) :=
  ⟨2, by rw [pow_two]; exact groupSum_mul_self hcard⟩

/-- The group sum is nonzero (its coefficient at `1` is `1 ≠ 0`). -/
lemma groupSum_ne_zero : groupSum k G ≠ 0 := by
  intro h
  have h1 := groupSum_apply (k := k) (G := G) (1 : G)
  rw [h] at h1
  simp at h1

/-- **Non-semisimplicity in the modular case.** If `|G| = 0` in `k` then the group algebra
`k[G]` is not semisimple: the nonzero central nilpotent `P = ∑_g g` lies in the Jacobson
radical, which vanishes for a semisimple ring. -/
theorem not_isSemisimpleRing_of_card_eq_zero (hcard : (Fintype.card G : k) = 0) :
    ¬ IsSemisimpleRing (MonoidAlgebra k G) := by
  intro hss
  haveI := hss
  refine groupSum_ne_zero (k := k) (G := G) ?_
  have hmem : groupSum k G ∈ Ideal.jacobson (⊥ : Ideal (MonoidAlgebra k G)) := by
    rw [Ideal.mem_jacobson_iff]
    intro y
    -- `y · P` is nilpotent (`P` is central and squares to zero), so `1 + y·P` is a unit.
    have hcomm : Commute y (groupSum k G) := Subalgebra.mem_center_iff.mp groupSum_mem_center y
    have hnil : IsNilpotent (y * groupSum k G) :=
      hcomm.isNilpotent_mul_left (groupSum_isNilpotent hcard)
    obtain ⟨u, hu⟩ := hnil.isUnit_one_add
    refine ⟨↑u⁻¹, ?_⟩
    have key : (↑u⁻¹ : MonoidAlgebra k G) * (y * groupSum k G) + ↑u⁻¹ = 1 := by
      have h := u.inv_mul
      rw [hu, mul_add, mul_one, add_comm] at h
      exact h
    rw [Ideal.mem_bot, mul_assoc, key, sub_self]
  have hjb : Ideal.jacobson (⊥ : Ideal (MonoidAlgebra k G))
      = Ring.jacobson (MonoidAlgebra k G) := Ideal.jacobson_bot
  have hmem' : groupSum k G ∈ Ring.jacobson (MonoidAlgebra k G) := hjb ▸ hmem
  rw [IsSemisimpleRing.jacobson_eq_bot, Ideal.mem_bot] at hmem'
  exact hmem'

end GroupSum

/-! ### Field-general bridge between simple `FDRep`s and simple `k[G]`-modules

The counting half of Exercise 4.2.3 requires relating the categorical count
`Nat.card (IrrepClasses k G)` to an algebraic count of simple `k[G]`-modules. The bridge must
be **field-general** — no `IsAlgClosed`, no `NeZero (|G| : k)` — because the exercise lives in
the modular (non-semisimple) case. This section develops:

* `simple_fdRepOf_of_isSimpleModule`: a simple `k[G]`-module gives a simple `FDRep k G` object
  (a field-general restatement of `FDRep.simple_of_isSimpleModule_asModule`, which carries a
  spurious `[NeZero (Nat.card G : k)]` inherited from its `IsAlgClosed` section);
* `Simple` viewed as an `ObjectProperty` closed under isomorphism;
* `repSimpleClassesEquivModuleSimpleClasses`: the bijection between isomorphism classes of
  simple objects of `Rep k G` and of `ModuleCat k[G]`, induced by
  `Rep.equivalenceModuleMonoidAlgebra` via `Etingof.isoClassesEquivOfEquivalence`.

The remaining links (`IrrepClasses k G ≃` simple-object classes of `Rep k G`, the
`Finite` instance, and the final count) are tracked in the sibling issues. -/

section Bridge

open CategoryTheory ObjectProperty

universe u v

/-- A fully faithful functor preserving monomorphisms reflects simple objects. This is a
field-general (and namespace-local) copy of the private lemma used in
`Infrastructure/IrreducibleEnumeration`, restated here without any `IsAlgClosed` context. -/
private lemma simple_of_fullyFaithful_preservesMono {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro _
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- **Field-general bridge (module ⟹ representation).** If `ρ.asModule` is a simple
`k[G]`-module, then `FDRep.of ρ` is a simple object of `FDRep k G`. No `NeZero (Nat.card G : k)`
or `IsAlgClosed k` hypothesis is required: the proof only uses the equivalence
`Rep k G ≌ ModuleCat k[G]` and the fully faithful forgetful functor `FDRep k G ⥤ Rep k G`. -/
theorem simple_fdRepOf_of_isSimpleModule
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V)
    [hρ : @IsSimpleModule (MonoidAlgebra k G) _ ρ.asModule _
      (Representation.instModuleMonoidAlgebraAsModule ρ)] :
    Simple (FDRep.of ρ) := by
  letI : Module (MonoidAlgebra k G) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  haveI := hρ
  let E := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  haveI : Simple (E.functor.obj ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ))) :=
    @simple_of_isSimpleModule (MonoidAlgebra k G) ρ.asModule _ _
      (Representation.instModuleMonoidAlgebraAsModule ρ) hρ
  haveI : Simple ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ)) :=
    simple_of_fullyFaithful_preservesMono E.functor _
  exact simple_of_fullyFaithful_preservesMono (forget₂ (FDRep k G) (Rep k G)) _

/-- Being a simple object, packaged as an `ObjectProperty`. -/
def simpleProp (C : Type*) [Category C] [Limits.HasZeroMorphisms C] : ObjectProperty C :=
  fun X => Simple X

instance (C : Type*) [Category C] [Limits.HasZeroMorphisms C] :
    (simpleProp C).IsClosedUnderIsomorphisms where
  of_iso e hX := (Simple.iff_of_iso e).mp hX

/-- An equivalence of categories preserves and reflects simple objects. -/
lemma simpleProp_iff_of_equivalence {A B : Type*} [Category A] [Category B]
    [Limits.HasZeroMorphisms A] [Limits.HasZeroMorphisms B]
    (E : A ≌ B) [E.functor.PreservesMonomorphisms] [E.inverse.PreservesMonomorphisms]
    (X : A) : Simple (E.functor.obj X) ↔ Simple X := by
  constructor
  · intro _
    exact simple_of_fullyFaithful_preservesMono E.functor X
  · intro hX
    haveI := hX
    haveI : Simple (E.inverse.obj (E.functor.obj X)) :=
      Simple.of_iso (Y := X) (E.unitIso.symm.app X)
    exact simple_of_fullyFaithful_preservesMono E.inverse (E.functor.obj X)

variable (k G) in
/-- **Counting bridge (representation side).** The isomorphism classes of simple objects of
`Rep k G` are in bijection with those of `ModuleCat k[G]`, induced by the equivalence
`Rep.equivalenceModuleMonoidAlgebra` through `Etingof.isoClassesEquivOfEquivalence`. -/
noncomputable def repSimpleClassesEquivModuleSimpleClasses :
    Quotient (isIsomorphicSetoid (simpleProp (Rep k G)).FullSubcategory) ≃
      Quotient (isIsomorphicSetoid
        (simpleProp (ModuleCat (MonoidAlgebra k G))).FullSubcategory) := by
  refine isoClassesEquivOfEquivalence
    (Equivalence.congrFullSubcategory (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G))
      (P := simpleProp (Rep k G)) (Q := simpleProp (ModuleCat (MonoidAlgebra k G))) ?_)
  exact funext fun X => propext
    (simpleProp_iff_of_equivalence (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)) X)

end Bridge

/-- **Exercise 4.2.3.** If `|G| = 0` in `k` (the characteristic of `k` divides the order
of the finite group `G`), then the number of isomorphism classes of irreducible
representations of `G` over `k` is strictly less than the number of conjugacy classes of
`G`. -/
theorem Exercise4_2_3 (k G : Type*) [Field k] [Group G] [Fintype G]
    (h : (Fintype.card G : k) = 0) :
    Nat.card (IrrepClasses k G) < Nat.card (ConjClasses G) := by
  -- The algebraic core is `not_isSemisimpleRing_of_card_eq_zero h`: `k[G]` is not
  -- semisimple because `groupSum k G = ∑_g g` is a nonzero central nilpotent.
  -- Remaining (the counting comparison): relate `Nat.card (IrrepClasses k G)` to the
  -- dimension of the centre of the semisimple quotient `k[G] / rad`, and
  -- `Nat.card (ConjClasses G)` to `dim_k Z(k[G])` (class sums are a basis of the centre,
  -- cf. `finrank_center_monoidAlgebra` in `Chapter4/Corollary4_2_2.lean`), then use the
  -- strict drop coming from `0 ≠ groupSum ∈ rad`. This modular counting half is deferred.
  sorry

end Etingof

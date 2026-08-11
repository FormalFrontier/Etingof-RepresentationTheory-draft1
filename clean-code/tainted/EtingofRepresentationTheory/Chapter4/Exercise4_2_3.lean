import Mathlib
import EtingofRepresentationTheory.Chapter7.Introduction_7_4
import EtingofRepresentationTheory.Infrastructure.IrrepClasses

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
(irreducible) representations. This is the set of irreducibles up to
isomorphism, obtained via the isomorphism-class setoid on a category
(`CategoryTheory.isIsomorphicSetoid`).

The hypothesis "`|G| = 0` in `k`" is `(Fintype.card G : k) = 0`, i.e. the characteristic
of `k` divides `|G|`.

This file is the infrastructure layer for Exercise 4.2.3. The
mathematical content is that in the modular case the element `P = ∑_g g` is nonzero,
central, nilpotent (`P² = |G| · P = 0`), and hence lies in the Jacobson radical of `k[G]`;
the group algebra is therefore not semisimple. This file proves that non-semisimplicity
(`not_isSemisimpleRing_of_card_eq_zero`), the count identification
`card_irrepClasses_eq_card_simpleModuleClasses` (`IrrepClasses k G ≃ SimpleModuleClasses (k[G])`),
and finiteness of the irreducibles (`finite_simpleModuleClasses`, `IrrepClasses.instFinite`).

This file does not state the main comparison itself: the strict counting drop
`Nat.card (IrrepClasses k G) < Nat.card (ConjClasses G)` (`Etingof.Exercise4_2_3`) is
proved downstream in `Exercise4_2_3_Assembly.lean`, because the
split-field and strict-bound machinery it depends on import this file (see the tail comment
below).
-/

open CategoryTheory

namespace Etingof

/-! `IrrepClasses k G`, the type of isomorphism classes of irreducible (simple)
representations of `G` over `k`, is defined in
`EtingofRepresentationTheory.Infrastructure.IrrepClasses`. It was originally introduced here,
but it is the correct index type for any statement about the irreducibles of `G` up to
isomorphism (notably Definition 5.7.1), so it lives in a file that imports nothing but
Mathlib. Its quotient API (`IrrepClasses.mk`, `mk_eq_mk_iff`, `lift`, `repOf`, `character`)
is available from that file. -/

/-! ### The group sum `P = ∑_g g` and non-semisimplicity in the modular case

In the modular case (`|G| = 0` in `k`) the element `P = ∑_{g ∈ G} g` of the group
algebra `k[G]` is a nonzero, central, nilpotent element: `P² = |G| · P = 0`. Its
existence shows that `k[G]` is not semisimple: a nonzero central nilpotent lies in
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
@[simp] lemma groupSum_apply (x : G) : (groupSum k G).coeff x = 1 := by
  classical
  rw [groupSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single x
    (fun b _ hb => by simp [hb])
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
  rw [h, show (0 : MonoidAlgebra k G).coeff (1 : G) = 0 from rfl] at h1
  exact zero_ne_one h1

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

/-! ### Relating simple `FDRep`s and simple `k[G]`-modules

The counting half of Exercise 4.2.3 requires relating the categorical count
`Nat.card (IrrepClasses k G)` to an algebraic count of simple `k[G]`-modules. This must hold
over an arbitrary field (no `IsAlgClosed`, no `NeZero (|G| : k)`), because the exercise lives in
the modular (non-semisimple) case. This section develops:

* `simple_fdRepOf_of_isSimpleModule`: a simple `k[G]`-module gives a simple `FDRep k G` object
  (a field-general restatement of `FDRep.simple_of_isSimpleModule_asModule`, which carries a
  spurious `[NeZero (Nat.card G : k)]` inherited from its `IsAlgClosed` section);
* `Simple` viewed as an `ObjectProperty` closed under isomorphism;
* `repSimpleClassesEquivModuleSimpleClasses`: the bijection between isomorphism classes of
  simple objects of `Rep k G` and of `ModuleCat k[G]`, induced by
  `Rep.equivalenceModuleMonoidAlgebra` via `Etingof.isoClassesEquivOfEquivalence`.

The remaining links (`IrrepClasses k G ≃` simple-object classes of `Rep k G`, the
`Finite` instance, and the final count) are developed below. -/

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

/-- **Module ⟹ representation.** If `ρ.asModule` is a simple
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

/-- **Simple `k[G]`-modules are finite-dimensional.** Since `k[G]` is a finite-dimensional
`k`-algebra (for finite `G`), any simple `k[G]`-module is a cyclic (hence finitely generated)
`k[G]`-module, and finite over `k` by transitivity. This is the input to essential
surjectivity of `FDRep k G ⥤ Rep k G` on simple objects. -/
theorem finite_k_of_isSimpleModule [Finite G] {M : Type u} [AddCommGroup M]
    [Module k M] [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M]
    [IsSimpleModule (MonoidAlgebra k G) M] : Module.Finite k M := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial (MonoidAlgebra k G) M
  obtain ⟨m, hm0⟩ := exists_ne (0 : M)
  have htop : Submodule.span (MonoidAlgebra k G) {m} = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left (by
      rw [Submodule.span_singleton_eq_bot]; exact hm0)
  haveI : Module.Finite (MonoidAlgebra k G) M := ⟨⟨{m}, by simpa using htop⟩⟩
  haveI : Module.Finite k (MonoidAlgebra k G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G k)
  exact Module.Finite.trans (MonoidAlgebra k G) M

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
/-- **Counting step (representation side).** The isomorphism classes of simple objects of
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

/-! ### `FDRep k G` and `Rep k G` have the same simple objects

The final ingredient for the counting comparison is that the forgetful functor
`FDRep k G ⥤ Rep k G` restricts to an *equivalence* on the full subcategories of simple
objects. Preservation of simplicity is the mathematical content: a simple
finite-dimensional representation, viewed as a `k[G]`-module, is a simple module. We prove
this directly: every `k[G]`-submodule of `V.ρ.asModule` is a subrepresentation, hence
(being finite-dimensional) yields a monomorphism into `V` in `FDRep k G`, which `Simple V`
forces to be `0` (submodule `⊥`) or an isomorphism (submodule `⊤`). Essential surjectivity
uses that a simple `k[G]`-module is finite-dimensional (`finite_k_of_isSimpleModule`), so a
simple `Rep k G` object comes from an `FDRep k G` object. -/

/-- The inclusion of a subrepresentation of `V.ρ` as an intertwining map into `V.ρ`. -/
noncomputable def subInclusion (V : FDRep k G) (S : Subrepresentation V.ρ) :
    S.toRepresentation.IntertwiningMap V.ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ S.toSubmodule.subtype (fun _ _ => rfl)

private lemma nontrivial_carrier_of_simple (V : FDRep k G) [Simple V] : Nontrivial V.V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply id_nonzero V
  apply (forget₂ (FDRep k G) (FGModuleCat k)).map_injective
  apply (forget₂ (FGModuleCat k) (ModuleCat k)).map_injective
  ext x
  exact @Subsingleton.elim V.V h _ _

/-- **Preservation of simplicity (module side).** A simple object `V` of `FDRep k G` has a
simple underlying `k[G]`-module `V.ρ.asModule`. Every `k[G]`-submodule is a
finite-dimensional subrepresentation, hence gives a monomorphism into `V` in `FDRep k G`;
simplicity of `V` forces it to be `⊥` or `⊤`. -/
theorem isSimpleModule_asModule_of_simple (V : FDRep k G) [Simple V] :
    IsSimpleModule (MonoidAlgebra k G) (Representation.asModule V.ρ) := by
  haveI : Nontrivial V.V := nontrivial_carrier_of_simple V
  haveI : Nontrivial (Representation.asModule V.ρ) :=
    (Representation.asModuleEquiv V.ρ).toEquiv.nontrivial
  refine { eq_bot_or_eq_top := fun N => ?_ }
  set S : Subrepresentation V.ρ := Subrepresentation.ofSubmodule' N with hS
  haveI : Module.Finite k S.toSubmodule := inferInstance
  let ι : S.toRepresentation.IntertwiningMap V.ρ := subInclusion V S
  let j : (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of S.toRepresentation) ⟶
      (forget₂ (FDRep k G) (Rep k G)).obj V := Rep.ofHom ι
  have hjhom : ⇑j.hom = (Subtype.val : S.toSubmodule → V.V) := rfl
  have hjinj : Function.Injective ⇑j.hom := by rw [hjhom]; exact Subtype.coe_injective
  haveI hmonoj : Mono j := (Rep.mono_iff_injective j).mpr hjinj
  let j' : FDRep.of S.toRepresentation ⟶ V :=
    (forget₂ (FDRep k G) (Rep k G)).preimage j
  have hmap : (forget₂ (FDRep k G) (Rep k G)).map j' = j :=
    (forget₂ (FDRep k G) (Rep k G)).map_preimage j
  haveI hmonoj' : Mono j' :=
    (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map (by rw [hmap]; exact hmonoj)
  by_cases hz : j' = 0
  · left
    have hj0 : j = 0 := by rw [← hmap, hz]; exact Functor.map_zero _ _ _
    have hzero : ⇑j.hom = 0 := by rw [hj0]; rfl
    rw [eq_bot_iff]
    intro x hx
    have hxS : x ∈ S := (Subrepresentation.mem_ofSubmodule'_iff (ρ := V.ρ)).mpr hx
    have hval : (Subtype.val : S.toSubmodule → V.V) ⟨x, hxS⟩ = 0 := by
      rw [← hjhom]; exact congrFun hzero ⟨x, hxS⟩
    rw [Submodule.mem_bot]
    exact hval
  · right
    haveI : IsIso j' := (Simple.mono_isIso_iff_nonzero j').mpr hz
    haveI hisoj : IsIso ((forget₂ (FDRep k G) (Rep k G)).map j') := inferInstance
    rw [hmap] at hisoj
    have hsurj : Function.Surjective ⇑j.hom := (Rep.epi_iff_surjective j).mp inferInstance
    rw [hjhom] at hsurj
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy⟩ := hsurj x
    have hxS : x ∈ S := hy ▸ y.2
    exact (Subrepresentation.mem_ofSubmodule'_iff (ρ := V.ρ)).mp hxS

/-- **Simple objects of `Rep k G` are exactly the simple `k[G]`-modules.** -/
theorem simple_rep_iff_isSimpleModule (W : Rep k G) :
    Simple W ↔ IsSimpleModule (MonoidAlgebra k G) (Representation.asModule W.ρ) := by
  rw [← simpleProp_iff_of_equivalence (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)) W]
  exact simple_iff_isSimpleModule

/-- **Preservation of simplicity (categorical form).** The forgetful functor
`FDRep k G ⥤ Rep k G` sends simple objects to simple objects. -/
theorem simple_forget₂_of_simple (V : FDRep k G) [Simple V] :
    Simple ((forget₂ (FDRep k G) (Rep k G)).obj V) := by
  rw [simple_rep_iff_isSimpleModule]
  exact isSimpleModule_asModule_of_simple V

/-- The forgetful functor `FDRep k G ⥤ Rep k G`, lifted to the full subcategories of simple
objects. -/
noncomputable abbrev fdRepSimpleToRepSimple :
    (simpleProp (FDRep k G)).FullSubcategory ⥤ (simpleProp (Rep k G)).FullSubcategory :=
  (simpleProp (Rep k G)).lift
    ((simpleProp (FDRep k G)).ι ⋙ forget₂ (FDRep k G) (Rep k G))
    (fun X => by haveI : Simple X.obj := X.property; exact simple_forget₂_of_simple X.obj)

instance [Finite G] : (fdRepSimpleToRepSimple (k := k) (G := G)).EssSurj where
  mem_essImage W := by
    haveI : Simple W.obj := W.property
    haveI hsm : IsSimpleModule (MonoidAlgebra k G) (Representation.asModule W.obj.ρ) :=
      (simple_rep_iff_isSimpleModule W.obj).mp W.property
    haveI : Module.Finite k (Representation.asModule W.obj.ρ) :=
      finite_k_of_isSimpleModule (k := k) (G := G) (M := Representation.asModule W.obj.ρ)
    haveI : Module.Finite k W.obj.V :=
      Module.Finite.equiv (Representation.asModuleEquiv W.obj.ρ)
    haveI : Simple (FDRep.of W.obj.ρ) :=
      simple_fdRepOf_of_isSimpleModule (hρ := hsm) W.obj.ρ
    exact ⟨⟨FDRep.of W.obj.ρ, ‹Simple (FDRep.of W.obj.ρ)›⟩, ⟨Iso.refl _⟩⟩

noncomputable instance [Finite G] :
    (fdRepSimpleToRepSimple (k := k) (G := G)).IsEquivalence where

variable (k G) in
/-- `IrrepClasses k G`, the isomorphism classes of simple objects of `FDRep k G`, is in
bijection with the isomorphism classes of simple objects of `Rep k G`, via the forgetful
functor `FDRep k G ⥤ Rep k G`. -/
noncomputable def irrepClassesEquivRepSimpleClasses [Finite G] :
    IrrepClasses k G ≃
      Quotient (isIsomorphicSetoid (simpleProp (Rep k G)).FullSubcategory) :=
  isoClassesEquivOfEquivalence (fdRepSimpleToRepSimple (k := k) (G := G)).asEquivalence

/-- Isomorphism classes of simple modules over a ring `R`, with underlying modules taken in
universe `w`. -/
abbrev SimpleModuleClasses.{w, r} (R : Type r) [Ring R] :=
  Quotient (isIsomorphicSetoid (simpleProp (ModuleCat.{w} R)).FullSubcategory)

variable (k G) in
/-- Isomorphism classes of irreducible representations of `G` over `k` correspond to
isomorphism classes of simple `k[G]`-modules. The intermediate `Rep k G` classes are
reconstructed inline (rather than reusing `repSimpleClassesEquivModuleSimpleClasses`) so their
carrier universe unifies with the one coming from `FDRep k G`. -/
noncomputable def irrepClassesEquivSimpleModuleClasses [Finite G] :
    IrrepClasses k G ≃ SimpleModuleClasses.{u} (MonoidAlgebra k G) :=
  (irrepClassesEquivRepSimpleClasses k G).trans
    (isoClassesEquivOfEquivalence
      (Equivalence.congrFullSubcategory (Rep.equivalenceModuleMonoidAlgebra.{u} (k := k) (G := G))
        (P := simpleProp (Rep.{u} k G)) (Q := simpleProp (ModuleCat.{u} (MonoidAlgebra k G)))
        (funext fun X => propext (simpleProp_iff_of_equivalence
          (Rep.equivalenceModuleMonoidAlgebra.{u} (k := k) (G := G)) X))))

variable (k G) in
/-- The number of isomorphism classes of irreducible representations of `G` over `k` equals
the number of isomorphism classes of simple `k[G]`-modules. -/
theorem card_irrepClasses_eq_card_simpleModuleClasses [Finite G] :
    Nat.card (IrrepClasses k G) = Nat.card (SimpleModuleClasses.{u} (MonoidAlgebra k G)) :=
  Nat.card_congr (irrepClassesEquivSimpleModuleClasses k G)

end Bridge

/-! ### Finiteness of the set of irreducibles

A finite group `G` has only finitely many irreducible representations over any field `k`.
Via the counting correspondence above this reduces to: a finite-dimensional algebra `R` over a field
`k` has only finitely many isomorphism classes of simple modules. The mathematical content is
that every simple `R`-module is annihilated by the Jacobson radical, hence a module over the
semisimple quotient `A = R ⧸ rad`, and over a semisimple ring every simple module embeds into
the ring as a submodule lying in one of the finitely many isotypic components of `A`. -/

section Finiteness

attribute [local instance] CategoryTheory.isIsomorphicSetoid

variable {R : Type*} [Ring R]

/-- A simple `R`-module is torsion by the Jacobson radical of `R`: the radical annihilates
every simple module. -/
private theorem isTorsionBySet_jacobson {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Module.IsTorsionBySet R M (Ring.jacobson R) := fun x a =>
  Module.mem_annihilator.mp (IsSemisimpleModule.jacobson_le_annihilator R M a.2) x

/-- The `R ⧸ rad`-module structure carried by a simple `R`-module (the radical acts as `0`). -/
@[implicit_reducible]
private noncomputable def jacobsonModule {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Module (R ⧸ Ring.jacobson R) M :=
  (isTorsionBySet_jacobson (R := R) (M := M)).module

/-- With its `R ⧸ rad`-module structure, a simple `R`-module is a simple `R ⧸ rad`-module:
`rad` acts as `0`, so `R`-submodules and `R ⧸ rad`-submodules coincide. -/
private theorem isSimpleModule_jacobsonModule {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] :
    letI := jacobsonModule (R := R) (M := M); IsSimpleModule (R ⧸ Ring.jacobson R) M :=
  letI := jacobsonModule (R := R) (M := M)
  ((isTorsionBySet_jacobson (R := R) (M := M)).semilinearMap.isSimpleModule_iff_of_bijective
    Function.bijective_id).mp inferInstance

/-- An `R ⧸ rad`-linear map between two simple `R`-modules (with their descended module
structures) is automatically `R`-linear: the two actions agree because `rad` acts as `0`. -/
private noncomputable def demoteEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [IsSimpleModule R M] [IsSimpleModule R N]
    (e : letI := jacobsonModule (R := R) (M := M); letI := jacobsonModule (R := R) (M := N);
      M ≃ₗ[R ⧸ Ring.jacobson R] N) : M ≃ₗ[R] N :=
  letI := jacobsonModule (R := R) (M := M)
  letI := jacobsonModule (R := R) (M := N)
  { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
    map_add' := e.map_add
    map_smul' := fun r x => e.map_smul (Ideal.Quotient.mk _ r) x }

/-- An `R`-linear equivalence between two simple `R`-modules promotes to an
`R ⧸ rad`-linear equivalence for their descended module structures. -/
private noncomputable def promoteEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [IsSimpleModule R M] [IsSimpleModule R N] (e : M ≃ₗ[R] N) :
    letI := jacobsonModule (R := R) (M := M); letI := jacobsonModule (R := R) (M := N);
      M ≃ₗ[R ⧸ Ring.jacobson R] N :=
  letI := jacobsonModule (R := R) (M := M)
  letI := jacobsonModule (R := R) (M := N)
  { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
    map_add' := e.map_add
    map_smul' := fun a x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact e.map_smul r x }

open scoped Classical in
/-- **Finitely many simple modules.** A ring `R` that is finite-dimensional as an algebra over
a field `k` has only finitely many isomorphism classes of simple modules (with underlying types
in the universe of `k`).

The radical `rad = Ring.jacobson R` annihilates every simple module, so simple `R`-modules are
simple modules over the semisimple quotient `A = R ⧸ rad`. Over the semisimple (hence Noetherian)
ring `A`, each simple module embeds into `A` as a submodule lying in one of the finitely many
isotypic components of `A` (`isotypicComponents A A`). Sending a simple module to the isotypic
component of its descent is therefore an injection into a finite type. -/
theorem finite_simpleModuleClasses (k : Type u) {R : Type*} [Field k] [Ring R] [Algebra k R]
    [Module.Finite k R] : Finite (SimpleModuleClasses.{u} R) := by
  classical
  haveI : IsArtinianRing R := isArtinian_of_tower k inferInstance
  haveI : IsSemiprimaryRing R := inferInstance
  set A := R ⧸ Ring.jacobson R with hA
  haveI : IsSemisimpleRing A := inferInstance
  haveI : Finite (isotypicComponents A A) := inferInstance
  -- Object-level assignment: a simple `R`-module ↦ the isotypic component of its `A`-descent.
  have hsimp : ∀ P : (simpleProp (ModuleCat.{u} R)).FullSubcategory,
      IsSimpleModule R (P.obj : ModuleCat.{u} R) := fun P => by
    haveI : Simple P.obj := P.property
    exact isSimpleModule_of_simple _
  let f : (simpleProp (ModuleCat.{u} R)).FullSubcategory → isotypicComponents A A := fun P => by
    haveI := hsimp P
    letI := jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
    haveI := isSimpleModule_jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
    refine ⟨isotypicComponent A A (P.obj : ModuleCat.{u} R), ?_⟩
    obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
      A (P.obj : ModuleCat.{u} R)
    exact ⟨I, IsSimpleModule.congr e.symm, e.isotypicComponent_eq⟩
  -- Isomorphic simple modules give equal components (well-definedness on iso classes).
  have hresp : ∀ P Q : (simpleProp (ModuleCat.{u} R)).FullSubcategory, P ≈ Q → f P = f Q := by
    rintro P Q ⟨iso⟩
    haveI := hsimp P; haveI := hsimp Q
    letI := jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
    letI := jacobsonModule (R := R) (M := (Q.obj : ModuleCat.{u} R))
    apply Subtype.ext
    have eR : (P.obj : ModuleCat.{u} R) ≃ₗ[R] (Q.obj : ModuleCat.{u} R) :=
      ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
    exact (promoteEquiv (R := R) (M := (P.obj : ModuleCat.{u} R))
      (N := (Q.obj : ModuleCat.{u} R)) eR).isotypicComponent_eq
  -- The assignment is injective on isomorphism classes, so the class type is finite.
  refine Finite.of_injective (Quotient.lift f hresp) ?_
  intro a b
  refine Quotient.inductionOn₂ a b (fun P Q hab => ?_)
  simp only [Quotient.lift_mk] at hab
  haveI := hsimp P; haveI := hsimp Q
  letI := jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
  letI := jacobsonModule (R := R) (M := (Q.obj : ModuleCat.{u} R))
  haveI := isSimpleModule_jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
  haveI := isSimpleModule_jacobsonModule (R := R) (M := (Q.obj : ModuleCat.{u} R))
  have hcomp : isotypicComponent A A (P.obj : ModuleCat.{u} R)
      = isotypicComponent A A (Q.obj : ModuleCat.{u} R) := congrArg Subtype.val hab
  obtain ⟨I, ⟨eP⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    A (P.obj : ModuleCat.{u} R)
  haveI : IsSimpleModule A (I : Submodule A A) := IsSimpleModule.congr eP.symm
  have key : isotypicComponent A A (I : Submodule A A)
      = isotypicComponent A A (Q.obj : ModuleCat.{u} R) :=
    eP.isotypicComponent_eq.symm.trans hcomp
  have hIle : (I : Submodule A A) ≤ isotypicComponent A A (Q.obj : ModuleCat.{u} R) :=
    (Submodule.le_isotypicComponent I).trans key.le
  obtain ⟨eQ⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent A A (Q.obj : ModuleCat.{u} R)) I hIle
  have eR : (P.obj : ModuleCat.{u} R) ≃ₗ[R] (Q.obj : ModuleCat.{u} R) :=
    demoteEquiv (R := R) (M := (P.obj : ModuleCat.{u} R))
      (N := (Q.obj : ModuleCat.{u} R)) (eP.trans eQ)
  exact Quotient.sound
    ⟨(simpleProp (ModuleCat.{u} R)).fullyFaithfulι.preimageIso eR.toModuleIso⟩

/-! ### Radical-quotient invariance of the simple count

Passing to the semisimple quotient `R ⧸ rad` leaves the number of isomorphism classes of simple
modules unchanged. The radical annihilates every simple module, so restriction of scalars along the
surjection `R ↠ R ⧸ rad` is a bijection between the simple `R ⧸ rad`-modules and the simple
`R`-modules; it descends to an equivalence, hence a `Nat.card` equality, on isomorphism classes. -/

/-- The identity map identifies two `S`-module structures on the same additive group whose scalar
actions agree, as an isomorphism of the corresponding bundled modules. -/
private def idModuleIso {S : Type*} [Ring S] {M : Type u} [AddCommGroup M]
    (i₁ i₂ : Module S M) (h : ∀ (s : S) (x : M), (letI := i₁; s • x) = (letI := i₂; s • x)) :
    (letI := i₁; ModuleCat.of S M) ≅ (letI := i₂; ModuleCat.of S M) :=
  @LinearEquiv.toModuleIso S _ M M _ _ i₁ i₂
    (@AddEquiv.toLinearEquiv S M M _ _ _ i₁ i₂ (AddEquiv.refl M) h)

/-- Restriction of scalars along `R ↠ R ⧸ rad`: an `R ⧸ rad`-module is an `R`-module (the radical
acts as `0`). -/
@[implicit_reducible]
private noncomputable def restrictedModule {M : Type*} [AddCommGroup M]
    [Module (R ⧸ Ring.jacobson R) M] : Module R M :=
  Module.compHom M (Ideal.Quotient.mk (Ring.jacobson R))

/-- A simple `R ⧸ rad`-module remains simple after restricting scalars to `R`: the `R`- and
`R ⧸ rad`-submodules coincide because `R ↠ R ⧸ rad` is surjective. -/
private theorem isSimpleModule_restrictedModule {M : Type*} [AddCommGroup M]
    [Module (R ⧸ Ring.jacobson R) M] [IsSimpleModule (R ⧸ Ring.jacobson R) M] :
    letI := restrictedModule (R := R) (M := M); IsSimpleModule R M :=
  letI := restrictedModule (R := R) (M := M)
  ((({ toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      M →ₛₗ[Ideal.Quotient.mk (Ring.jacobson R)] M)).isSimpleModule_iff_of_bijective
    Function.bijective_id).mpr inferInstance

/-- Object map `demote`: a simple `R`-module carried to its underlying simple `R ⧸ rad`-module. -/
@[reducible]
private noncomputable def demoteSimpleObj
    (P : (simpleProp (ModuleCat.{u} R)).FullSubcategory) :
    (simpleProp (ModuleCat.{u} (R ⧸ Ring.jacobson R))).FullSubcategory := by
  haveI : Simple P.obj := P.property
  haveI : IsSimpleModule R (P.obj : ModuleCat.{u} R) := isSimpleModule_of_simple _
  letI := jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
  haveI := isSimpleModule_jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
  exact ⟨ModuleCat.of (R ⧸ Ring.jacobson R) (P.obj : ModuleCat.{u} R), simple_of_isSimpleModule⟩

/-- Object map `inflate`: a simple `R ⧸ rad`-module carried to its underlying simple
`R`-module (restriction of scalars). -/
@[reducible]
private noncomputable def inflateSimpleObj
    (Q : (simpleProp (ModuleCat.{u} (R ⧸ Ring.jacobson R))).FullSubcategory) :
    (simpleProp (ModuleCat.{u} R)).FullSubcategory := by
  haveI : Simple Q.obj := Q.property
  haveI : IsSimpleModule (R ⧸ Ring.jacobson R)
      (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) := isSimpleModule_of_simple _
  letI := restrictedModule (R := R) (M := (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)))
  haveI := isSimpleModule_restrictedModule (R := R)
    (M := (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)))
  exact ⟨ModuleCat.of R (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)), simple_of_isSimpleModule⟩

variable (R) in
/-- **Radical-quotient bijection.** Restriction of scalars along `R ↠ R ⧸ rad` gives a bijection
between isomorphism classes of simple `R ⧸ rad`-modules and isomorphism classes of simple
`R`-modules. -/
noncomputable def simpleModuleClassesQuotientJacobsonEquiv :
    SimpleModuleClasses.{u} (R ⧸ Ring.jacobson R) ≃ SimpleModuleClasses.{u} R where
  toFun := Quotient.map inflateSimpleObj (by
    rintro Q Q' ⟨iso⟩
    haveI : Simple Q.obj := Q.property
    haveI : Simple Q'.obj := Q'.property
    haveI : IsSimpleModule (R ⧸ Ring.jacobson R)
        (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) := isSimpleModule_of_simple _
    haveI : IsSimpleModule (R ⧸ Ring.jacobson R)
        (Q'.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) := isSimpleModule_of_simple _
    letI := restrictedModule (R := R) (M := (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)))
    letI := restrictedModule (R := R) (M := (Q'.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)))
    have eA : (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) ≃ₗ[R ⧸ Ring.jacobson R]
        (Q'.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) :=
      ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
    let eR : (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) ≃ₗ[R]
        (Q'.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) :=
      { toFun := eA, invFun := eA.symm, left_inv := eA.left_inv, right_inv := eA.right_inv,
        map_add' := eA.map_add,
        map_smul' := fun r x => eA.map_smul (Ideal.Quotient.mk (Ring.jacobson R) r) x }
    exact ⟨(simpleProp (ModuleCat.{u} R)).fullyFaithfulι.preimageIso eR.toModuleIso⟩)
  invFun := Quotient.map demoteSimpleObj (by
    rintro P P' ⟨iso⟩
    haveI : Simple P.obj := P.property
    haveI : Simple P'.obj := P'.property
    haveI : IsSimpleModule R (P.obj : ModuleCat.{u} R) := isSimpleModule_of_simple _
    haveI : IsSimpleModule R (P'.obj : ModuleCat.{u} R) := isSimpleModule_of_simple _
    have eR : (P.obj : ModuleCat.{u} R) ≃ₗ[R] (P'.obj : ModuleCat.{u} R) :=
      ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
    exact ⟨(simpleProp (ModuleCat.{u} (R ⧸ Ring.jacobson R))).fullyFaithfulι.preimageIso
      (promoteEquiv (R := R) (M := (P.obj : ModuleCat.{u} R))
        (N := (P'.obj : ModuleCat.{u} R)) eR).toModuleIso⟩)
  left_inv := by
    rintro y
    induction y using Quotient.inductionOn with
    | _ Q =>
      haveI : Simple Q.obj := Q.property
      exact Quotient.sound
        ⟨(simpleProp (ModuleCat.{u} (R ⧸ Ring.jacobson R))).fullyFaithfulι.preimageIso
          (idModuleIso _ inferInstance (fun a x => by
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a; rfl))⟩
  right_inv := by
    rintro y
    induction y using Quotient.inductionOn with
    | _ P =>
      haveI : Simple P.obj := P.property
      haveI hsP : IsSimpleModule R (P.obj : ModuleCat.{u} R) := isSimpleModule_of_simple _
      let iAj : Module (R ⧸ Ring.jacobson R) (P.obj : ModuleCat.{u} R) :=
        jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
      let iRc : Module R (P.obj : ModuleCat.{u} R) :=
        @restrictedModule R _ (P.obj : ModuleCat.{u} R) _ iAj
      exact Quotient.sound
        ⟨(simpleProp (ModuleCat.{u} R)).fullyFaithfulι.preimageIso
          (idModuleIso iRc inferInstance (fun r x => rfl))⟩

/-- **Radical-quotient invariance of the simple count.** The number of isomorphism classes of
simple modules is unchanged when passing to the Jacobson-radical quotient. -/
theorem natCard_simpleModuleClasses_quotient_jacobson (k : Type u) [Field k] [Algebra k R]
    [Module.Finite k R] :
    Nat.card (SimpleModuleClasses.{u} (R ⧸ Ring.jacobson R))
      = Nat.card (SimpleModuleClasses.{u} R) :=
  Nat.card_congr (simpleModuleClassesQuotientJacobsonEquiv R)

instance IrrepClasses.instFinite {k G : Type*} [Field k] [Group G] [Finite G] :
    Finite (IrrepClasses k G) := by
  haveI : Module.Finite k (MonoidAlgebra k G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G k)
  haveI := finite_simpleModuleClasses k (R := MonoidAlgebra k G)
  exact Finite.of_equiv _ (irrepClassesEquivSimpleModuleClasses k G).symm

end Finiteness

-- **Exercise 4.2.3** (`Etingof.Exercise4_2_3`, the strict modular counting drop
-- `Nat.card (IrrepClasses k G) < Nat.card (ConjClasses G)`) is proved downstream in
-- `Exercise4_2_3_Assembly.lean`: this file cannot state it here because the split-field and
-- strict-bound machinery it depends on (`Exercise4_2_3_FieldGeneral.lean`,
-- `Exercise4_2_3_StrictBound.lean`) both import this file.

end Etingof

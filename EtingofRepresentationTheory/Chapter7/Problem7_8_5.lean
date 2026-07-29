import Mathlib
import EtingofRepresentationTheory.Chapter7.Definition7_8_6

set_option backward.isDefEq.respectTransparency false

/-!
# Problem 7.8.5: Long exact sequence of cohomology from a subcomplex

This file gives both versions of the construction.  The first section constructs the
degreewise quotient `D i ⧸ C i` from an honest family of submodules stable under the
differential.  The second section retains the useful abstract formulation in terms of an
arbitrary short exact sequence of complexes.
-/

open CategoryTheory

namespace Etingof

abbrev Problem7_8_5_Complex :=
  HomologicalComplex (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)

/-- A literal subcomplex of a complex of abelian groups: submodules in every degree,
stable under the differential. -/
structure Problem7_8_5_Subcomplex (D : Problem7_8_5_Complex) where
  obj : (i : ℤ) → Submodule ℤ (D.X i)
  d_mem : ∀ {i j : ℤ} {x : D.X i}, x ∈ obj i → D.d i j x ∈ obj j

namespace Problem7_8_5_Subcomplex

variable {D : Problem7_8_5_Complex} (C : Problem7_8_5_Subcomplex D)

/-- The ambient complex with its underlying abelian groups equipped with the canonical
`ℤ`-module structure.  This removes the irrelevant choice of a `ℤ`-module instance from
the concrete quotient construction. -/
def canonical (D : Problem7_8_5_Complex) : Problem7_8_5_Complex where
  X i := @ModuleCat.of ℤ Int.instRing (D.X i) (D.X i).isAddCommGroup
    (AddCommGroup.toIntModule (D.X i))
  d i j := @ModuleCat.ofHom ℤ Int.instRing (D.X i) (D.X j)
    (D.X i).isAddCommGroup (AddCommGroup.toIntModule (D.X i))
    (D.X j).isAddCommGroup (AddCommGroup.toIntModule (D.X j))
    (D.d i j).hom.toAddMonoidHom.toIntLinearMap
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simpa using ConcreteCategory.congr_hom (D.shape i j hij) x
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change D.d j k (D.d i j x) = 0
    rw [← ConcreteCategory.comp_apply, D.d_comp_d]
    rfl

/-- The complex whose degree `i` term is the submodule `C.obj i`. -/
def complex : Problem7_8_5_Complex where
  X i := ModuleCat.of ℤ (C.obj i)
  d i j := ModuleCat.ofHom <| (AddMonoidHom.mk'
    (fun x : C.obj i ↦ (⟨D.d i j x, C.d_mem x.property⟩ : C.obj j))
    (by intro x y; ext; simp)).toIntLinearMap
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [D.shape i j hij]
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change D.d j k (D.d i j x) = 0
    rw [← ConcreteCategory.comp_apply, D.d_comp_d]
    rfl

/-- The inclusion of the subcomplex into `D`. -/
def inclusion : C.complex ⟶ canonical D where
  f i := @ModuleCat.ofHom ℤ Int.instRing (C.obj i) (D.X i)
    (C.obj i).addCommGroup (AddCommGroup.toIntModule (C.obj i))
    (D.X i).isAddCommGroup (AddCommGroup.toIntModule (D.X i)) <|
      (AddMonoidHom.mk' (fun x : C.obj i ↦ (x : D.X i)) (by simp)).toIntLinearMap
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- The textbook quotient complex, with degree `i` term the literal module quotient
`D.X i ⧸ C.obj i`. -/
def quotient : Problem7_8_5_Complex where
  X i := ModuleCat.of ℤ (D.X i ⧸ (C.obj i).toAddSubgroup)
  d i j := ModuleCat.ofHom <| (QuotientAddGroup.map (C.obj i).toAddSubgroup
    (C.obj j).toAddSubgroup (D.d i j).hom.toAddMonoidHom <| by
    intro x hx
    exact C.d_mem hx).toIntLinearMap
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using Quotient.inductionOn' with
    | _ x =>
    simp [D.shape i j hij]
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using Quotient.inductionOn' with
    | _ x =>
      have hd : D.d j k (D.d i j x) = 0 := by
        rw [← ConcreteCategory.comp_apply, D.d_comp_d]
        rfl
      simp [hd]

/-- The degreewise quotient projection `D ⟶ D/C`. -/
def projection : canonical D ⟶ C.quotient where
  f i := @ModuleCat.ofHom ℤ Int.instRing (D.X i)
    (D.X i ⧸ (C.obj i).toAddSubgroup)
    (D.X i).isAddCommGroup (AddCommGroup.toIntModule (D.X i))
    (QuotientAddGroup.Quotient.addCommGroup (C.obj i).toAddSubgroup)
    (AddCommGroup.toIntModule (D.X i ⧸ (C.obj i).toAddSubgroup)) <|
      (QuotientAddGroup.mk' (C.obj i).toAddSubgroup).toIntLinearMap
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- The canonical sequence `0 → C → D → D/C → 0`. -/
def shortComplex : ShortComplex Problem7_8_5_Complex :=
  ShortComplex.mk C.inclusion C.projection (by
    ext i x
    change C.obj i at x
    change QuotientAddGroup.mk' (C.obj i).toAddSubgroup (x : D.X i) = 0
    rw [QuotientAddGroup.mk'_apply]
    exact (QuotientAddGroup.eq_zero_iff (x : D.X i)).mpr x.property)

/-- The canonical subcomplex/quotient sequence is short exact. -/
theorem shortExact : C.shortComplex.ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact
      (fun x : C.obj i ↦ (x : D.X i))
      (QuotientAddGroup.mk' (C.obj i).toAddSubgroup)
    intro x
    change QuotientAddGroup.mk' (C.obj i).toAddSubgroup x = 0 ↔
      x ∈ Set.range (fun y : C.obj i ↦ (y : D.X i))
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  · intro x y h
    exact Subtype.ext h
  · exact QuotientAddGroup.mk'_surjective _

/-- If the quotient class represented by `x : D i` is a cocycle, then `d x` lies in
the subcomplex.  This is the key lift/differential step in the textbook chase. -/
theorem differential_mem_of_quotient_cycle (i j : ℤ) (x : D.X i)
    (hx : C.quotient.d i j (C.projection.f i x) = 0) :
    D.d i j x ∈ C.obj j := by
  change QuotientAddGroup.map (C.obj i).toAddSubgroup (C.obj j).toAddSubgroup
    (D.d i j).hom.toAddMonoidHom (by intro y hy; exact C.d_mem hy)
      (QuotientAddGroup.mk' (C.obj i).toAddSubgroup x) = 0 at hx
  rw [QuotientAddGroup.map_mk'] at hx
  exact (QuotientAddGroup.eq_zero_iff (D.d i j x)).mp hx

/-- The element of `C j` prescribed by the representative/lift construction: lift a
quotient cocycle to `x : D i`, apply `d`, and regard the result as an element of `C j`. -/
def liftedDifferential (i j : ℤ) (x : D.X i)
    (hx : C.quotient.d i j (C.projection.f i x) = 0) : C.obj j :=
  ⟨D.d i j x, C.differential_mem_of_quotient_cycle i j x hx⟩

/-- The homology class of the quotient cocycle represented by `x`. -/
noncomputable def quotientCocycleClass (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (x : D.X i) (hx : C.quotient.d i j (C.projection.f i x) = 0) :
    C.quotient.homology i :=
  C.quotient.homologyπ i
    (C.quotient.cyclesMk (C.projection.f i x) j
      ((ComplexShape.up ℤ).next_eq' hij) hx)

/-- The homology class in `C` of the lifted differential `d x`. -/
noncomputable def liftedDifferentialClass (i j : ℤ)
    (x : D.X i) (hx : C.quotient.d i j (C.projection.f i x) = 0)
    (k : ℤ) (hk : (ComplexShape.up ℤ).next j = k) : C.complex.homology j :=
  C.complex.homologyπ j
    (C.complex.cyclesMk (C.liftedDifferential i j x hx) k hk
      (C.shortExact.d_eq_zero_of_f_eq_d_apply i j x
        (C.liftedDifferential i j x hx) rfl k))

/-- The concrete connecting morphism attached to the literal quotient complex `D/C`. -/
noncomputable def concreteConnecting (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    C.quotient.homology i ⟶ C.complex.homology j :=
  C.shortExact.δ i j hij

/-- The representative/lift/differential formula from the text.  The quotient cocycle
represented by `x` is sent to the homology class of `d x`, viewed in `C`.  In particular,
this proves that the concrete chase computes Mathlib's categorical `ShortExact.δ`. -/
theorem connecting_formula (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (x : D.X i) (hx : C.quotient.d i j (C.projection.f i x) = 0)
    (k : ℤ) (hk : (ComplexShape.up ℤ).next j = k) :
    C.concreteConnecting i j hij (C.quotientCocycleClass i j hij x hx) =
      C.liftedDifferentialClass i j x hx k hk := by
  simpa [concreteConnecting, quotientCocycleClass, liftedDifferentialClass,
    shortComplex, projection, inclusion, canonical, complex, liftedDifferential] using
    C.shortExact.δ_apply i j hij (C.projection.f i x) hx x rfl
      (C.liftedDifferential i j x hx) rfl k hk

/-- Independence of every choice in the chase.  If two representatives/lifts determine
the same input homology class, then their lifted differentials determine the same class in
`H^{i+1}(C)`.  This simultaneously covers changing the quotient representative and changing
its lift in `D`. -/
theorem connecting_wellDefined (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (x y : D.X i)
    (hx : C.quotient.d i j (C.projection.f i x) = 0)
    (hy : C.quotient.d i j (C.projection.f i y) = 0)
    (k : ℤ) (hk : (ComplexShape.up ℤ).next j = k)
    (hxy : C.quotientCocycleClass i j hij x hx =
      C.quotientCocycleClass i j hij y hy) :
    C.liftedDifferentialClass i j x hx k hk =
      C.liftedDifferentialClass i j y hy k hk := by
  rw [← C.connecting_formula i j hij x hx k hk,
    ← C.connecting_formula i j hij y hy k hk, hxy]

/-- In particular, two lifts of the same quotient cocycle give the same output class. -/
theorem connecting_lift_independent (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) (x y : D.X i)
    (hx : C.quotient.d i j (C.projection.f i x) = 0)
    (hy : C.quotient.d i j (C.projection.f i y) = 0)
    (hproj : C.projection.f i x = C.projection.f i y)
    (k : ℤ) (hk : (ComplexShape.up ℤ).next j = k) :
    C.liftedDifferentialClass i j x hx k hk =
      C.liftedDifferentialClass i j y hy k hk := by
  apply C.connecting_wellDefined i j hij x y hx hy k hk
  unfold quotientCocycleClass
  congr 2

/-- The concrete quotient construction agrees with the categorical snake-lemma map. -/
theorem concreteConnecting_eq_categorical (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    C.concreteConnecting i j hij = C.shortExact.δ i j hij :=
  rfl

end Problem7_8_5_Subcomplex

/-- The connecting homomorphism `c_i : H^i(E) → H^{i+1}(C)` for an abstract short exact
sequence.  This reusable abstract declaration is retained for Definition 7.8.6. -/
noncomputable def Problem7_8_5_connecting
    {S : ShortComplex Problem7_8_5_Complex}
    (hS : S.ShortExact) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij

/-- The abstract long-exact-sequence theorem, useful for any presentation of a short exact
sequence of complexes. -/
theorem Problem7_8_5
    {S : ShortComplex Problem7_8_5_Complex}
    (hS : S.ShortExact) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i)
      (by rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact ∧
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  ⟨hS.homology_exact₁ i j hij, hS.homology_exact₂ i, hS.homology_exact₃ i j hij⟩

/-- Problem 7.8.5 for the literal subcomplex and quotient constructed above.  The maps in
this exact sequence use `concreteConnecting`; the comparison theorem and representative
formula identify it with both the textbook chase and the categorical snake-lemma map. -/
theorem Problem7_8_5_quotient
    {D : Problem7_8_5_Complex} (C : Problem7_8_5_Subcomplex D)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (ShortComplex.mk (C.concreteConnecting i j hij)
      (HomologicalComplex.homologyMap C.shortComplex.f j)
      (by simp [Problem7_8_5_Subcomplex.concreteConnecting,
        ShortComplex.ShortExact.δ_comp C.shortExact i j hij])).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap C.shortComplex.f i)
      (HomologicalComplex.homologyMap C.shortComplex.g i)
      (by rw [← HomologicalComplex.homologyMap_comp, C.shortComplex.zero,
          HomologicalComplex.homologyMap_zero])).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap C.shortComplex.g i)
      (C.concreteConnecting i j hij)
      (by simp [Problem7_8_5_Subcomplex.concreteConnecting,
        ShortComplex.ShortExact.comp_δ C.shortExact i j hij])).Exact := by
  simpa [Problem7_8_5_Subcomplex.concreteConnecting] using
    Problem7_8_5 C.shortExact i j hij

end Etingof

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Module.DirectSumData

universe w v u

namespace RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RepresentationTheory.Algebra.Module.DirectSumData

section ExtCongr

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Isomorphisms in both arguments induce an additive equivalence between the corresponding Ext groups. -/
noncomputable def CategoryTheory.Abelian.Ext.addEquiv_of_isos {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) :
    Abelian.Ext.{w} X Y n ≃+ Abelian.Ext.{w} X' Y' n where
  toFun α :=
    (Abelian.Ext.mk₀ e.inv).comp (α.comp (Abelian.Ext.mk₀ f.hom) (add_zero n)) (zero_add n)
  invFun β :=
    (Abelian.Ext.mk₀ e.hom).comp (β.comp (Abelian.Ext.mk₀ f.inv) (add_zero n)) (zero_add n)
  left_inv α := by
    simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.comp_assoc_of_third_deg_zero, Iso.hom_inv_id, Abelian.Ext.comp_mk₀_id,
      Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_id_comp]
  right_inv β := by
    simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.comp_assoc_of_third_deg_zero, Iso.inv_hom_id, Abelian.Ext.comp_mk₀_id,
      Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_id_comp]
  map_add' α₁ α₂ := by
    simp only [Abelian.Ext.add_comp, Abelian.Ext.comp_add]

end ExtCongr

section ProjectiveDimension

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A finite biproduct has projective dimension below a bound when every summand does. -/
lemma CategoryTheory.hasProjectiveDimensionLT_biproduct {ι : Type*} [Finite ι] (X : ι → C) [HasBiproduct X]
    (n : ℕ) (h : ∀ i, HasProjectiveDimensionLT (X i) n) :
    HasProjectiveDimensionLT (⨁ X) n :=
  HasProjectiveDimensionLT.mk fun i hi Y e => by
    haveI := Fintype.ofFinite ι
    haveI : ∀ j, Subsingleton (Abelian.Ext.{w} (X j) Y i) := fun j =>
      have := h j
      HasProjectiveDimensionLT.subsingleton (X j) n i hi Y
    haveI : Subsingleton (∀ j, Abelian.Ext.{w} (X j) Y i) :=
      ⟨fun _ _ => funext fun _ => Subsingleton.elim _ _⟩
    exact (Abelian.Ext.biproductAddEquiv (biproduct.isBilimit X) Y i).subsingleton.elim _ _

end ProjectiveDimension

/-- Splits a dependent family of additive groups indexed by a sum into a pair of families. -/
@[simps]
def AddEquiv.pi_sum {α β : Type*} (f : α ⊕ β → Type*) [∀ j, AddCommGroup (f j)] :
    (∀ j, f j) ≃+ (∀ a, f (Sum.inl a)) × (∀ b, f (Sum.inr b)) where
  toFun g := (fun a => g (Sum.inl a), fun b => g (Sum.inr b))
  invFun p := Sum.rec p.1 p.2
  left_inv g := funext fun j => by cases j <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The forward sum-indexed family equivalence restricts a family to the two summands. -/
add_decl_doc AddEquiv.pi_sum_apply

/-- The inverse sum-indexed family equivalence selects the appropriate component of a pair. -/
add_decl_doc AddEquiv.pi_sum_symm_apply

/-- A dependent function type is a subsingleton when each of its fibers is a subsingleton. -/
lemma subsingleton_pi {α : Type*} (f : α → Type*) [∀ a, Subsingleton (f a)] :
    Subsingleton (∀ a, f a) :=
  ⟨fun _ _ => funext fun _ => Subsingleton.elim _ _⟩

/-- A product with a subsingleton first factor is additively equivalent to its second factor. -/
noncomputable def AddEquiv.prod_right_of_subsingleton (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Subsingleton X] : (X × Y) ≃+ Y where
  toFun p := p.2
  invFun y := (0, y)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- A product with a subsingleton second factor is additively equivalent to its first factor. -/
noncomputable def AddEquiv.prod_left_of_subsingleton (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Subsingleton Y] : (X × Y) ≃+ X where
  toFun p := p.1
  invFun x := (x, 0)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl

section Reduction

variable {A : Type u} [CommRing A] {M N : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- Provides an additive equivalence from an expression with a specified first module-category object to a function type indexed by auxiliary objects. -/
noncomputable def Auxiliary.addEquiv_pi_left (D : Module.DirectSumData A M) (Y : _root_.ModuleCat.{u} A)
    (n : ℕ) :
    RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (_root_.ModuleCat.of A M) Y n ≃+ ∀ j : D.summandIndex, RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (D.summand j) Y n :=
  (CategoryTheory.Abelian.Ext.addEquiv_of_isos D.moduleIsoBiproduct (Iso.refl Y) n).trans
    (Abelian.Ext.biproductAddEquiv (biproduct.isBilimit D.summand) Y n)

/-- Provides an additive equivalence from an expression with a specified second module-category object to a function type indexed by auxiliary objects. -/
noncomputable def Auxiliary.addEquiv_pi_right (X : _root_.ModuleCat.{u} A) (E : Module.DirectSumData A N)
    (n : ℕ) :
    RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses X (_root_.ModuleCat.of A N) n ≃+ ∀ l : E.summandIndex, RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses X (E.summand l) n :=
  (CategoryTheory.Abelian.Ext.addEquiv_of_isos (Iso.refl X) E.moduleIsoBiproduct n).trans
    (Abelian.Ext.addEquivBiproduct X (biproduct.isBilimit E.summand) n)

/-- Provides an additive equivalence from an expression with two specified module-category objects to a doubly indexed function type built from auxiliary objects. -/
noncomputable def Auxiliary.addEquiv_pi_both (D : Module.DirectSumData A M) (E : Module.DirectSumData A N)
    (n : ℕ) :
    RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (_root_.ModuleCat.of A M) (_root_.ModuleCat.of A N) n ≃+
      ∀ (j : D.summandIndex) (l : E.summandIndex), RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (D.summand j) (E.summand l) n :=
  (CategoryTheory.Abelian.Ext.addEquiv_of_isos D.moduleIsoBiproduct E.moduleIsoBiproduct n).trans
    ((Abelian.Ext.biproductAddEquiv (biproduct.isBilimit D.summand) _ n).trans
      (AddEquiv.piCongrRight fun _ =>
        Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit E.summand) n))

/-- Additively identifies linear maps from the scalar ring to a module with elements of that module. -/
noncomputable def LinearMap.addEquiv_from_self (A : Type u) [CommRing A] (Z : Type u) [AddCommGroup Z]
    [Module A Z] : (A →ₗ[A] Z) ≃+ Z where
  toFun f := f 1
  invFun z := LinearMap.toSpanSingleton A Z z
  left_inv f := by ext; simp [LinearMap.toSpanSingleton_apply]
  right_inv z := by simp [LinearMap.toSpanSingleton_apply]
  map_add' _ _ := rfl

/-- Returns the scalar attached to an index in the combined indexing type. -/
def _root_.RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData.combined_coefficient (D : Module.DirectSumData A M) : D.summandIndex → A :=
  Sum.elim (fun _ => 0) D.quotientGenerator

/-- The combined coefficient vanishes on indices from the finite left summand. -/
@[simp] lemma _root_.RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData.combined_coefficient_inl (D : Module.DirectSumData A M) (i : Fin D.natParameter) :
    D.combined_coefficient (Sum.inl i) = 0 := rfl

/-- On the right summand, the combined coefficient agrees with the original coefficient. -/
@[simp] lemma _root_.RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData.combined_coefficient_inr (D : Module.DirectSumData A M) (i : D.Index) :
    D.combined_coefficient (Sum.inr i) = D.quotientGenerator i := rfl

/-- Identifies an indexed component with the quotient by the ideal generated by its coefficient. -/
noncomputable def _root_.RepresentationTheory.Algebra.Module.DirectSumData.Module.DirectSumData.component_iso_quotient_span (D : Module.DirectSumData A M) (j : D.summandIndex) :
    D.summand j ≅ _root_.ModuleCat.of A (A ⧸ Ideal.span {D.combined_coefficient j}) := by
  cases j with
  | inl i =>
    exact LinearEquiv.toModuleIso
      (Submodule.quotEquivOfEqBot _ (Ideal.span_singleton_eq_bot.mpr rfl)).symm
  | inr i => exact Iso.refl _

end Reduction

section PIDProjectiveDimension

variable (A : Type u) [CommRing A]

private noncomputable def mulByCoefficient (d : A) : A →ₗ[A] A := d • LinearMap.id

private lemma mulByCoefficient_apply (d x : A) : mulByCoefficient A d x = d * x := by
  simp [mulByCoefficient]

private lemma range_mulByCoefficient (d : A) :
    LinearMap.range (mulByCoefficient A d) = Ideal.span {d} := by
  ext x
  simp only [LinearMap.mem_range, mulByCoefficient_apply, Ideal.mem_span_singleton]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

/-- A quotient of a domain by a principal ideal generated by one element has projective dimension less than two. -/
lemma ModuleCat.hasProjectiveDimensionLT_two_quotient_span_singleton [IsDomain A] (d : A) :
    HasProjectiveDimensionLT (_root_.ModuleCat.of A (A ⧸ Ideal.span {d})) 2 := by
  haveI : HasProjectiveDimensionLT (_root_.ModuleCat.of A A) 2 :=
    hasProjectiveDimensionLT_of_ge (_root_.ModuleCat.of A A) 1 2 (by omega)
  rcases eq_or_ne d 0 with rfl | hd
  ·
    have hbot : (Ideal.span {(0 : A)} : Ideal A) = ⊥ := Ideal.span_singleton_eq_bot.mpr rfl
    exact hasProjectiveDimensionLT_of_iso
      (LinearEquiv.toModuleIso (Submodule.quotEquivOfEqBot _ hbot).symm) 2
  ·
    let f : A →ₗ[A] A := mulByCoefficient A d
    let g : A →ₗ[A] (A ⧸ Ideal.span {d}) := (Ideal.span {d} : Ideal A).mkQ
    have eq0 : g.comp f = 0 := LinearMap.ext fun x => by
      simpa only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        LinearMap.zero_apply, mulByCoefficient_apply, f, g] using Ideal.mem_span_singleton.mpr ⟨x, rfl⟩
    have hexact : Function.Exact f g := by
      rw [LinearMap.exact_iff, Submodule.ker_mkQ]
      exact (range_mulByCoefficient A d).symm
    have hinj : Function.Injective f := fun x y hxy =>
      mul_left_cancel₀ hd (by rw [← mulByCoefficient_apply A d x, ← mulByCoefficient_apply A d y]; exact hxy)
    have hsurj : Function.Surjective g := Submodule.mkQ_surjective _
    let S := _root_.ModuleCat.shortComplexOfCompEqZero f g eq0
    have hS : S.ShortExact := _root_.ModuleCat.shortComplex_shortExact S hexact hinj hsurj
    exact RepresentationTheory.PolynomialQuotientZModAuxiliary.hasProjectiveDimensionLT_two_of_shortExact
      hS inferInstance inferInstance

/-- Auxiliary module data over a domain yields projective dimension less than two. -/
lemma Auxiliary.hasProjectiveDimensionLT_two_of_data [IsDomain A] {M : Type u} [AddCommGroup M]
    [Module A M] (D : Module.DirectSumData A M) :
    HasProjectiveDimensionLT (_root_.ModuleCat.of A M) 2 := by
  haveI : HasProjectiveDimensionLT (_root_.ModuleCat.of A A) 2 :=
    hasProjectiveDimensionLT_of_ge (_root_.ModuleCat.of A A) 1 2 (by omega)
  haveI : HasProjectiveDimensionLT (⨁ D.summand) 2 :=
    CategoryTheory.hasProjectiveDimensionLT_biproduct D.summand 2 fun j => by
      cases j with
      | inl i => exact ‹HasProjectiveDimensionLT (_root_.ModuleCat.of A A) 2›
      | inr i => exact ModuleCat.hasProjectiveDimensionLT_two_quotient_span_singleton A (D.quotientGenerator i)
  exact hasProjectiveDimensionLT_of_iso D.moduleIsoBiproduct.symm 2

/-- A finite module over a principal ideal domain has projective dimension less than two. -/
lemma ModuleCat.hasProjectiveDimensionLT_two_of_finite_of_isPrincipalIdealRing [IsDomain A] [IsPrincipalIdealRing A] (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    HasProjectiveDimensionLT (_root_.ModuleCat.of A M) 2 :=
  (RepresentationTheory.Algebra.Module.DirectSumData.nonempty_directSumData A M).elim (Auxiliary.hasProjectiveDimensionLT_two_of_data A)

end PIDProjectiveDimension

/-- Provides auxiliary data for a finite module whose indexed coefficients are all nonzero. -/
theorem Auxiliary.exists_data_with_nonzero_coefficients (A : Type u) [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ D : Module.DirectSumData A M, ∀ i, D.quotientGenerator i ≠ 0 := by
  classical
  obtain ⟨n, ι, hι, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum A M
  refine ⟨{ natParameter := n
            Index := ι
            instFintypeIndex := hι
            instDecidableEqIndex := Classical.decEq ι
            quotientGenerator := fun i => p i ^ e i
            linearEquivFinFunProdQuotient := f ≪≫ₗ LinearEquiv.prodCongr
              (Finsupp.linearEquivFunOnFinite A A (Fin n))
              (DirectSum.linearEquivFunOnFintype A ι fun i => A ⧸ Ideal.span {p i ^ e i}) },
    fun i => pow_ne_zero _ (hp i).ne_zero⟩

end RepresentationTheory.HomologicalAlgebra.ProjectiveDimension.FiniteModulesOverPID

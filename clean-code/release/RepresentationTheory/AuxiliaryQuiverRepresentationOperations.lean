/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.Algebra.Quiver.AuxiliaryConstructions
import RepresentationTheory.QuiverRepresentation.Auxiliary
import RepresentationTheory.QuiverRepresentationQuotientTransform
import RepresentationTheory.Quiver.Finite
import Mathlib






















namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData



section Iso

variable {k : Type*} [Field k] {n : ℕ} [Q : Quiver (Fin n)]





/-- At each vertex, an auxiliary product representation has the product of the component vertex spaces. -/
@[simp] theorem auxiliaryProduct_obj (V₁ V₂ : AuxiliaryQuiverModuleData k (Fin n)) (v : Fin n) :
    (auxiliaryBinaryConstruction k (Fin n) V₁ V₂).obj v = (V₁.obj v × V₂.obj v) := rfl



/-- The arrow map of an auxiliary product representation is the product of the component arrow maps. -/
@[simp] theorem auxiliaryProduct_map (V₁ V₂ : AuxiliaryQuiverModuleData k (Fin n))
    {a b : Fin n} (f : a ⟶ b) :
    (auxiliaryBinaryConstruction k (Fin n) V₁ V₂).map f = (V₁.map f).prodMap (V₂.map f) := rfl


/-- A vertexwise linear equivalence commuting with every quiver arrow also commutes after evaluation on a vector. -/
theorem Related.commutes_apply {V W : AuxiliaryQuiverModuleData k (Fin n)}
    {e : ∀ v, V.obj v ≃ₗ[k] W.obj v}
    (he : ∀ {a b : Fin n} (f : a ⟶ b),
      (e b).toLinearMap ∘ₗ V.map f = W.map f ∘ₗ (e a).toLinearMap)
    {a b : Fin n} (f : a ⟶ b) (x : V.obj a) :
    e b (V.map f x) = W.map f (e a x) := by
  have := LinearMap.congr_fun (he f) x
  simpa using this

/-- Every auxiliary quiver representation is related to itself. -/
@[refl]
theorem Related.refl (V : AuxiliaryQuiverModuleData k (Fin n)) : V.Related V :=
  ⟨fun v => LinearEquiv.refl k (V.obj v), by
    intro a b f
    ext x
    simp⟩

/-- Auxiliary relations between quiver representations compose transitively. -/
theorem Related.trans {U V W : AuxiliaryQuiverModuleData k (Fin n)}
    (h₁ : U.Related V) (h₂ : V.Related W) : U.Related W := by
  obtain ⟨e, he⟩ := h₁
  obtain ⟨e', he'⟩ := h₂
  refine ⟨fun v => (e v).trans (e' v), ?_⟩
  intro a b f
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [Related.commutes_apply he f x, Related.commutes_apply he' f (e a x)]

/-- An auxiliary relation between quiver representations can be reversed. -/
theorem Related.symm {V W : AuxiliaryQuiverModuleData k (Fin n)}
    (h : V.Related W) : W.Related V := by
  obtain ⟨e, he⟩ := h
  refine ⟨fun v => (e v).symm, ?_⟩
  intro a b f
  ext y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq, Related.commutes_apply he f ((e a).symm y),
    LinearEquiv.apply_symm_apply]


/-- Auxiliary relations between two pairs of quiver representations induce a relation between their products. -/
theorem Related.prod {V₁ V₂ W₁ W₂ : AuxiliaryQuiverModuleData k (Fin n)}
    (h₁ : V₁.Related W₁) (h₂ : V₂.Related W₂) :
    (auxiliaryBinaryConstruction k (Fin n) V₁ V₂).Related (auxiliaryBinaryConstruction k (Fin n) W₁ W₂) := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  refine ⟨fun v => (e₁ v).prodCongr (e₂ v), ?_⟩
  intro a b f
  ext x
  exact Prod.ext (Related.commutes_apply he₁ f x.1) (Related.commutes_apply he₂ f x.2)

end Iso

section ZeroAndList

variable {k : Type*} [Field k] {n : ℕ} [Q : Quiver (Fin n)]




/-- The auxiliary zero quiver representation over a field. -/
def auxiliaryZero : AuxiliaryQuiverModuleData k (Fin n) where
  obj := fun _ => PUnit.{1}
  map := fun _ => 0


/-- A representation with subsingleton vertex spaces is related to the auxiliary zero representation. -/
theorem auxiliaryRelation_zero_of_subsingleton (V : AuxiliaryQuiverModuleData k (Fin n))
    (h : ∀ v, Subsingleton (V.obj v)) : V.Related auxiliaryZero := by
  refine ⟨fun v => ?_, ?_⟩
  · haveI := h v
    exact ({ toFun := 0
             invFun := 0
             map_add' := fun x y => Subsingleton.elim _ _
             map_smul' := fun c x => Subsingleton.elim _ _
             left_inv := fun x => Subsingleton.elim _ _
             right_inv := fun x => Subsingleton.elim _ _ } : V.obj v ≃ₗ[k] PUnit.{1})
  · intro a b f
    haveI : Subsingleton ((auxiliaryZero : AuxiliaryQuiverModuleData k (Fin n)).obj b) :=
      (inferInstance : Subsingleton PUnit)
    ext x
    exact Subsingleton.elim _ _


/-- Combines a list of auxiliary quiver representations into one representation. -/
noncomputable def auxiliaryListProduct (L : List (AuxiliaryQuiverModuleData k (Fin n))) :
    AuxiliaryQuiverModuleData k (Fin n) :=
  L.foldr (auxiliaryBinaryConstruction k (Fin n)) auxiliaryZero

/-- The auxiliary product of the empty list is the auxiliary zero representation. -/
@[simp] theorem auxiliaryListProduct_nil :
    auxiliaryListProduct ([] : List (AuxiliaryQuiverModuleData k (Fin n))) = auxiliaryZero := rfl

/-- The auxiliary product of a nonempty list is the product of its head with the product of its tail. -/
@[simp] theorem auxiliaryListProduct_cons (a : AuxiliaryQuiverModuleData k (Fin n))
    (L : List (AuxiliaryQuiverModuleData k (Fin n))) :
    auxiliaryListProduct (a :: L) = auxiliaryBinaryConstruction k (Fin n) a (auxiliaryListProduct L) := rfl


/-- An auxiliary representation is related to its product with the auxiliary zero representation on the right. -/
theorem auxiliaryProduct_zero_right (V : AuxiliaryQuiverModuleData k (Fin n)) :
    V.Related (auxiliaryBinaryConstruction k (Fin n) V auxiliaryZero) := by
  refine ⟨fun v => (LinearEquiv.prodUnique (R := k) (M := V.obj v) (M₂ := PUnit)).symm, ?_⟩
  intro a b f
  ext x ; rfl


/-- The product of the auxiliary zero representation with a representation is related to that representation. -/
theorem auxiliaryProduct_zero_left (V : AuxiliaryQuiverModuleData k (Fin n)) :
    (auxiliaryBinaryConstruction k (Fin n) auxiliaryZero V).Related V := by
  refine ⟨fun v => LinearEquiv.uniqueProd (R := k) (M := V.obj v) (M₂ := PUnit), ?_⟩
  intro a b f
  ext x ; rfl


/-- The two parenthesizations of a triple auxiliary product are related. -/
theorem auxiliaryProduct_assoc (A B C : AuxiliaryQuiverModuleData k (Fin n)) :
    (auxiliaryBinaryConstruction k (Fin n) (auxiliaryBinaryConstruction k (Fin n) A B) C).Related
      (auxiliaryBinaryConstruction k (Fin n) A (auxiliaryBinaryConstruction k (Fin n) B C)) := by
  refine ⟨fun v => LinearEquiv.prodAssoc k (A.obj v) (B.obj v) (C.obj v), ?_⟩
  intro a b f
  ext x ; rfl


/-- The product of the auxiliary list products is related to the auxiliary product of the appended lists. -/
theorem auxiliaryListProduct_append
    (LA LB : List (AuxiliaryQuiverModuleData k (Fin n))) :
    (auxiliaryBinaryConstruction k (Fin n) (auxiliaryListProduct LA) (auxiliaryListProduct LB)).Related
      (auxiliaryListProduct (LA ++ LB)) := by
  induction LA with
  | nil =>
      simp only [List.nil_append, auxiliaryListProduct_nil]
      refine ⟨fun v => ?_, ?_⟩
      · exact LinearEquiv.uniqueProd (R := k) (M := (auxiliaryListProduct LB).obj v) (M₂ := PUnit)
      · intro a b f
        ext x ; rfl
  | cons a L IH =>
      simp only [List.cons_append, auxiliaryListProduct_cons]
      refine (auxiliaryProduct_assoc a (auxiliaryListProduct L) (auxiliaryListProduct LB)).trans ?_
      exact (Related.refl a).prod IH

end ZeroAndList

section SubRep

variable {k : Type*} [Field k] {n : ℕ} [Q : Quiver (Fin n)]


/-- Builds an auxiliary quiver representation from a vertexwise family of submodules preserved by every arrow map. -/
def auxiliarySubobject (V : AuxiliaryQuiverModuleData k (Fin n)) (W : ∀ v, Submodule k (V.obj v))
    (hW : ∀ {a b : Fin n} (e : a ⟶ b), ∀ x ∈ W a, V.map e x ∈ W b) :
    AuxiliaryQuiverModuleData k (Fin n) where
  obj := fun v => W v
  map := fun {_a _b} e => (V.map e).restrict (hW e)

/-- The vertex space of the auxiliary subobject is the corresponding submodule subtype. -/
@[simp] theorem auxiliarySubobject_obj (V : AuxiliaryQuiverModuleData k (Fin n)) (W) (hW) (v : Fin n) :
    (auxiliarySubobject V W hW).obj v = W v := rfl



/-- Pointwise complementary invariant submodules give an auxiliary relation between a representation and the product of the associated subobjects. -/
theorem auxiliaryProduct_subobjects_of_isCompl (V : AuxiliaryQuiverModuleData k (Fin n))
    (W₁ W₂ : ∀ v, Submodule k (V.obj v))
    (hW₁ : ∀ {a b : Fin n} (e : a ⟶ b), ∀ x ∈ W₁ a, V.map e x ∈ W₁ b)
    (hW₂ : ∀ {a b : Fin n} (e : a ⟶ b), ∀ x ∈ W₂ a, V.map e x ∈ W₂ b)
    (hc : ∀ v, IsCompl (W₁ v) (W₂ v)) :
    V.Related (auxiliaryBinaryConstruction k (Fin n) (auxiliarySubobject V W₁ hW₁) (auxiliarySubobject V W₂ hW₂)) := by
  letI acg : ∀ v, AddCommGroup (V.obj v) := fun v => RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)





  let sc : ∀ v, (↥(W₁ v) × ↥(W₂ v)) →ₗ[k] V.obj v :=
    fun v => (W₁ v).subtype.coprod (W₂ v).subtype
  have hbij : ∀ v, Function.Bijective (sc v) := fun v =>
    (@Submodule.prodEquivOfIsCompl k _ (V.obj v) (acg v) (V.moduleInstance v)
      (W₁ v) (W₂ v) (hc v)).bijective
  let pe : ∀ v, (↥(W₁ v) × ↥(W₂ v)) ≃ₗ[k] V.obj v :=
    fun v => LinearEquiv.ofBijective (sc v) (hbij v)
  have hpe_apply : ∀ v (y : ↥(W₁ v) × ↥(W₂ v)), pe v y = sc v y := fun v y => rfl

  have hnat : ∀ {a b : Fin n} (f : a ⟶ b) (y : ↥(W₁ a) × ↥(W₂ a)),
      sc b ((auxiliaryBinaryConstruction k (Fin n) (auxiliarySubobject V W₁ hW₁) (auxiliarySubobject V W₂ hW₂)).map f y)
        = V.map f (sc a y) := by
    intro a b f y
    simp only [sc]
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, map_add,
      Submodule.coe_subtype, Submodule.coe_subtype, Submodule.coe_subtype, Submodule.coe_subtype]
    congr 1
  refine ⟨fun v => (pe v).symm, ?_⟩
  intro a b f
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  refine (pe b).symm_apply_eq.mpr ?_
  rw [hpe_apply, hnat]
  congr 1
  exact ((pe a).apply_symm_apply x).symm

end SubRep

section Existence

universe uk uh





/-- A nonzero submodule of a finite-dimensional vector space has positive dimension. -/
theorem finrank_pos_of_ne_bot {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] (p : Submodule k M) (hp : p ≠ ⊥) : 0 < Module.finrank k p := by
  haveI : Module.Finite k p := FiniteDimensional.finiteDimensional_submodule p
  haveI : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
  exact Module.finrank_pos








/-- A representation with finite vertex modules is related to the auxiliary product of a list whose members satisfy the displayed property. -/
theorem auxiliary_exists_list_of_property {k : Type uk} [Field k] {n : ℕ} [Quiver.{uh} (Fin n)]
    (V : AuxiliaryQuiverModuleData.{uk, 0, 0, uh} k (Fin n))
    [∀ v, Module.Finite k (V.obj v)] :
    ∃ L : List (AuxiliaryQuiverModuleData.{uk, 0, 0, uh} k (Fin n)),
      (∀ W ∈ L, W.AuxiliaryCondition) ∧ V.Related (auxiliaryListProduct L) := by

  suffices H : ∀ N, ∀ (V : AuxiliaryQuiverModuleData.{uk, 0, 0, uh} k (Fin n))
      [∀ v, Module.Finite k (V.obj v)],
      (∑ v, Module.finrank k (V.obj v)) = N →
      ∃ L : List (AuxiliaryQuiverModuleData.{uk, 0, 0, uh} k (Fin n)),
        (∀ W ∈ L, W.AuxiliaryCondition) ∧ V.Related (auxiliaryListProduct L) by
    exact H _ V rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro V _ hVN
    by_cases hInd : V.AuxiliaryCondition
    ·
      exact ⟨[V], by simpa using hInd, by
        simpa using auxiliaryProduct_zero_right V⟩
    ·
      rw [AuxiliaryCondition, not_and_or] at hInd
      rcases hInd with hzero | hsplit
      ·
        push Not at hzero
        exact ⟨[], by simp, auxiliaryRelation_zero_of_subsingleton V hzero⟩
      ·
        push Not at hsplit
        obtain ⟨W₁, W₂, hW₁, hW₂, hc, hne₁, hne₂⟩ := hsplit


        haveI hfd₁ : ∀ v, Module.Finite k ((auxiliarySubobject V W₁ hW₁).obj v) := fun v =>
          @FiniteDimensional.finiteDimensional_submodule k (V.obj v) _
            (RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)) (V.moduleInstance v)
            (inferInstanceAs (Module.Finite k (V.obj v))) (W₁ v)
        haveI hfd₂ : ∀ v, Module.Finite k ((auxiliarySubobject V W₂ hW₂).obj v) := fun v =>
          @FiniteDimensional.finiteDimensional_submodule k (V.obj v) _
            (RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)) (V.moduleInstance v)
            (inferInstanceAs (Module.Finite k (V.obj v))) (W₂ v)



        have hdim : ∀ v, Module.finrank k (W₁ v) + Module.finrank k (W₂ v)
            = Module.finrank k (V.obj v) := fun v =>
          @Submodule.finrank_add_eq_of_isCompl k (V.obj v) _
            (RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k)) (V.moduleInstance v)
            (inferInstanceAs (Module.Finite k (V.obj v))) (W₁ v) (W₂ v) (hc v)
        have hsum : (∑ v, Module.finrank k ((auxiliarySubobject V W₁ hW₁).obj v))
            + (∑ v, Module.finrank k ((auxiliarySubobject V W₂ hW₂).obj v))
            = ∑ v, Module.finrank k (V.obj v) := by
          simp only [auxiliarySubobject_obj]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun v _ => hdim v)

        obtain ⟨v₁, hv₁⟩ := hne₁
        obtain ⟨v₂, hv₂⟩ := hne₂
        have hpos₂ : 0 < ∑ v, Module.finrank k ((auxiliarySubobject V W₂ hW₂).obj v) := by
          refine Finset.sum_pos' (fun v _ => Nat.zero_le _) ⟨v₂, Finset.mem_univ _, ?_⟩
          change 0 < Module.finrank k (W₂ v₂)
          exact @finrank_pos_of_ne_bot k (V.obj v₂) _ (RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k))
            (V.moduleInstance v₂) (inferInstanceAs (Module.Finite k (V.obj v₂))) (W₂ v₂) hv₂
        have hpos₁ : 0 < ∑ v, Module.finrank k ((auxiliarySubobject V W₁ hW₁).obj v) := by
          refine Finset.sum_pos' (fun v _ => Nat.zero_le _) ⟨v₁, Finset.mem_univ _, ?_⟩
          change 0 < Module.finrank k (W₁ v₁)
          exact @finrank_pos_of_ne_bot k (V.obj v₁) _ (RepresentationTheory.QuiverRepresentationQuotientTransform.moduleAddCommGroupOfCommRing (k := k))
            (V.moduleInstance v₁) (inferInstanceAs (Module.Finite k (V.obj v₁))) (W₁ v₁) hv₁
        have hlt₁ : (∑ v, Module.finrank k ((auxiliarySubobject V W₁ hW₁).obj v)) < N := by
          rw [← hVN, ← hsum]; omega
        have hlt₂ : (∑ v, Module.finrank k ((auxiliarySubobject V W₂ hW₂).obj v)) < N := by
          rw [← hVN, ← hsum]; omega

        obtain ⟨L₁, hL₁ind, hL₁iso⟩ := IH _ hlt₁ (auxiliarySubobject V W₁ hW₁) rfl
        obtain ⟨L₂, hL₂ind, hL₂iso⟩ := IH _ hlt₂ (auxiliarySubobject V W₂ hW₂) rfl
        refine ⟨L₁ ++ L₂, ?_, ?_⟩
        · intro W hW
          rcases List.mem_append.mp hW with h | h
          · exact hL₁ind W h
          · exact hL₂ind W h
        · refine (auxiliaryProduct_subobjects_of_isCompl V W₁ W₂ hW₁ hW₂ hc).trans ?_
          exact (hL₁iso.prod hL₂iso).trans
            (auxiliaryListProduct_append L₁ L₂)

end Existence

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.RingTheory.ElementProperties
import RepresentationTheory.FGModuleCat.Projectivity
import RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Morita.Matrix













noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace RepresentationTheory

section FreeEnd

variable (B : Type u) [Ring B] (N : ℕ)

/-- The opposite ring of endomorphisms of a finite free module is equivalent to the corresponding square matrix ring. -/



noncomputable def ModuleCat.FiniteFreeRetractEndomorphisms.opModuleEndRingEquivMatrix :
    (Module.End B (Fin N → B))ᵐᵒᵖ ≃+* Matrix (Fin N) (Fin N) B where
  toFun f := LinearMap.toMatrixRight' f.unop
  invFun M := MulOpposite.op (LinearMap.toMatrixRight'.symm M)
  left_inv f := by
    apply MulOpposite.unop_injective
    exact LinearMap.toMatrixRight'.symm_apply_apply f.unop
  right_inv M := LinearMap.toMatrixRight'.apply_symm_apply M
  map_add' f g := by
    ext i j
    rfl
  map_mul' f g := by
    rw [MulOpposite.unop_mul]
    change LinearMap.toMatrixRight' (g.unop.comp f.unop) = _
    rw [LinearMap.toMatrixRight'_comp]

end FreeEnd

section FreeEndAlgebra

variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (N : ℕ)

/-- The opposite algebra of endomorphisms of a finite free module is equivalent to the corresponding square matrix algebra. -/

noncomputable def ModuleCat.FiniteFreeRetractEndomorphisms.opModuleEndAlgEquivMatrix :
    (Module.End B (Fin N → B))ᵐᵒᵖ ≃ₐ[k] Matrix (Fin N) (Fin N) B :=
  AlgEquiv.ofRingEquiv (f := ModuleCat.FiniteFreeRetractEndomorphisms.opModuleEndRingEquivMatrix B N) (fun c => by
    ext i j
    simp only [ModuleCat.FiniteFreeRetractEndomorphisms.opModuleEndRingEquivMatrix, LinearMap.toMatrixRight', Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst j
      simp [Algebra.smul_def]
    · simp [hij])

end FreeEndAlgebra

section FullProjection

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- Data exhibiting a finitely generated module as a retract of a finite free module. -/

structure ModuleCat.FiniteFreeRetractEndomorphisms.FiniteFreeRetractData (P : FGModuleCat.{u} B) where
  /-- The natural-number rank of the finite free module in the retract data. -/
  rank : ℕ
  /-- The rank specified by finite-free retract data is positive. -/
  rank_pos : 0 < rank
  /-- The morphism from the finite free module back to the given module. -/
  fromFiniteFree : FGModuleCat.of.{u} B (Fin rank → B) ⟶ P
  /-- The morphism from the given module to the finite free module specified by the retract data. -/
  toFiniteFree : P ⟶ FGModuleCat.of.{u} B (Fin rank → B)
  /-- The morphism to the finite free module followed by the return morphism is the identity. -/
  toFiniteFree_comp_fromFiniteFree : toFiniteFree ≫ fromFiniteFree = 𝟙 P

/-- An auxiliary finitely generated module associated with finite-free retract data. -/

abbrev ModuleCat.FiniteFreeRetractEndomorphisms.FiniteFreeRetractData.auxiliaryModule {P : FGModuleCat.{u} B}
    (D : ModuleCat.FiniteFreeRetractEndomorphisms.FiniteFreeRetractData P) : FGModuleCat.{u} B :=
  FGModuleCat.of.{u} B (Fin D.rank → B)

/-- Finite-free retract data obtained from a finitely generated module satisfying the designated property. -/

noncomputable def CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.finiteFreeRetractData
    (P : FGModuleCat.{u} B) (hP : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P) :
    ModuleCat.FiniteFreeRetractEndomorphisms.FiniteFreeRetractData P := by
  classical
  let hex : ∃ (n : ℕ) (p : (Fin n → B) →ₗ[B] P), Function.Surjective p :=
    Module.Finite.exists_fin' (R := B) (M := P)
  let n : ℕ := Classical.choose hex
  let p : (Fin n → B) →ₗ[B] P := Classical.choose (Classical.choose_spec hex)
  have hp : Function.Surjective p := Classical.choose_spec (Classical.choose_spec hex)
  let restrict : (Fin (n + 1) → B) →ₗ[B] (Fin n → B) :=
    LinearMap.funLeft B B Fin.castSucc
  let extend : (Fin n → B) →ₗ[B] (Fin (n + 1) → B) :=
    { toFun := fun x => Fin.lastCases 0 x
      map_add' := fun x y => by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun r x => by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp }
  have hre : restrict.comp extend = LinearMap.id := by
    ext x i
    simp [restrict, extend, LinearMap.funLeft_apply]
  have hrestrict : Function.Surjective restrict :=
    LinearMap.range_eq_top.mp (LinearMap.range_eq_top.mpr fun x =>
      ⟨extend x, LinearMap.congr_fun hre x⟩)
  let F : FGModuleCat.{u} B := FGModuleCat.of.{u} B (Fin (n + 1) → B)
  let p' : F ⟶ P := FGModuleCat.ofHom (p.comp restrict)
  have hpcomp : Function.Surjective (p.comp restrict) := hp.comp hrestrict
  have hp' : Epi p' := by
    apply RepresentationTheory.FGModuleCat.Projectivity.epi_of_toModuleCat_map_epi p'
    exact (ModuleCat.epi_iff_surjective _).mpr hpcomp
  letI : Epi p' := hp'
  letI : Projective P := hP.toProjective
  let i : P ⟶ F := Projective.factorThru (𝟙 P) p'
  exact
    { rank := n + 1
      rank_pos := Nat.succ_pos n
      fromFiniteFree := p'
      toFiniteFree := i
      toFiniteFree_comp_fromFiniteFree := Projective.factorThru_comp (𝟙 P) p' }

variable (P : FGModuleCat.{u} B) (hP : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P)

/-- An auxiliary element of the opposite endomorphism ring obtained from a module satisfying the designated property. -/


noncomputable def CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.auxiliaryOppositeEndomorphism :
    (Module.End B (hP.finiteFreeRetractData P).auxiliaryModule)ᵐᵒᵖ :=
  MulOpposite.op ((hP.finiteFreeRetractData P).toFiniteFree.hom.hom.comp
    (hP.finiteFreeRetractData P).fromFiniteFree.hom.hom)

/-- The auxiliary opposite endomorphism satisfies the designated predicate. -/

theorem CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.auxiliaryOppositeEndomorphism_property :
    RepresentationTheory.RingTheory.ElementProperties.ringElementCondition (hP.auxiliaryOppositeEndomorphism P) := by
  classical
  let D := hP.finiteFreeRetractData P
  let e : (Module.End B D.auxiliaryModule)ᵐᵒᵖ :=
    MulOpposite.op (D.toFiniteFree.hom.hom.comp D.fromFiniteFree.hom.hom)
  have hip (x : P) : D.fromFiniteFree.hom.hom (D.toFiniteFree.hom.hom x) = x := by
    have hx := congrArg (fun f : P ⟶ P => f.hom.hom x) D.toFiniteFree_comp_fromFiniteFree
    simpa using hx
  have he : IsIdempotentElem e := by
    rw [isIdempotentElem_iff]
    apply MulOpposite.unop_injective
    apply LinearMap.ext
    intro x
    change D.toFiniteFree.hom.hom (D.fromFiniteFree.hom.hom
      (D.toFiniteFree.hom.hom (D.fromFiniteFree.hom.hom x))) =
        D.toFiniteFree.hom.hom (D.fromFiniteFree.hom.hom x)
    rw [hip]
  refine ⟨he, ?_⟩
  rw [eq_top_iff]
  intro x _
  suffices h_one : (1 : (Module.End B D.auxiliaryModule)ᵐᵒᵖ) ∈
      Ideal.span {a * e * b |
        (a : (Module.End B D.auxiliaryModule)ᵐᵒᵖ) (b : (Module.End B D.auxiliaryModule)ᵐᵒᵖ)} by
    rw [← mul_one x]
    exact Ideal.mul_mem_left _ x h_one
  obtain ⟨m, hm, q, hq⟩ := hP.exists_epi D.auxiliaryModule
  letI : HasBiproduct (fun _ : Fin m => P) := hm
  letI : Epi q := hq
  haveI : Projective D.auxiliaryModule := by
    apply RepresentationTheory.FGModuleCat.Projectivity.projective_of_toModuleCat_projective
    exact ModuleCat.projective_of_free (Pi.basisFun B (Fin D.rank))
  let j : D.auxiliaryModule ⟶ ⨁ fun _ : Fin m => P := Projective.factorThru (𝟙 D.auxiliaryModule) q
  have hjq : j ≫ q = 𝟙 D.auxiliaryModule := Projective.factorThru_comp (𝟙 D.auxiliaryModule) q
  let a (t : Fin m) : Module.End B D.auxiliaryModule :=
    D.toFiniteFree.hom.hom.comp ((biproduct.π (fun _ : Fin m => P) t).hom.hom.comp j.hom.hom)
  let b (t : Fin m) : Module.End B D.auxiliaryModule :=
    q.hom.hom.comp ((biproduct.ι (fun _ : Fin m => P) t).hom.hom.comp D.fromFiniteFree.hom.hom)
  have hterm (t : Fin m) :
      MulOpposite.op (a t) * e * MulOpposite.op (b t)
        ∈ Ideal.span {a * e * b |
          (a : (Module.End B D.auxiliaryModule)ᵐᵒᵖ) (b : (Module.End B D.auxiliaryModule)ᵐᵒᵖ)} := by
    apply Ideal.subset_span
    exact ⟨_, _, rfl⟩
  have hsum :
      (1 : (Module.End B D.auxiliaryModule)ᵐᵒᵖ) =
        ∑ t : Fin m,
          MulOpposite.op (a t) * e * MulOpposite.op (b t) := by
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_one]
    have hunopSum (s : Finset (Fin m)) :
        (∑ t ∈ s, MulOpposite.op (a t) * e * MulOpposite.op (b t)).unop =
          ∑ t ∈ s, (MulOpposite.op (a t) * e * MulOpposite.op (b t)).unop := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert t s hts ih => simp [hts, ih]
    rw [hunopSum Finset.univ]
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op]
    simp only [a, b, e]
    apply LinearMap.ext
    intro x
    simp only [Module.End.one_apply, Module.End.mul_apply, LinearMap.comp_apply,
      LinearMap.sum_apply]
    simp only [MulOpposite.unop_op, LinearMap.comp_apply]
    simp only [hip]
    have hcat :
        (∑ t : Fin m, j ≫ biproduct.π (fun _ : Fin m => P) t ≫
          biproduct.ι (fun _ : Fin m => P) t ≫ q) = 𝟙 D.auxiliaryModule := by
      calc
        _ = j ≫ (∑ t : Fin m, biproduct.π (fun _ : Fin m => P) t ≫
              biproduct.ι (fun _ : Fin m => P) t) ≫ q := by
            simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        _ = j ≫ q := by rw [biproduct.total, Category.id_comp]
        _ = 𝟙 D.auxiliaryModule := hjq
    let homToEnd : (D.auxiliaryModule ⟶ D.auxiliaryModule) →+ Module.End B D.auxiliaryModule :=
      { toFun := fun f => f.hom.hom
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have homToEnd_apply (f : D.auxiliaryModule ⟶ D.auxiliaryModule) : homToEnd f = f.hom.hom := rfl
    have hend := congrArg (fun f : D.auxiliaryModule ⟶ D.auxiliaryModule => homToEnd f) hcat
    have hend' :
        (∑ t : Fin m, homToEnd (j ≫ biproduct.π (fun _ : Fin m => P) t ≫
          biproduct.ι (fun _ : Fin m => P) t ≫ q)) = homToEnd (𝟙 D.auxiliaryModule) := by
      rw [← map_sum]
      exact hend
    have hx := congrArg (fun f : Module.End B D.auxiliaryModule => f x) hend'
    simp only [homToEnd_apply] at hx
    simpa only [LinearMap.sum_apply, FGModuleCat.hom_hom_comp,
      FGModuleCat.hom_hom_id, Module.End.one_apply, LinearMap.comp_apply,
      LinearMap.id_apply] using hx.symm
  rw [hsum]
  exact Submodule.sum_mem _ fun t _ => hterm t

/-- A ring equivalence from the designated subring associated with an auxiliary endomorphism to the opposite endomorphism ring of the module. -/


noncomputable def CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.auxiliarySubringEquivEnd :
    let e := hP.auxiliaryOppositeEndomorphism P
    let he := (hP.auxiliaryOppositeEndomorphism_property P).1
    letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he
    RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e ≃+* (Module.End B P)ᵐᵒᵖ := by
  let D := hP.finiteFreeRetractData P
  let e : (Module.End B D.auxiliaryModule)ᵐᵒᵖ :=
    MulOpposite.op (D.toFiniteFree.hom.hom.comp D.fromFiniteFree.hom.hom)
  let he : IsIdempotentElem e := (hP.auxiliaryOppositeEndomorphism_property P).1
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he
  change RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e ≃+* (Module.End B P)ᵐᵒᵖ
  have hip (x : P) : D.fromFiniteFree.hom.hom (D.toFiniteFree.hom.hom x) = x := by
    have hx := congrArg (fun f : P ⟶ P => f.hom.hom x) D.toFiniteFree_comp_fromFiniteFree
    simpa using hx
  have hfix (f : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (x : D.auxiliaryModule) :
      D.toFiniteFree.hom.hom (D.fromFiniteFree.hom.hom (f.val.unop x)) = f.val.unop x := by
    have hf := RepresentationTheory.RingTheory.Idempotent.right_mul_eq_of_mem_sandwichSubmodule he f.prop
    have hx := LinearMap.congr_fun (congrArg MulOpposite.unop hf) x
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, Module.End.mul_apply,
      LinearMap.comp_apply, e, CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.auxiliaryOppositeEndomorphism] using hx
  exact
    { toFun := fun f => MulOpposite.op
        (D.fromFiniteFree.hom.hom.comp (f.val.unop.comp D.toFiniteFree.hom.hom))
      invFun := fun g =>
        ⟨MulOpposite.op (D.toFiniteFree.hom.hom.comp (g.unop.comp D.fromFiniteFree.hom.hom)), by
          change MulOpposite.op (D.toFiniteFree.hom.hom.comp (g.unop.comp D.fromFiniteFree.hom.hom)) ∈
            RepresentationTheory.RingTheory.Idempotent.sandwichSubmodule (k := k) e
          rw [RepresentationTheory.RingTheory.Idempotent.mem_sandwichSubmodule_iff]
          refine ⟨MulOpposite.op
            (D.toFiniteFree.hom.hom.comp (g.unop.comp D.fromFiniteFree.hom.hom)), ?_⟩
          apply MulOpposite.unop_injective
          apply LinearMap.ext
          intro x
          change D.toFiniteFree.hom.hom (D.fromFiniteFree.hom.hom
            (D.toFiniteFree.hom.hom (g.unop (D.fromFiniteFree.hom.hom
              (D.toFiniteFree.hom.hom (D.fromFiniteFree.hom.hom x)))))) =
                D.toFiniteFree.hom.hom (g.unop (D.fromFiniteFree.hom.hom x))
          simp only [hip]⟩
      left_inv := fun f => by
        apply Subtype.ext
        apply MulOpposite.unop_injective
        simp only [MulOpposite.unop_op]
        have hf : f.val ∈ RepresentationTheory.RingTheory.Idempotent.sandwichSubmodule (k := k) e := f.prop
        have hsupport : e * f.val * e = f.val := by
          rw [RepresentationTheory.RingTheory.Idempotent.left_mul_eq_of_mem_sandwichSubmodule he hf, RepresentationTheory.RingTheory.Idempotent.right_mul_eq_of_mem_sandwichSubmodule he hf]
        apply LinearMap.ext
        intro x
        have hx := LinearMap.congr_fun (congrArg MulOpposite.unop hsupport) x
        simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, Module.End.mul_apply,
          LinearMap.comp_apply, e, CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.auxiliaryOppositeEndomorphism] using hx
      right_inv := fun g => by
        apply MulOpposite.unop_injective
        apply LinearMap.ext
        intro x
        simp only [MulOpposite.unop_op, LinearMap.comp_apply, hip]
      map_add' := fun f g => by
        apply MulOpposite.unop_injective
        have hadd : (f + g).val = f.val + g.val := rfl
        apply LinearMap.ext
        intro x
        simp only [hadd, MulOpposite.unop_add, MulOpposite.unop_op, LinearMap.comp_apply,
          LinearMap.add_apply]
        rw [map_add]
      map_mul' := fun f g => by
        apply MulOpposite.unop_injective
        have hmul : (f * g).val = f.val * g.val := rfl
        apply LinearMap.ext
        intro x
        simp only [hmul, MulOpposite.unop_mul, MulOpposite.unop_op, Module.End.mul_apply,
          LinearMap.comp_apply]
        rw [hfix] }

/-- The categorical endomorphism ring of a finitely generated module is equivalent to the endomorphism ring of its carrier. -/


noncomputable def ModuleCat.FiniteFreeRetractEndomorphisms.endRingEquivModuleEnd :
    End P ≃+* Module.End B P where
  toFun f := f.hom.hom
  invFun f := FGModuleCat.ofHom f
  left_inv f := by apply FGModuleCat.hom_ext; rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The categorical endomorphism algebra of a finitely generated module is equivalent to the algebra of endomorphisms of its carrier. -/

noncomputable def ModuleCat.FiniteFreeRetractEndomorphisms.endAlgEquivModuleEnd :
    End P ≃ₐ[k] Module.End B P :=
  AlgEquiv.ofRingEquiv (f := ModuleCat.FiniteFreeRetractEndomorphisms.endRingEquivModuleEnd P) (fun c => by
    apply LinearMap.ext
    intro x
    rfl)

/-- An algebra equivalence from the designated subalgebra associated with an auxiliary endomorphism to the opposite endomorphism algebra of the module. -/

noncomputable def CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.auxiliarySubalgebraEquivEnd :
    let e := hP.auxiliaryOppositeEndomorphism P
    let he := (hP.auxiliaryOppositeEndomorphism_property P).1
    letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he
    letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he
    RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e ≃ₐ[k] (Module.End B P)ᵐᵒᵖ := by
  let D := hP.finiteFreeRetractData P
  let e : (Module.End B D.auxiliaryModule)ᵐᵒᵖ := hP.auxiliaryOppositeEndomorphism P
  let he : IsIdempotentElem e := (hP.auxiliaryOppositeEndomorphism_property P).1
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he
  exact AlgEquiv.ofRingEquiv (f := hP.auxiliarySubringEquivEnd P) (fun c => by
    have hip (x : P) : D.fromFiniteFree.hom.hom (D.toFiniteFree.hom.hom x) = x := by
      have hx := congrArg (fun f : P ⟶ P => f.hom.hom x) D.toFiniteFree_comp_fromFiniteFree
      simpa using hx
    have h_one_val : (1 : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e).val = e := rfl
    have h_alg :
        (algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) c).val =
          algebraMap k (Module.End B D.auxiliaryModule)ᵐᵒᵖ c * e := by
      change (c • (1 : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e)).val = _
      rw [show (c • (1 : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e)).val =
        c • (1 : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e).val from rfl, h_one_val, Algebra.smul_def]
    apply MulOpposite.unop_injective
    apply LinearMap.ext
    intro x
    change D.fromFiniteFree.hom.hom
      ((algebraMap k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) c).val.unop (D.toFiniteFree.hom.hom x)) = c • x
    rw [h_alg]
    change D.fromFiniteFree.hom.hom (D.toFiniteFree.hom.hom
      (D.fromFiniteFree.hom.hom (c • D.toFiniteFree.hom.hom x))) = c • x
    rw [LinearMap.map_smul_of_tower, hip]
    exact congrArg (fun y : P => c • y) (hip x))

end FullProjection

section ProgeneratorMorita

/-- A module satisfying the designated property yields an equivalence with modules over its opposite endomorphism ring. -/

theorem CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.exists_moduleCatEquivalenceEnd
    {k B : Type u} [Field k] [Ring B] [Algebra k B]
    (P : FGModuleCat.{u} B) (hP : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P) :
    Nonempty (ModuleCat.{u} B ≌ ModuleCat.{u} (End P)ᵐᵒᵖ) := by
  classical
  let D := hP.finiteFreeRetractData P
  let e : (Module.End B D.auxiliaryModule)ᵐᵒᵖ := hP.auxiliaryOppositeEndomorphism P
  let he : RepresentationTheory.RingTheory.ElementProperties.ringElementCondition e := hP.auxiliaryOppositeEndomorphism_property P
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1
  let i : Fin D.rank := ⟨0, D.rank_pos⟩
  let EMatrix : ModuleCat.{u} B ≌ ModuleCat.{u} (Matrix (Fin D.rank) (Fin D.rank) B) :=
    ModuleCat.matrixEquivalence B i
  let EFree : ModuleCat.{u} (Matrix (Fin D.rank) (Fin D.rank) B) ≌
      ModuleCat.{u} (Module.End B D.auxiliaryModule)ᵐᵒᵖ :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ModuleCat.FiniteFreeRetractEndomorphisms.opModuleEndRingEquivMatrix B D.rank)
  obtain ⟨ECorner⟩ := RepresentationTheory.RingTheory.ElementProperties.membershipSubtype_has_condition_of_ringElementCondition (k := k) he
  let cornerEndEquiv : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e ≃+* (End P)ᵐᵒᵖ :=
    (hP.auxiliarySubringEquivEnd P).trans (RingEquiv.op (ModuleCat.FiniteFreeRetractEndomorphisms.endRingEquivModuleEnd P)).symm
  let EEnd : ModuleCat.{u} (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) ≌ ModuleCat.{u} (End P)ᵐᵒᵖ :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv cornerEndEquiv).symm
  exact ⟨EMatrix.trans (EFree.trans (ECorner.trans EEnd))⟩

/-- A finite algebra and a module satisfying the designated property yield the auxiliary algebra relation with the opposite endomorphism algebra. -/

theorem CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.toAuxiliaryAlgebraRelation
    {k B : Type u} [Field k] [Ring B] [Algebra k B] [Module.Finite k B]
    (P : FGModuleCat.{u} B) (hP : RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses P) :
    RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k B (End P)ᵐᵒᵖ := by
  classical
  let D := hP.finiteFreeRetractData P
  let e : (Module.End B D.auxiliaryModule)ᵐᵒᵖ := hP.auxiliaryOppositeEndomorphism P
  let he : RepresentationTheory.RingTheory.ElementProperties.ringElementCondition e := hP.auxiliaryOppositeEndomorphism_property P
  letI : Ring (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.ring he.1
  letI : Algebra k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.Idempotent.submodule.algebra he.1
  let i : Fin D.rank := ⟨0, D.rank_pos⟩
  let matrixMorita := moritaEquivalenceMatrix B k i
  have hMatrix : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k B (Matrix (Fin D.rank) (Fin D.rank) B) :=
    ⟨matrixMorita.eqv, matrixMorita.linear⟩
  let freeMorita := MoritaEquivalence.symm k
    (MoritaEquivalence.ofAlgEquiv (ModuleCat.FiniteFreeRetractEndomorphisms.opModuleEndAlgEquivMatrix k B D.rank))
  have hFree : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k (Matrix (Fin D.rank) (Fin D.rank) B)
      (Module.End B D.auxiliaryModule)ᵐᵒᵖ := ⟨freeMorita.eqv, freeMorita.linear⟩
  haveI : Module.Finite k (Module.End B D.auxiliaryModule)ᵐᵒᵖ := inferInstance
  have hCorner : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k (Module.End B D.auxiliaryModule)ᵐᵒᵖ
      (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) := RepresentationTheory.RingTheory.ElementProperties.membershipSubtype_has_indexed_condition_of_ringElementCondition he
  let cornerEndAlgEquiv : RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e ≃ₐ[k] (End P)ᵐᵒᵖ :=
    (hP.auxiliarySubalgebraEquivEnd P).trans
      (AlgEquiv.op (ModuleCat.FiniteFreeRetractEndomorphisms.endAlgEquivModuleEnd P)).symm
  let endMorita := MoritaEquivalence.ofAlgEquiv cornerEndAlgEquiv
  have hEnd : RepresentationTheory.RingAuxiliary.AlgebraAuxiliary k (RepresentationTheory.RingTheory.Idempotent.submodule (k := k) e) (End P)ᵐᵒᵖ :=
    ⟨endMorita.eqv, endMorita.linear⟩
  exact ((hMatrix.trans hFree).trans hCorner).trans hEnd

end ProgeneratorMorita

end RepresentationTheory

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.Auxiliary.statement005220 := _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.auxiliarySubalgebraEquivEnd

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.Auxiliary.statement005222 := _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.auxiliarySubringEquivEnd

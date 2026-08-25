import EtingofRepresentationTheory.Infrastructure.BasicAlgebraExistence
import EtingofRepresentationTheory.Infrastructure.FGModuleCatEnoughProjectives
import EtingofRepresentationTheory.Chapter9.Definition9_6_2
import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Morita.Matrix

/-!
# Morita equivalence from a finite progenerator

This file proves the classical all-modules Morita theorem in the concrete form needed by
Definition 9.7.1.  A finite progenerator `P` over a finite-dimensional algebra `B` is a direct
summand of a finite free module `F`.  The corresponding idempotent in `End(F)ᵒᵖ` is full because
`P` generates `F`; its corner is `End(P)ᵒᵖ`.  Matrix Morita equivalence and the existing
full-idempotent corner equivalence then give

`ModuleCat B ≌ ModuleCat (End P)ᵒᵖ`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace Etingof

section FreeEnd

variable (B : Type u) [Ring B] (N : ℕ)

/-- The opposite endomorphism ring of the finite-rank free left module is the matrix ring.
For a noncommutative coefficient ring, left-linear endomorphisms act by matrices on the right,
which is why both the opposite and `toMatrixRight'` occur. -/
noncomputable def freeEndOpRingEquivMatrix :
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

/-- The finite-free endomorphism/matrix identification respects the central `k`-action. -/
noncomputable def freeEndOpAlgEquivMatrix :
    (Module.End B (Fin N → B))ᵐᵒᵖ ≃ₐ[k] Matrix (Fin N) (Fin N) B :=
  AlgEquiv.ofRingEquiv (f := freeEndOpRingEquivMatrix B N) (fun c => by
    ext i j
    simp only [freeEndOpRingEquivMatrix, LinearMap.toMatrixRight', Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst j
      simp [Algebra.smul_def]
    · simp [hij])

end FreeEndAlgebra

section FullProjection

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- A split finite-free presentation of a finite progenerator. -/
structure ProgeneratorFreePresentation (P : FGModuleCat.{u} B) where
  rank : ℕ
  rank_pos : 0 < rank
  proj : FGModuleCat.of.{u} B (Fin rank → B) ⟶ P
  incl : P ⟶ FGModuleCat.of.{u} B (Fin rank → B)
  incl_proj : incl ≫ proj = 𝟙 P

/-- The finite free object underlying a presentation. -/
abbrev ProgeneratorFreePresentation.free {P : FGModuleCat.{u} B}
    (D : ProgeneratorFreePresentation P) : FGModuleCat.{u} B :=
  FGModuleCat.of.{u} B (Fin D.rank → B)

/-- A finite progenerator is a summand of a nonzero finite-rank free module. -/
noncomputable def IsProgenerator.freePresentation
    (P : FGModuleCat.{u} B) (hP : IsProgenerator P) :
    ProgeneratorFreePresentation P := by
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
    apply FGModuleCat.epi_of_forget₂_epi p'
    exact (ModuleCat.epi_iff_surjective _).mpr hpcomp
  letI : Epi p' := hp'
  letI : Projective P := hP.toProjective
  let i : P ⟶ F := Projective.factorThru (𝟙 P) p'
  exact
    { rank := n + 1
      rank_pos := Nat.succ_pos n
      proj := p'
      incl := i
      incl_proj := Projective.factorThru_comp (𝟙 P) p' }

variable (P : FGModuleCat.{u} B) (hP : IsProgenerator P)

/-- The projection onto `P` inside the chosen finite free presentation, viewed in the opposite
endomorphism ring. -/
noncomputable def IsProgenerator.freeIdempotent :
    (Module.End B (hP.freePresentation P).free)ᵐᵒᵖ :=
  MulOpposite.op ((hP.freePresentation P).incl.hom.hom.comp
    (hP.freePresentation P).proj.hom.hom)

/-- The finite-free projection associated to a progenerator is a full idempotent. -/
theorem IsProgenerator.freeIdempotent_isFull :
    IsFullIdempotent (hP.freeIdempotent P) := by
  classical
  let D := hP.freePresentation P
  let e : (Module.End B D.free)ᵐᵒᵖ :=
    MulOpposite.op (D.incl.hom.hom.comp D.proj.hom.hom)
  have hip (x : P) : D.proj.hom.hom (D.incl.hom.hom x) = x := by
    have hx := congrArg (fun f : P ⟶ P => f.hom.hom x) D.incl_proj
    simpa using hx
  have he : IsIdempotentElem e := by
    rw [isIdempotentElem_iff]
    apply MulOpposite.unop_injective
    apply LinearMap.ext
    intro x
    change D.incl.hom.hom (D.proj.hom.hom
      (D.incl.hom.hom (D.proj.hom.hom x))) =
        D.incl.hom.hom (D.proj.hom.hom x)
    rw [hip]
  refine ⟨he, ?_⟩
  rw [eq_top_iff]
  intro x _
  suffices h_one : (1 : (Module.End B D.free)ᵐᵒᵖ) ∈
      Ideal.span {a * e * b |
        (a : (Module.End B D.free)ᵐᵒᵖ) (b : (Module.End B D.free)ᵐᵒᵖ)} by
    rw [← mul_one x]
    exact Ideal.mul_mem_left _ x h_one
  obtain ⟨m, hm, q, hq⟩ := hP.epiFromBiproduct D.free
  letI : HasBiproduct (fun _ : Fin m => P) := hm
  letI : Epi q := hq
  haveI : Projective D.free := by
    apply FGModuleCat.projective_of_forget₂_projective
    exact ModuleCat.projective_of_free (Pi.basisFun B (Fin D.rank))
  let j : D.free ⟶ ⨁ fun _ : Fin m => P := Projective.factorThru (𝟙 D.free) q
  have hjq : j ≫ q = 𝟙 D.free := Projective.factorThru_comp (𝟙 D.free) q
  let a (t : Fin m) : Module.End B D.free :=
    D.incl.hom.hom.comp ((biproduct.π (fun _ : Fin m => P) t).hom.hom.comp j.hom.hom)
  let b (t : Fin m) : Module.End B D.free :=
    q.hom.hom.comp ((biproduct.ι (fun _ : Fin m => P) t).hom.hom.comp D.proj.hom.hom)
  have hterm (t : Fin m) :
      MulOpposite.op (a t) * e * MulOpposite.op (b t)
        ∈ Ideal.span {a * e * b |
          (a : (Module.End B D.free)ᵐᵒᵖ) (b : (Module.End B D.free)ᵐᵒᵖ)} := by
    apply Ideal.subset_span
    exact ⟨_, _, rfl⟩
  have hsum :
      (1 : (Module.End B D.free)ᵐᵒᵖ) =
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
          biproduct.ι (fun _ : Fin m => P) t ≫ q) = 𝟙 D.free := by
      calc
        _ = j ≫ (∑ t : Fin m, biproduct.π (fun _ : Fin m => P) t ≫
              biproduct.ι (fun _ : Fin m => P) t) ≫ q := by
            simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        _ = j ≫ q := by rw [biproduct.total, Category.id_comp]
        _ = 𝟙 D.free := hjq
    let homToEnd : (D.free ⟶ D.free) →+ Module.End B D.free :=
      { toFun := fun f => f.hom.hom
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have homToEnd_apply (f : D.free ⟶ D.free) : homToEnd f = f.hom.hom := rfl
    have hend := congrArg (fun f : D.free ⟶ D.free => homToEnd f) hcat
    have hend' :
        (∑ t : Fin m, homToEnd (j ≫ biproduct.π (fun _ : Fin m => P) t ≫
          biproduct.ι (fun _ : Fin m => P) t ≫ q)) = homToEnd (𝟙 D.free) := by
      rw [← map_sum]
      exact hend
    have hx := congrArg (fun f : Module.End B D.free => f x) hend'
    simp only [homToEnd_apply] at hx
    simpa only [LinearMap.sum_apply, FGModuleCat.hom_hom_comp,
      FGModuleCat.hom_hom_id, Module.End.one_apply, LinearMap.comp_apply,
      LinearMap.id_apply] using hx.symm
  rw [hsum]
  exact Submodule.sum_mem _ fun t _ => hterm t

/-- The corner of the finite-free projection is the opposite endomorphism ring of the
progenerator. -/
noncomputable def IsProgenerator.freeCornerRingEquivEndOp :
    let e := hP.freeIdempotent P
    let he := (hP.freeIdempotent_isFull P).1
    letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he
    CornerRing (k := k) e ≃+* (Module.End B P)ᵐᵒᵖ := by
  let D := hP.freePresentation P
  let e : (Module.End B D.free)ᵐᵒᵖ :=
    MulOpposite.op (D.incl.hom.hom.comp D.proj.hom.hom)
  let he : IsIdempotentElem e := (hP.freeIdempotent_isFull P).1
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he
  change CornerRing (k := k) e ≃+* (Module.End B P)ᵐᵒᵖ
  have hip (x : P) : D.proj.hom.hom (D.incl.hom.hom x) = x := by
    have hx := congrArg (fun f : P ⟶ P => f.hom.hom x) D.incl_proj
    simpa using hx
  have hfix (f : CornerRing (k := k) e) (x : D.free) :
      D.incl.hom.hom (D.proj.hom.hom (f.val.unop x)) = f.val.unop x := by
    have hf := cornerSubmodule_right_mul he f.prop
    have hx := LinearMap.congr_fun (congrArg MulOpposite.unop hf) x
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, Module.End.mul_apply,
      LinearMap.comp_apply, e, IsProgenerator.freeIdempotent] using hx
  exact
    { toFun := fun f => MulOpposite.op
        (D.proj.hom.hom.comp (f.val.unop.comp D.incl.hom.hom))
      invFun := fun g =>
        ⟨MulOpposite.op (D.incl.hom.hom.comp (g.unop.comp D.proj.hom.hom)), by
          change MulOpposite.op (D.incl.hom.hom.comp (g.unop.comp D.proj.hom.hom)) ∈
            cornerSubmodule (k := k) e
          rw [mem_cornerSubmodule_iff]
          refine ⟨MulOpposite.op
            (D.incl.hom.hom.comp (g.unop.comp D.proj.hom.hom)), ?_⟩
          apply MulOpposite.unop_injective
          apply LinearMap.ext
          intro x
          change D.incl.hom.hom (D.proj.hom.hom
            (D.incl.hom.hom (g.unop (D.proj.hom.hom
              (D.incl.hom.hom (D.proj.hom.hom x)))))) =
                D.incl.hom.hom (g.unop (D.proj.hom.hom x))
          simp only [hip]⟩
      left_inv := fun f => by
        apply Subtype.ext
        apply MulOpposite.unop_injective
        simp only [MulOpposite.unop_op]
        have hf : f.val ∈ cornerSubmodule (k := k) e := f.prop
        have hsupport : e * f.val * e = f.val := by
          rw [cornerSubmodule_left_mul he hf, cornerSubmodule_right_mul he hf]
        apply LinearMap.ext
        intro x
        have hx := LinearMap.congr_fun (congrArg MulOpposite.unop hsupport) x
        simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, Module.End.mul_apply,
          LinearMap.comp_apply, e, IsProgenerator.freeIdempotent] using hx
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

/-- Categorical endomorphisms of a finitely generated module are its ordinary linear
endomorphisms. -/
noncomputable def fgModuleCatEndRingEquiv :
    End P ≃+* Module.End B P where
  toFun f := f.hom.hom
  invFun f := FGModuleCat.ofHom f
  left_inv f := by apply FGModuleCat.hom_ext; rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The categorical/linear endomorphism identification is `k`-linear. -/
noncomputable def fgModuleCatEndAlgEquiv :
    End P ≃ₐ[k] Module.End B P :=
  AlgEquiv.ofRingEquiv (f := fgModuleCatEndRingEquiv P) (fun c => by
    apply LinearMap.ext
    intro x
    rfl)

/-- The corner/endomorphism identification respects the central `k`-action. -/
noncomputable def IsProgenerator.freeCornerRingAlgEquivEndOp :
    let e := hP.freeIdempotent P
    let he := (hP.freeIdempotent_isFull P).1
    letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he
    letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he
    CornerRing (k := k) e ≃ₐ[k] (Module.End B P)ᵐᵒᵖ := by
  let D := hP.freePresentation P
  let e : (Module.End B D.free)ᵐᵒᵖ := hP.freeIdempotent P
  let he : IsIdempotentElem e := (hP.freeIdempotent_isFull P).1
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he
  letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he
  exact AlgEquiv.ofRingEquiv (f := hP.freeCornerRingEquivEndOp P) (fun c => by
    have hip (x : P) : D.proj.hom.hom (D.incl.hom.hom x) = x := by
      have hx := congrArg (fun f : P ⟶ P => f.hom.hom x) D.incl_proj
      simpa using hx
    have h_one_val : (1 : CornerRing (k := k) e).val = e := rfl
    have h_alg :
        (algebraMap k (CornerRing (k := k) e) c).val =
          algebraMap k (Module.End B D.free)ᵐᵒᵖ c * e := by
      change (c • (1 : CornerRing (k := k) e)).val = _
      rw [show (c • (1 : CornerRing (k := k) e)).val =
        c • (1 : CornerRing (k := k) e).val from rfl, h_one_val, Algebra.smul_def]
    apply MulOpposite.unop_injective
    apply LinearMap.ext
    intro x
    change D.proj.hom.hom
      ((algebraMap k (CornerRing (k := k) e) c).val.unop (D.incl.hom.hom x)) = c • x
    rw [h_alg]
    change D.proj.hom.hom (D.incl.hom.hom
      (D.proj.hom.hom (c • D.incl.hom.hom x))) = c • x
    rw [LinearMap.map_smul_of_tower, hip]
    exact congrArg (fun y : P => c • y) (hip x))

end FullProjection

section ProgeneratorMorita

/-- The all-modules Morita theorem for a finite progenerator. -/
theorem IsProgenerator.moduleCatEquivEndOp
    {k B : Type u} [Field k] [Ring B] [Algebra k B]
    (P : FGModuleCat.{u} B) (hP : IsProgenerator P) :
    Nonempty (ModuleCat.{u} B ≌ ModuleCat.{u} (End P)ᵐᵒᵖ) := by
  classical
  let D := hP.freePresentation P
  let e : (Module.End B D.free)ᵐᵒᵖ := hP.freeIdempotent P
  let he : IsFullIdempotent e := hP.freeIdempotent_isFull P
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he.1
  let i : Fin D.rank := ⟨0, D.rank_pos⟩
  let EMatrix : ModuleCat.{u} B ≌ ModuleCat.{u} (Matrix (Fin D.rank) (Fin D.rank) B) :=
    ModuleCat.matrixEquivalence B i
  let EFree : ModuleCat.{u} (Matrix (Fin D.rank) (Fin D.rank) B) ≌
      ModuleCat.{u} (Module.End B D.free)ᵐᵒᵖ :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (freeEndOpRingEquivMatrix B D.rank)
  obtain ⟨ECorner⟩ := morita_equiv_of_full_idempotent (k := k) he
  let cornerEndEquiv : CornerRing (k := k) e ≃+* (End P)ᵐᵒᵖ :=
    (hP.freeCornerRingEquivEndOp P).trans (RingEquiv.op (fgModuleCatEndRingEquiv P)).symm
  let EEnd : ModuleCat.{u} (CornerRing (k := k) e) ≌ ModuleCat.{u} (End P)ᵐᵒᵖ :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv cornerEndEquiv).symm
  exact ⟨EMatrix.trans (EFree.trans (ECorner.trans EEnd))⟩

/-- The progenerator Morita equivalence is `k`-linear for a module-finite `k`-algebra. -/
theorem IsProgenerator.kLinearMoritaEquivalentEndOp
    {k B : Type u} [Field k] [Ring B] [Algebra k B] [Module.Finite k B]
    (P : FGModuleCat.{u} B) (hP : IsProgenerator P) :
    KLinearMoritaEquivalent k B (End P)ᵐᵒᵖ := by
  classical
  let D := hP.freePresentation P
  let e : (Module.End B D.free)ᵐᵒᵖ := hP.freeIdempotent P
  let he : IsFullIdempotent e := hP.freeIdempotent_isFull P
  letI : Ring (CornerRing (k := k) e) := CornerRing.instRing he.1
  letI : Algebra k (CornerRing (k := k) e) := CornerRing.instAlgebra he.1
  let i : Fin D.rank := ⟨0, D.rank_pos⟩
  let matrixMorita := moritaEquivalenceMatrix B k i
  have hMatrix : KLinearMoritaEquivalent k B (Matrix (Fin D.rank) (Fin D.rank) B) :=
    ⟨matrixMorita.eqv, matrixMorita.linear⟩
  let freeMorita := MoritaEquivalence.symm k
    (MoritaEquivalence.ofAlgEquiv (freeEndOpAlgEquivMatrix k B D.rank))
  have hFree : KLinearMoritaEquivalent k (Matrix (Fin D.rank) (Fin D.rank) B)
      (Module.End B D.free)ᵐᵒᵖ := ⟨freeMorita.eqv, freeMorita.linear⟩
  haveI : Module.Finite k (Module.End B D.free)ᵐᵒᵖ := inferInstance
  have hCorner : KLinearMoritaEquivalent k (Module.End B D.free)ᵐᵒᵖ
      (CornerRing (k := k) e) := klinear_morita_equiv_of_full_idempotent he
  let cornerEndAlgEquiv : CornerRing (k := k) e ≃ₐ[k] (End P)ᵐᵒᵖ :=
    (hP.freeCornerRingAlgEquivEndOp P).trans
      (AlgEquiv.op (fgModuleCatEndAlgEquiv P)).symm
  let endMorita := MoritaEquivalence.ofAlgEquiv cornerEndAlgEquiv
  have hEnd : KLinearMoritaEquivalent k (CornerRing (k := k) e) (End P)ᵐᵒᵖ :=
    ⟨endMorita.eqv, endMorita.linear⟩
  exact ((hMatrix.trans' hFree).trans' hCorner).trans' hEnd

end ProgeneratorMorita

end Etingof

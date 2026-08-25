/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

universe u v w

open scoped TensorProduct

namespace RepresentationTheory.SymmetricAlgebra.ProjectiveResolution

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]
variable {κ : Type w} [LinearOrder κ] [Fintype κ]

/-- For the displayed family of linear maps, the range at `i + 1` equals the kernel at `i`. -/
theorem basisLinearMap_range_succ_eq_ker (b : Module.Basis κ k V) (i : ℕ) :
    LinearMap.range
        (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
          b (i + 1)) =
      LinearMap.ker
        (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
          b i) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
      _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential_comp
        b i,
      LinearMap.zero_apply]
  · refine ⟨_root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.linearMapToSucc
      b (i + 1) x, ?_⟩
    have h :=
      _root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.succComposite_add_prevComposite_eq_id_apply
        b i x
    rwa [LinearMap.mem_ker.mp hx, map_zero, add_zero] at h

/-- The range of the zeroth map in the displayed family equals the kernel of the following linear map. -/
theorem basisLinearMap_range_zero_eq_ker (b : Module.Basis κ k V) :
    LinearMap.range
        (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
          b 0) =
      LinearMap.ker
        (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero
          k V) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
      _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero_comp_basisMap_zero
        b,
      LinearMap.zero_apply]
  · refine ⟨_root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.linearMapToSucc
      b 0 x, ?_⟩
    have h :=
      _root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.composite_add_auxiliaryComposite_eq_id_zero_apply
        b x
    rwa [LinearMap.mem_ker.mp hx, map_zero, add_zero] at h

omit [Fintype κ] in
/-- The displayed symmetric-algebra module at index `i` is free. -/
theorem basisIndexedTerm_free (b : Module.Basis κ k V) (i : ℕ) :
    Module.Free (SymmetricAlgebra k V)
      (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType
        k V i) :=
  Module.Free.of_basis
    (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.exteriorPowerBasis
      k V b i)

section Resolution

open CategoryTheory Limits

variable (b : Module.Basis κ k V)

/-- Every object of the complex determined by a finite ordered basis is projective. -/
theorem basisComplex_X_projective (i : ℕ) :
    Projective
      ((_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
        b).X i) :=
  haveI := basisIndexedTerm_free b i
  inferInstanceAs
    (Projective (ModuleCat.of (SymmetricAlgebra k V)
      (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType
        k V i)))

/-- A chain map from the basis-indexed complex to the complex concentrated in degree zero. -/
noncomputable def basisComplexToSingleZero :
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
        b ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} (SymmetricAlgebra k V))).obj
        (ModuleCat.of _
          (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)) :=
  (ChainComplex.toSingle₀Equiv
      (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
        b)
      (ModuleCat.of (SymmetricAlgebra k V)
        (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V))).symm
    ⟨ModuleCat.ofHom
        (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero
          k V), by
      rw [_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex_d
        b 0]
      ext x
      exact LinearMap.congr_fun
        (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero_comp_basisMap_zero
          b) x⟩

omit [LinearOrder κ] in
/-- The zero-degree component of the basis-indexed chain map is the displayed module homomorphism. -/
@[simp]
theorem basisComplexToSingleZero_f_zero :
    (basisComplexToSingleZero b).f 0 =
      ModuleCat.ofHom
        (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero
          k V) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The complex determined by a finite ordered basis is exact at index `i + 1`. -/
theorem basisComplex_exactAt_succ (i : ℕ) :
    (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
      b).ExactAt (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hf :
      ((_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
        b).sc' (i + 2) (i + 1) i).f =
        ModuleCat.ofHom
          (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
            b (i + 1)) :=
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex_d
      b (i + 1)
  have hg :
      ((_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
        b).sc' (i + 2) (i + 1) i).g =
        ModuleCat.ofHom
          (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
            b i) :=
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex_d
      b i
  intro x hx
  rw [hg] at hx
  refine ⟨_root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.linearMapToSucc
    b (i + 1) x, ?_⟩
  rw [hf]
  change
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
      b i x = 0 at hx
  change
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
      b (i + 1)
        (_root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.linearMapToSucc
          b (i + 1) x) = x
  have h :=
    _root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.succComposite_add_prevComposite_eq_id_apply
      b i x
  rwa [hx, map_zero, add_zero] at h

/-- The displayed short complex associated with a finite ordered basis is exact. -/
theorem basisShortComplex_exact :
    (ShortComplex.moduleCatMk
      (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
        b 0)
      (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero
        k V)
      (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero_comp_basisMap_zero
        b)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  refine ⟨_root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.linearMapToSucc
    b 0 x, ?_⟩
  change
    _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero
      k V x = 0 at hx
  change
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
      b 0
        (_root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.linearMapToSucc
          b 0 x) = x
  have h :=
    _root_.RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps.Module.Basis.composite_add_auxiliaryComposite_eq_id_zero_apply
      b x
  rwa [hx, map_zero, add_zero] at h

/-- The chain map to the complex concentrated in degree zero is a quasi-isomorphism. -/
theorem basisComplexToSingleZero_quasiIso : QuasiIso (basisComplexToSingleZero b) := by
  rw [quasiIso_iff]
  rintro (_ | i)
  · have hepi : Epi
        (ShortComplex.moduleCatMk
          (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
            b 0)
          (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero
            k V)
          (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero_comp_basisMap_zero
            b)).g := by
      rw [show
          (ShortComplex.moduleCatMk
            (_root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplexDifferential
              b 0)
            (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero
              k V)
            (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero_comp_basisMap_zero
              b)).g =
            ModuleCat.ofHom
              (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero
                k V) from rfl,
        ModuleCat.epi_iff_surjective]
      exact
        _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.tensorToDegreeZero_surjective
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_)).2
        ⟨basisShortComplex_exact b, hepi⟩
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    all_goals rfl
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact basisComplex_exactAt_succ b i

/-- A projective resolution of the displayed symmetric-algebra module associated with a finite ordered basis. -/
noncomputable def projectiveResolutionOfBasis :
    ProjectiveResolution
      (ModuleCat.of (SymmetricAlgebra k V)
        (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)) where
  complex :=
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
      b
  π := basisComplexToSingleZero b
  projective i := basisComplex_X_projective b i
  quasiIso := basisComplexToSingleZero_quasiIso b

/-- The complex underlying the basis-associated projective resolution is the displayed basis-indexed complex. -/
@[simp]
theorem projectiveResolutionOfBasis_complex :
    (projectiveResolutionOfBasis b).complex =
      _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.basisSymmetricAlgebraComplex
        b := rfl

/-- The structure map of the basis-associated projective resolution is the displayed chain map. -/
@[simp]
theorem projectiveResolutionOfBasis_pi :
    (projectiveResolutionOfBasis b).π = basisComplexToSingleZero b := rfl

/-- Every object of the complex underlying the basis-associated projective resolution is a free module. -/
theorem projectiveResolutionOfBasis_X_free (i : ℕ) :
    Module.Free (SymmetricAlgebra k V) ((projectiveResolutionOfBasis b).complex.X i) :=
  basisIndexedTerm_free b i

end Resolution

/-- A projective resolution constructed when the module is finite dimensional over a field. -/
noncomputable def projectiveResolutionOfFiniteDimensional (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    CategoryTheory.ProjectiveResolution
      (ModuleCat.of (SymmetricAlgebra k V)
        (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V)) :=
  projectiveResolutionOfBasis (Module.finBasis k V)

end RepresentationTheory.SymmetricAlgebra.ProjectiveResolution

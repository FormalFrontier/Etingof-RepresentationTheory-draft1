import EtingofRepresentationTheory.Chapter8.Problem8_2_10
import EtingofRepresentationTheory.Chapter8.Problem8_2_6
import EtingofRepresentationTheory.Chapter8.PIDDecomposition
import EtingofRepresentationTheory.Chapter8.TensorRightFunctorK
import EtingofRepresentationTheory.Chapter9.Example9_4_4
import EtingofRepresentationTheory.Chapter9.Problem9_4_2
import EtingofRepresentationTheory.Chapter9.HomologicalDimensionRingEquiv
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-!
# Hilbert-syzygy vanishing for finite-rank symmetric algebras

This file supplies the arbitrary-module vanishing conclusions of Problem 8.2.10(iv).  Its
general lemma says that every additive left-derived functor vanishes above the projective
dimension of its input.  Applying that lemma to the `k`-linear tensor functor gives the `Tor`
half; the `Ext` half follows from the defining characterization of projective dimension.

The finite-rank symmetric algebra is identified with a multivariate polynomial ring through a
chosen basis.  The resulting homological-dimension bound is therefore exactly the existing
Chapter 9 Hilbert-syzygy theorem, not an unrelated duplicate.

The companion module `Problem8_2_10_HilbertSyzygyResolution` carries out the book's construction:
it tensors the literal Koszul bimodule resolution with an arbitrary module and proves that the
resulting free projective resolution stops above `dim V`.  The endpoints here remain factored
through the Chapter 9 characterization, making their agreement with the later treatment explicit.
-/

universe u v

open CategoryTheory Limits

namespace Etingof

/-- An additive left-derived functor vanishes strictly above the projective dimension of its
input.  This is the derived-functor form of finite projective dimension, proved by repeatedly
dimension-shifting through projective presentations. -/
theorem isZero_leftDerived_of_hasProjectiveDimensionLE
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {D : Type u} [Category.{v} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (X : C) (d i : ℕ)
    (hX : HasProjectiveDimensionLE X d) (hi : d < i) :
    IsZero ((F.leftDerived i).obj X) := by
  induction d generalizing X i with
  | zero =>
      haveI : HasProjectiveDimensionLE X 0 := hX
      haveI : Projective X := (projective_iff_hasProjectiveDimensionLE_zero X).mpr hX
      cases i with
      | zero => omega
      | succ j => exact Functor.isZero_leftDerived_obj_projective_succ F j X
  | succ d ih =>
      obtain ⟨p⟩ := EnoughProjectives.presentation X
      let S : ShortComplex C := ShortComplex.mk (kernel.ι p.f) p.f (by simp)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p.f }
      haveI : Projective S.X₂ := p.projective
      have hP : HasProjectiveDimensionLT S.X₂ (d + 1) :=
        hasProjectiveDimensionLT_of_ge S.X₂ 1 (d + 1) (by omega)
      have hK : HasProjectiveDimensionLE S.X₁ d :=
        hS.hasProjectiveDimensionLT_X₁ (d + 1) hP hX
      cases i with
      | zero => omega
      | succ i =>
          cases i with
          | zero => omega
          | succ j =>
              obtain ⟨δ, hExact⟩ :=
                Functor.leftDerived_sixTerm_exact F hS (j + 1) (j + 2) rfl
              have hHighP : IsZero ((F.leftDerived (j + 2)).obj S.X₂) :=
                Functor.isZero_leftDerived_obj_projective_succ F (j + 1) S.X₂
              have hLowP : IsZero ((F.leftDerived (j + 1)).obj S.X₂) :=
                Functor.isZero_leftDerived_obj_projective_succ F j S.X₂
              let e := iso_of_sixTerm_exact hExact hHighP hLowP
              change ((F.leftDerived (j + 2)).obj S.X₃ ≅
                (F.leftDerived (j + 1)).obj S.X₁) at e
              have hKzero : IsZero ((F.leftDerived (j + 1)).obj S.X₁) :=
                ih S.X₁ (j + 1) hK (by omega)
              change IsZero ((F.leftDerived (j + 2)).obj S.X₃)
              exact IsZero.of_iso hKzero e

section SymmetricAlgebra

variable (k : Type u) [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V]
variable {n : ℕ}

local notation "SV" => SymmetricAlgebra k V

/-- The Chapter 9 polynomial-ring bound transported across the basis identification
`SymmetricAlgebra k V ≃ₐ[k] MvPolynomial (Fin n) k`. -/
theorem symmetricAlgebra_hasHomologicalDimensionLE (b : Module.Basis (Fin n) k V) :
    HasHomologicalDimensionLE SV n :=
  (hasHomologicalDimensionLE_congr
    (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv n).mpr
      (mvPolynomial_hasHomologicalDimensionLE k n)

/-- **Problem 8.2.10(iv), `Ext`.** Above `dim V = n`, `Extⁱ_{SV}(M,N)` vanishes for
arbitrary left `SV`-modules `M` and `N`. -/
theorem Problem_8_2_10_iv_ext (b : Module.Basis (Fin n) k V)
    (M N : ModuleCat.{u} SV) (i : ℕ) (hi : n < i) :
    Subsingleton (Abelian.Ext M N i) :=
  (Problem942.hasProjectiveDimensionLE_iff_ext_vanishing SV M n).mp
    (symmetricAlgebra_hasHomologicalDimensionLE k V b M) N i hi

/-- **Problem 8.2.10(iv), `Tor`.** Above `dim V = n`, `Torᵢ^{SV}(M,N)` vanishes for
arbitrary right `SV`-module `M` and left `SV`-module `N`. -/
theorem Problem_8_2_10_iv_tor (b : Module.Basis (Fin n) k V)
    (M : ModuleCat.{u} SVᵐᵒᵖ) (N : Type u) [AddCommGroup N] [Module SV N]
    (i : ℕ) (hi : n < i) :
    IsZero (Torₖ k SV N M i) := by
  have hRight : HasRightHomologicalDimensionLE SV n :=
    (hasRightHomologicalDimensionLE_iff_left n).mpr
      (symmetricAlgebra_hasHomologicalDimensionLE k V b)
  exact isZero_leftDerived_of_hasProjectiveDimensionLE
    (tensorRightFunctorₖ k SV N) M n i (hRight M) hi

/-- **Problem 8.2.10(iv), `Tor`, in the book's left-module convention.** Since `SV` is
commutative, an ordinary left `SV`-module is canonically a right `SV`-module.  Thus the Tor
vanishing theorem may be stated for two ordinary `SV`-modules, exactly as in the book. -/
theorem Problem_8_2_10_iv_tor_left_modules (b : Module.Basis (Fin n) k V)
    (M N : ModuleCat.{u} SV) (i : ℕ) (hi : n < i) :
    IsZero (Torₖ k SV N ((mopFunctor SV).obj M) i) :=
  Problem_8_2_10_iv_tor k V b ((mopFunctor SV).obj M) N i hi

/-- **Hilbert syzygies, arbitrary-module endpoint.** Every `SV`-module has projective
dimension at most `dim V = n`; consequently both `Ext` and `Tor` vanish in every degree above
`n`, uniformly for arbitrary ordinary left `SV`-modules.  The Tor input is converted to a right
module using commutativity of `SV`. -/
theorem Problem_8_2_10_iv_hilbert_syzygy (b : Module.Basis (Fin n) k V) :
    (∀ M : ModuleCat.{u} SV, HasProjectiveDimensionLE M n) ∧
      (∀ (M N : ModuleCat.{u} SV) (i : ℕ), n < i →
        Subsingleton (Abelian.Ext M N i)) ∧
      (∀ (M N : ModuleCat.{u} SV) (i : ℕ), n < i →
        IsZero (Torₖ k SV N ((mopFunctor SV).obj M) i)) := by
  refine ⟨symmetricAlgebra_hasHomologicalDimensionLE k V b, ?_, ?_⟩
  · exact fun M N i hi => Problem_8_2_10_iv_ext k V b M N i hi
  · exact fun M N i hi => Problem_8_2_10_iv_tor_left_modules k V b M N i hi

/-- Basis-free finite-dimensional form of the `Ext` vanishing endpoint, with the bound written
exactly as `dim V`. -/
theorem Problem_8_2_10_iv_ext_finrank [FiniteDimensional k V]
    (M N : ModuleCat.{u} SV) (i : ℕ) (hi : Module.finrank k V < i) :
    Subsingleton (Abelian.Ext M N i) :=
  Problem_8_2_10_iv_ext k V (Module.finBasis k V) M N i hi

/-- Basis-free finite-dimensional form of the `Tor` vanishing endpoint, with the bound written
exactly as `dim V`. -/
theorem Problem_8_2_10_iv_tor_finrank [FiniteDimensional k V]
    (M : ModuleCat.{u} SVᵐᵒᵖ) (N : Type u) [AddCommGroup N] [Module SV N]
    (i : ℕ) (hi : Module.finrank k V < i) :
    IsZero (Torₖ k SV N M i) :=
  Problem_8_2_10_iv_tor k V (Module.finBasis k V) M N i hi

/-- Basis-free finite-dimensional form of the `Tor` endpoint for two ordinary left
`SV`-modules. -/
theorem Problem_8_2_10_iv_tor_left_modules_finrank [FiniteDimensional k V]
    (M N : ModuleCat.{u} SV) (i : ℕ) (hi : Module.finrank k V < i) :
    IsZero (Torₖ k SV N ((mopFunctor SV).obj M) i) :=
  Problem_8_2_10_iv_tor_left_modules k V (Module.finBasis k V) M N i hi

/-- Basis-free finite-dimensional form of the simultaneous arbitrary-module Hilbert-syzygy
theorem, with the bound written exactly as `dim V`. -/
theorem Problem_8_2_10_iv_hilbert_syzygy_finrank [FiniteDimensional k V] :
    (∀ M : ModuleCat.{u} SV,
        HasProjectiveDimensionLE M (Module.finrank k V)) ∧
      (∀ (M N : ModuleCat.{u} SV) (i : ℕ), Module.finrank k V < i →
        Subsingleton (Abelian.Ext M N i)) ∧
      (∀ (M N : ModuleCat.{u} SV) (i : ℕ), Module.finrank k V < i →
        IsZero (Torₖ k SV N ((mopFunctor SV).obj M) i)) :=
  Problem_8_2_10_iv_hilbert_syzygy k V (Module.finBasis k V)

/-- The symmetric-algebra homological-dimension statement used above is literally the Chapter 9
multivariate-polynomial statement transported along the basis isomorphism. -/
theorem Problem_8_2_10_iv_agrees_with_Example_9_4_4
    (b : Module.Basis (Fin n) k V) :
    HasHomologicalDimensionLE SV n ↔
      HasHomologicalDimensionLE (MvPolynomial (Fin n) k) n :=
  hasHomologicalDimensionLE_congr
    (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv n

end SymmetricAlgebra

end Etingof

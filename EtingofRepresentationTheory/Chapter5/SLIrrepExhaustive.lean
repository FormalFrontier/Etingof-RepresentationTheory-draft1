import EtingofRepresentationTheory.Chapter5.Remark5_23_3
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLExhaustive

/-!
# Exhaustiveness bridge for algebraic `SL_N` representations

This file supplies the formal bridge from the landed `GL_N` highest-weight classification to
`SL_N`.  It defines intrinsic regularity of matrix coefficients on `SL_N`, proves that restriction
of an algebraic `GL_N` representation is algebraic, and classifies every simple `SL_N`
representation equipped with an algebraic `GL_N` extension.

The remaining genuinely `SL_N`-specific input for unconditional exhaustiveness is precisely that
every intrinsically algebraic simple `SL_N` representation admits such an extension.
-/

noncomputable section

namespace Etingof

/-- Matrix-coefficient regularity for a family of endomorphisms indexed by `SL_n(k)`.  The
coefficients are restrictions of polynomials in the standard `GL_n` coordinate variables; on
`SL_n`, the inverse-determinant coordinate evaluates to `1`. -/
def IsAlgebraicSLCoefficientFamily
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Matrix.SpecialLinearGroup (Fin n) k → Y →ₗ[k] Y) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) k Y)
    (P : Fin m → Fin m → MvPolynomial (GLCoordVars n) k),
    ∀ (g : Matrix.SpecialLinearGroup (Fin n) k) (a c : Fin m),
      b.repr (σ g (b c)) a = evalAtGL (Matrix.SpecialLinearGroup.toGL g) (P a c)

/-- A bundled `SL_n` representation is algebraic when its coefficient family is algebraic. -/
def IsAlgebraicSLRepresentation
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  IsAlgebraicSLCoefficientFamily n σ

/-- Restricting an algebraic `GL_n` coefficient family to `SL_n` preserves algebraicity. -/
theorem IsAlgebraicCoefficientFamily.slRestrict
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y}
    (hρ : IsAlgebraicCoefficientFamily n ρ) :
    IsAlgebraicSLCoefficientFamily n (slRestrict ρ) := by
  obtain ⟨m, b, P, hP⟩ := hρ
  exact ⟨m, b, P, fun g a c => hP (Matrix.SpecialLinearGroup.toGL g) a c⟩

/-- An `SL_n` representation has an algebraic `GL_n` extension if its action is obtained by
restriction from an algebraic `GL_n` representation on the same vector space. -/
def HasAlgebraicGLExtension
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  ∃ ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y,
    IsAlgebraicCoefficientFamily n ρ ∧ slRestrict ρ = σ

/-- Liftable algebraicity implies intrinsic algebraicity on `SL_n`. -/
theorem HasAlgebraicGLExtension.isAlgebraic
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y}
    (hσ : HasAlgebraicGLExtension n σ) : IsAlgebraicSLRepresentation n σ := by
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact hρ.slRestrict

/-- A representation whose restriction to `SL_n` is simple is itself simple as a `GL_n`
representation: every `GL_n`-stable subspace is in particular `SL_n`-stable. -/
theorem isSimpleModule_of_slRestrict_isSimple
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    [hsl : IsSimpleModule (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k))
      (slRestrict ρ).asModule] :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have hsl' : Representation.IsIrreducible (slRestrict ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).2 hsl
  letI : Nontrivial Y :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) (slRestrict ρ).asModule
  refine
    { exists_pair_ne := ⟨⊥, ⊤, by
        intro h
        have h' := congrArg Subrepresentation.toSubmodule h
        change (⊥ : Submodule k Y) = ⊤ at h'
        exact bot_ne_top h'⟩
      eq_bot_or_eq_top := fun S => ?_ }
  let T : Subrepresentation (slRestrict ρ) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g _ hv =>
        S.apply_mem_toSubmodule (Matrix.SpecialLinearGroup.toGL g) hv }
  rcases hsl'.eq_bot_or_eq_top T with hT | hT
  · left
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊥
    have hT' := congrArg Subrepresentation.toSubmodule hT
    change T.toSubmodule = (⊥ : Submodule k Y) at hT'
    exact hT'
  · right
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    have hT' := congrArg Subrepresentation.toSubmodule hT
    change T.toSubmodule = (⊤ : Submodule k Y) at hT'
    exact hT'

/-- **Conditional exhaustiveness for `SL_n`.** Every simple `SL_n` representation that admits an
algebraic `GL_n` extension is isomorphic to the restriction of `L_λ` for some dominant weight
`λ`.  The only extra input needed for unconditional #7808 is that intrinsic algebraicity implies
the existence of such an extension. -/
theorem exists_dominantWeight_slEquiv_of_hasAlgebraicGLExtension
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    (hσ : HasAlgebraicGLExtension n σ)
    [hsimp : IsSimpleModule (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) σ.asModule] :
    ∃ lam : DominantWeight n,
      Nonempty (Representation.Equiv σ (slRestrict (algIrrepGLRepρ n lam k))) := by
  obtain ⟨ρ, hρ, hres⟩ := hσ
  subst σ
  letI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule :=
    isSimpleModule_of_slRestrict_isSimple ρ
  obtain ⟨lam, ⟨e⟩⟩ :=
    exists_dominantWeight_asModuleEquiv_of_isSimpleModule n k ρ hρ
  let E : Representation.Equiv ρ (algIrrepGLRepρ n lam k) :=
    Representation.Equiv.mk (Representation.kEquivOfAsModuleEquiv e) (fun g => by
      ext v
      exact Representation.kEquivOfAsModuleEquiv_intertwines e g v)
  exact ⟨lam, ⟨slRestrictEquiv E⟩⟩

end Etingof

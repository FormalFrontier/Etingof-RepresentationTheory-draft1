import Mathlib
import EtingofRepresentationTheory.Chapter5.KernelLemmaKPrime
import EtingofRepresentationTheory.Chapter5.PolyRightGrading

/-!
# Extracting a simple constituent from a nonzero subrepresentation of `A/det`

This file builds the **extraction keystone** for the kernel-lemma-K′ assembly
(issue #4922, parent #4897): from a *nonzero* `GL_N`-invariant submodule `W` of the
determinant quotient `A/det = k[Xᵢⱼ]/(det)` (`quotDetRep`, `KernelLemmaKPrime.lean`)
it produces a *simple* finite-dimensional `GL_N`-representation `L` (an `FDRep`)
together with an injective `GL_N`-equivariant map `φ : L →ₗ[k] A/det` whose image
lands inside `W`. This is exactly the `(L, hLsimp, φ, hφ_inj, hφ_equiv)` data the
part-(a) lemma `quotDetRep_irreducible_constituent_lastWeight_zero`
(`CauchyDetQuotient.lean`) consumes.

## Why a minimal invariant submodule, not complete reducibility

`Theorem5_23_2_i` now states genuine complete reducibility
(`IsSemisimpleModule k[GL_N] ρ.asModule`), but its proof is still open (the GL_N
complete-reducibility infrastructure is a long-term blocker), so we cannot consume
it here. Instead we take a *minimal nonzero invariant submodule* (an **atom** of
the `k[GL_N]`-submodule lattice), which is simple as a representation without any
complete-reducibility input.

Two ingredients make this work:

* **Finite-dimensional reduction.** `A/det` is infinite-dimensional, so the
  submodule lattice is not Artinian. But the right-translation action is graded:
  a single element `w ∈ W` lifts to a polynomial of bounded total degree `D`, and
  `restrictTotalDegree D` is a finite-dimensional `polyRightRep`-invariant
  submodule (`polyRightRep_mem_restrictTotalDegree`). Its image in `A/det`
  intersected with `W` is a nonzero finite-dimensional invariant submodule
  `M₀ ≤ W`.
* **Atom of a finite module.** `M₀` is finite over `k`, hence Artinian over
  `k[GL_N]` (`isArtinian_of_tower`), so its submodule lattice is atomic
  (`isAtomic_of_orderBot_wellFounded_lt`). An atom is a simple `k[GL_N]`-submodule
  (`isSimpleModule_iff_isAtom`), which we package as the desired `FDRep`.
-/

noncomputable section

open MvPolynomial Etingof Etingof.PolynomialGLAction
open scoped MonoidAlgebra

namespace Etingof

/-! ## A finite module over a `k`-algebra has a simple submodule below any nonzero one -/

section SimpleSubmodule

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **A nonzero finite-dimensional invariant submodule contains a simple one.**
For a representation `ρ`, any nonzero `k[G]`-submodule `W` of `ρ.asModule` that is
finite-dimensional over `k` contains a *simple* `k[G]`-submodule `S ≤ W`.

`W` is finite over `k`, hence Artinian over the algebra `k[G]`
(`isArtinian_of_tower`); its submodule lattice is therefore atomic, and an atom is
a simple `k[G]`-module. -/
theorem exists_isSimpleModule_le (ρ : Representation k G V)
    (W : Submodule (MonoidAlgebra k G) ρ.asModule) [Module.Finite k W] (hW : W ≠ ⊥) :
    ∃ S : Submodule (MonoidAlgebra k G) ρ.asModule,
      IsSimpleModule (MonoidAlgebra k G) S ∧ S ≤ W := by
  haveI : IsArtinian k W := inferInstance
  haveI : IsArtinian (MonoidAlgebra k G) W := isArtinian_of_tower k inferInstance
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  haveI : Nontrivial (Submodule (MonoidAlgebra k G) W) :=
    (Submodule.nontrivial_iff (MonoidAlgebra k G)).mpr inferInstance
  haveI : IsAtomic (Submodule (MonoidAlgebra k G) W) :=
    isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf
  obtain ⟨b, hb⟩ := IsAtomic.exists_atom (Submodule (MonoidAlgebra k G) W)
  haveI : IsSimpleModule (MonoidAlgebra k G) b := isSimpleModule_iff_isAtom.mpr hb
  refine ⟨b.map W.subtype, ?_, Submodule.map_subtype_le W b⟩
  exact IsSimpleModule.congr
    (Submodule.equivMapOfInjective W.subtype Subtype.val_injective b).symm

end SimpleSubmodule

/-! ## The simplicity bridge: subrepresentation `asModule` vs. `asSubmodule` -/

section Bridge

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- The `k[G]`-module `(σ.toRepresentation).asModule` carried by a subrepresentation
`σ` is, as a `k[G]`-module, the corresponding `k[G]`-submodule `σ.asSubmodule` of
`ρ.asModule`: both have the underlying set `σ.toSubmodule`, and on `single g t` both
actions send `y ↦ t • ρ g y`. -/
def toRepAsModuleEquiv (σ : Subrepresentation ρ) :
    (σ.toRepresentation).asModule ≃ₗ[MonoidAlgebra k G] σ.asSubmodule where
  toFun y := ⟨((σ.toRepresentation).asModuleEquiv y).1,
    ((σ.toRepresentation).asModuleEquiv y).2⟩
  map_add' y z := by apply Subtype.ext; simp
  map_smul' c y := by
    apply Subtype.ext
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add c₁ c₂ h₁ h₂ =>
        simp only [add_smul, RingHom.id_apply] at h₁ h₂ ⊢
        rw [Submodule.coe_add, ← h₁, ← h₂]; rfl
    | single g t =>
        simp only [RingHom.id_apply, SetLike.val_smul]
        rw [Representation.single_smul, Representation.single_smul]
        rfl
  invFun x := (σ.toRepresentation).asModuleEquiv.symm ⟨x.1, x.2⟩
  left_inv y := by simp
  right_inv x := by apply Subtype.ext; simp

/-- The carried module of a subrepresentation is simple exactly when the
corresponding `k[G]`-submodule is simple. -/
theorem isSimpleModule_toRepresentation_asModule (σ : Subrepresentation ρ)
    (h : IsSimpleModule (MonoidAlgebra k G) σ.asSubmodule) :
    IsSimpleModule (MonoidAlgebra k G) (σ.toRepresentation).asModule :=
  IsSimpleModule.congr (toRepAsModuleEquiv σ)

end Bridge

/-! ## The extraction keystone -/

namespace KernelLemmaKPrime

open Etingof.KernelLemmaKPrime Etingof.PolyRightGrading

variable {k : Type*} [Field k] {N : ℕ}

/-- **`polyRightRep` preserves bounded total degree.** Right translation sends each
variable to a homogeneous degree-`1` element, so it preserves total-degree `≤ D`;
the proof decomposes `f` into homogeneous components and uses that each component's
image is homogeneous of the same degree. -/
theorem polyRightRep_mem_restrictTotalDegree
    (g : Matrix.GeneralLinearGroup (Fin N) k) (D : ℕ)
    {f : MvPolynomial (Fin N × Fin N) k}
    (hf : f ∈ MvPolynomial.restrictTotalDegree (Fin N × Fin N) k D) :
    polyRightRep k N g f ∈ MvPolynomial.restrictTotalDegree (Fin N × Fin N) k D := by
  rw [MvPolynomial.mem_restrictTotalDegree] at hf
  have hsplit : polyRightRep k N g f
      = ∑ d ∈ Finset.range (f.totalDegree + 1),
          polyRightRep k N g (homogeneousComponent d f) := by
    rw [← map_sum]; congr 1; exact (MvPolynomial.sum_homogeneousComponent f).symm
  rw [hsplit]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.mem_restrictTotalDegree]
  refine le_trans
    (Etingof.PolyRightGrading.polyRightRep_isHomogeneous g
      (MvPolynomial.homogeneousComponent_isHomogeneous d f)).totalDegree_le ?_
  simp only [Finset.mem_range] at hd
  omega

/-- **The extraction keystone (issue #4922).** From a *nonzero* `GL_N`-invariant
submodule `W` of the determinant quotient `A/det = k[Xᵢⱼ]/(det)` (`quotDetRep`) we
extract a *simple* finite-dimensional `GL_N`-representation `L` together with an
injective `GL_N`-equivariant map `φ : L →ₗ[k] A/det` whose image lands inside `W`.

This is the data consumed by `quotDetRep_irreducible_constituent_lastWeight_zero`
(`CauchyDetQuotient.lean`). The construction: pick `w ≠ 0` in `W`, lift it to a
polynomial of total degree `≤ D`, push the finite-dimensional invariant submodule
`restrictTotalDegree D` down to `A/det` and intersect with `W` to get a *nonzero,
finite-dimensional, invariant* `M₀ ≤ W`; then take an atom of `M₀`'s
`k[GL_N]`-submodule lattice, which is a simple sub-representation. -/
theorem exists_simple_subrep_of_quotDetRep
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    {W : Submodule k (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N)}
    (hW_inv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ w ∈ W, quotDetRep k N g w ∈ W) (hW : W ≠ ⊥) :
    ∃ (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (φ : L →ₗ[k] (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N)),
      IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule L.ρ) ∧
      Function.Injective φ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
        φ (L.ρ g v) = quotDetRep k N g (φ v)) ∧
      Set.range φ ⊆ (W : Set _) := by
  classical
  -- A nonzero element `w = mk p` of `W`, with `p` of total degree `D`.
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  set D := p.totalDegree with hD
  -- The finite-dimensional `polyRightRep`-invariant submodule `restrictTotalDegree D`,
  -- pushed down to `A/det`.
  set Bsub : Submodule k (MvPolynomial (Fin N × Fin N) k) :=
    MvPolynomial.restrictTotalDegree (Fin N × Fin N) k D with hBsub
  set Bq : Submodule k (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) :=
    Bsub.map (Submodule.mkQ (detSubmodule k N)) with hBq
  -- `Bq` is invariant under `quotDetRep`.
  have hBq_inv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ x ∈ Bq, quotDetRep k N g x ∈ Bq := by
    rintro g _ ⟨f, hf, rfl⟩
    exact ⟨polyRightRep k N g f, polyRightRep_mem_restrictTotalDegree g D hf, by
      simp [quotDetRep_mk]⟩
  -- Package `W` and `Bq` as subrepresentations and take their meet.
  let Wr : Subrepresentation (quotDetRep k N) := ⟨W, fun g _ hx => hW_inv g _ hx⟩
  let Bqr : Subrepresentation (quotDetRep k N) := ⟨Bq, fun g _ hx => hBq_inv g _ hx⟩
  set M₀ : Submodule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (quotDetRep k N).asModule := (Wr ⊓ Bqr).asSubmodule with hM₀
  -- `w = mk p` lies in `M₀` (in `W`, and `p` has degree `≤ D`).
  have hwBq : (Submodule.Quotient.mk p :
      MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N) ∈ Bq :=
    ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin N × Fin N) D p).mpr (le_of_eq hD.symm), rfl⟩
  have hwM₀ : (Submodule.Quotient.mk p : (quotDetRep k N).asModule) ∈ M₀ := ⟨hwW, hwBq⟩
  -- Finite-dimensionality of `M₀` over `k`.
  haveI : Module.Finite k (Wr ⊓ Bqr).toSubmodule := by
    rw [Subrepresentation.toSubmodule_inf]
    exact Module.Finite.of_injective
      (Submodule.inclusion (inf_le_right : Wr.toSubmodule ⊓ Bqr.toSubmodule ≤ Bqr.toSubmodule))
      (Submodule.inclusion_injective _)
  haveI : Module.Finite k M₀ :=
    Module.Finite.equiv ((toRepAsModuleEquiv (Wr ⊓ Bqr)).restrictScalars k)
  have hM₀ne : M₀ ≠ ⊥ := by
    intro h
    apply hw0
    have : (Submodule.Quotient.mk p : (quotDetRep k N).asModule) = 0 := by
      rw [h] at hwM₀; simpa using hwM₀
    exact this
  -- Extract a simple `k[GL_N]`-submodule `S ≤ M₀`.
  obtain ⟨S, hSsimple, hSle⟩ := exists_isSimpleModule_le (quotDetRep k N) M₀ hM₀ne
  -- Package `S` as a subrepresentation and its `toRepresentation` as an `FDRep`.
  set Sr : Subrepresentation (quotDetRep k N) := Subrepresentation.ofSubmodule' S with hSr
  have hSrAsSub : Sr.asSubmodule = S := rfl
  have hScarrier : ∀ x ∈ Sr.toSubmodule, x ∈ W := fun x hx => (hSle hx).1
  haveI : Module.Finite k Sr.toSubmodule := by
    have hle : Sr.toSubmodule ≤ (Wr ⊓ Bqr).toSubmodule := fun x hx => hSle hx
    exact Module.Finite.of_injective
      (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  refine ⟨FDRep.of Sr.toRepresentation, Sr.toSubmodule.subtype, ?_, ?_, ?_, ?_⟩
  · have hsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        Sr.asSubmodule := by rw [hSrAsSub]; exact hSsimple
    exact isSimpleModule_toRepresentation_asModule Sr hsimp
  · exact Subtype.val_injective
  · intro g v; rfl
  · rintro _ ⟨v, rfl⟩
    exact hScarrier _ v.2

end KernelLemmaKPrime

end Etingof

end

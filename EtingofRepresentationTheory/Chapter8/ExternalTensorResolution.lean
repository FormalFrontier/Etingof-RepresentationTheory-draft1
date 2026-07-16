import EtingofRepresentationTheory.Chapter8.ExternalTensorComplex
import EtingofRepresentationTheory.Chapter8.ExternalTensorProjective
import EtingofRepresentationTheory.Chapter8.ExternalTensorRestriction
import EtingofRepresentationTheory.Chapter7.KunnethChainComplexNat
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# The external tensor product of two projective resolutions is a projective resolution

Assembling the pieces built in `ExternalTensorComplex.lean` (the total complex
`Etingof.extTensorComplex P₁ P₂` and its augmentation `Etingof.extTensorπ P₁ P₂`) and
`ExternalTensorProjective.lean` (degreewise projectivity `Etingof.extTensor_projective`), this
file constructs the `ProjectiveResolution` of `M₁ ⊗[k] M₂` over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`:

* `Etingof.extTensorComplex_projective`: each degree `(extTensorComplex P₁ P₂).X n` is projective
  over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`. Degree `n` is the coproduct `⨁_{i₁+i₂=n} (P₁)_{i₁} ⊗[k] (P₂)_{i₂}` of the
  bidegree pieces (`GradedObject.mapObj` = `∐`), each projective by `extTensor_projective` since the
  factors `(P₁)_{i₁}`, `(P₂)_{i₂}` are projective; a coproduct of projectives is projective.
* `Etingof.extTensorProjectiveResolution`: the `ProjectiveResolution` itself, with
  `complex := extTensorComplex P₁ P₂`, `π := extTensorπ P₁ P₂`, degreewise projectivity from the
  lemma above, and the `quasiIso` obligation (exactness of the resolution).

## The base ring must be a field

This file works over a **field** `k`, not a general `CommRing`. The `quasiIso` field of
`extTensorProjectiveResolution` — exactness of `P•₁ ⊗_k P•₂` as a resolution of `M₁ ⊗_k M₂` — is
*false* over a general commutative ring: it is the vanishing of the higher `Tor`
`Tor_{>0}^k(M₁, M₂)`, which is nonzero already for `k = ℤ`, `M₁ = M₂ = ℤ/2` (there
`Tor_1^ℤ(ℤ/2, ℤ/2) = ℤ/2`, so `P•₁ ⊗_ℤ P•₂` has homology in degree 1 and is not a resolution).
Over a field every module is flat, so the obstruction vanishes. Accordingly the section variable is
`[Field k]`; nothing downstream consumes the (over-general, previously `[CommRing k]`) resolution
yet, so tightening the hypothesis is safe.

## Status of `quasiIso`

The positive-degree half is proved here: `homology_tensorObj_res_isZero_succ` shows the `k`-tensor
of the two restricted resolutions is exact in every degree `n + 1`, via the Chapter 7 Künneth
formula `kunnethChainComplexNat` (`H_{n+1}(C₁ ⊗ C₂) ≅ ⨁_{p+q=n+1} H_p(C₁) ⊗ H_q(C₂)`, every summand
zero
since one index is positive and the restricted resolutions are acyclic in positive degrees).

The `quasiIso` field itself is still a `sorry` (a proof obligation *within* the definition; the
resolution data is real). What remains is the degree-`0` half — that the augmentation induces an
isomorphism on `H_0`, i.e. `H_0(C₁ ⊗ C₂) ≅ res M₁ ⊗ res M₂` compatibly with the map — together with
the final assembly. The route (tracked as a follow-up work item) is:

1. Restriction of scalars `ModuleCat (A₁ ⊗ A₂)ᵐᵒᵖ ⥤ ModuleCat k` is exact and conservative, hence
   reflects `QuasiIso` (`quasiIso_map_iff_of_preservesHomology`).
2. It carries `extTensorComplex P₁ P₂` to the total `k`-tensor complex of the underlying
   `k`-complexes of `P•₁`, `P•₂`, via `extTensorComplex_restrictIso` (#6738).
3. That `k`-tensor augmentation is a quasi-isomorphism: positive degrees by
   `homology_tensorObj_res_isZero_succ` above, and degree `0` by right-exactness of `⊗` over a field
   with the map-level `i = 0` square `ι_extRestrictComplexXIso_aug₀` (#6738).
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct MulOpposite

namespace Etingof

universe u

variable {k : Type u} [Field k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}

-- The restriction-of-scalars `k`-module structures on `A₁ᵐᵒᵖ`- and `A₂ᵐᵒᵖ`-modules, needed to
-- form the `k`-tensor `M₁ ⊗[k] M₂` and its external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action.
attribute [local instance] restrictModule₁ restrictModule₂ tower₁ tower₂ extModule

/-- The degree `.X n` of the external tensor complex, unfolded to the coproduct `mapObj` of its
bidegree summands. Stated as a `rfl` at the `mapObj` level (a single `total` projection), which is
cheap — unfolding all the way to `∐` forces a costly normalization of the bifunctor terms. -/
private theorem extTensorComplex_X_eq (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (n : ℕ) :
    (extTensorComplex (k := k) P₁ P₂).X n
      = (((((extTensorFunctor k A₁ A₂).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
          P₂.complex).toGradedObject.mapObj
          (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ))) n :=
  rfl

/-- Each degree of the external tensor complex is projective over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`. Degree `n` is
the coproduct of the bidegree pieces `(P₁)_{i₁} ⊗[k] (P₂)_{i₂}` over `i₁ + i₂ = n`; each is
projective by `extTensor_projective` (the factors are projective, being terms of projective
resolutions), and a coproduct of projectives is projective. The lifting property is assembled by
hand from `Sigma.desc`/`Sigma.ι` rather than via the coproduct-`Projective` instance, whose
full-transparency defeq check does not terminate on the heavy bifunctor summands. -/
theorem extTensorComplex_projective (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (n : ℕ) : Projective ((extTensorComplex (k := k) P₁ P₂).X n) := by
  rw [extTensorComplex_X_eq]
  set g := ((((extTensorFunctor k A₁ A₂).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj
    P₂.complex).toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n with hg
  -- Each summand `(P₁)_{i₁} ⊗[k] (P₂)_{i₂}` is projective; the coproduct exists.
  haveI hsummand : ∀ i, Projective (g i) := by
    rw [hg]; rintro ⟨⟨i₁, i₂⟩, h⟩
    exact extTensor_projective k A₁ A₂ (P₁.complex.X i₁) (P₂.complex.X i₂)
  haveI hcop : HasCoproduct g := by rw [hg]; infer_instance
  show Projective (∐ g)
  refine ⟨fun {E X} f e he => ⟨Sigma.desc fun b => Projective.factorThru (Sigma.ι g b ≫ f) e, ?_⟩⟩
  apply Sigma.hom_ext
  intro b
  rw [Sigma.ι_desc_assoc]
  exact Projective.factorThru_comp _ e

/-- Restriction of scalars along any ring hom preserves homology. It is a left adjoint
(`restrictCoextendScalarsAdj`), hence preserves cokernels; it also preserves monomorphisms and zero
morphisms, so `preservesHomology_of_preservesMonos_and_cokernels` applies. (The
`ChangeOfRingsExact` instances give this only for *commutative* target rings, which fails here since
`A₁ᵐᵒᵖ`, `A₂ᵐᵒᵖ` are noncommutative.) -/
theorem restrictScalars_preservesHomology {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{u} f).PreservesHomology := by
  haveI : Limits.PreservesColimits (ModuleCat.restrictScalars.{u} f) :=
    (ModuleCat.restrictCoextendScalarsAdj f).leftAdjoint_preservesColimits
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- A homology-preserving functor `F : ModuleCat R ⥤ ModuleCat k` carries a projective resolution to
a complex that is exact in every positive degree: `F` sends the quasi-isomorphism `Q.π` to a
quasi-isomorphism onto `F (single₀ N)`, whose homology vanishes above degree `0`. Applied below with
`F = res₁ k A₁` and `F = res₂ k A₂` to the two restricted resolutions. -/
theorem homology_mapHomologicalComplex_projective_isZero_succ
    {R : Type u} [Ring R] {N : ModuleCat.{u} R} (Q : ProjectiveResolution N)
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} k) [F.Additive] [F.PreservesHomology] (n : ℕ) :
    IsZero (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homology (n + 1)) := by
  have hqi : QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) (n + 1) :=
    inferInstance
  rw [quasiIsoAt_iff_isIso_homologyMap] at hqi
  refine IsZero.of_iso ?_ (asIso (HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) (n + 1)))
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ)
    (n + 1)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app N))
  exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 (F.obj N) (n + 1)
    (by simp)

/-- **Positive-degree acyclicity** of the `k`-tensor of the two restricted resolutions. By the
Chapter 7 Künneth formula `kunnethChainComplexNat`,
`H_{n+1}(C₁ ⊗ C₂) ≅ ⨁_{p+q=n+1} H_p(C₁) ⊗ H_q(C₂)`; every summand vanishes because one of `p, q`
is positive and `homology_mapHomologicalComplex_projective_isZero_succ` makes the corresponding
restricted-resolution homology zero, so the tensor summand is zero. This is the positive-degree
input to the `quasiIso` obligation of `extTensorProjectiveResolution`. -/
theorem homology_tensorObj_res_isZero_succ
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    IsZero ((HomologicalComplex.tensorObj (res₁Complex (k := k) P₁)
      (res₂Complex (k := k) P₂)).homology (n + 1)) := by
  haveI : (res₁ k A₁).PreservesHomology := restrictScalars_preservesHomology _
  haveI : (res₂ k A₂).PreservesHomology := restrictScalars_preservesHomology _
  obtain ⟨iso⟩ := kunnethChainComplexNat (res₁Complex (k := k) P₁) (res₂Complex (k := k) P₂) (n + 1)
  refine IsZero.of_iso ?_ iso
  rw [IsZero.iff_id_eq_zero]
  apply Limits.Sigma.hom_ext
  intro a
  rw [Category.comp_id, comp_zero]
  obtain ⟨⟨p, q⟩, hpq⟩ := a
  have hpq' : p + q = n + 1 := hpq
  refine IsZero.eq_zero_of_src ?_ _
  rcases p with _ | p'
  · have hq : q = n + 1 := by omega
    subst hq
    exact TensorExtend.isZero_tensorObj_right
      (homology_mapHomologicalComplex_projective_isZero_succ P₂ (res₂ k A₂) n)
  · exact TensorExtend.isZero_tensorObj_left
      (homology_mapHomologicalComplex_projective_isZero_succ P₁ (res₁ k A₁) p')

/-- The **external tensor product of two projective resolutions** `P•₁ ⊗_k P•₂` is a projective
resolution of `M₁ ⊗[k] M₂` over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`. The complex and augmentation are the total
complex `extTensorComplex P₁ P₂` and its augmentation `extTensorπ P₁ P₂`; degreewise projectivity is
`extTensorComplex_projective`. The `quasiIso` obligation (exactness of the resolution) is currently
`sorry` — see the module docstring for the route. -/
noncomputable def extTensorProjectiveResolution
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ProjectiveResolution (ModuleCat.of (A₁ ⊗[k] A₂)ᵐᵒᵖ (M₁ ⊗[k] M₂)) where
  complex := extTensorComplex P₁ P₂
  projective := extTensorComplex_projective P₁ P₂
  π := extTensorπ P₁ P₂
  -- Remaining: assemble `QuasiIso` from `homology_tensorObj_res_isZero_succ` (positive degrees)
  -- and the degree-`0` augmentation isomorphism, transported by `extTensorComplex_restrictIso`
  -- (#6738). Positive-degree acyclicity is proved above; see the module docstring for the route.
  quasiIso := sorry

end Etingof

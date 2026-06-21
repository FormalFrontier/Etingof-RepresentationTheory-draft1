import Mathlib
import EtingofRepresentationTheory.Chapter5.DetShiftIso

/-!
# The right-`GL_N` homogeneous grading of `k[Xᵢⱼ]` and the per-degree det sequence

This file records the **graded backbone** of the right-translation representation
`polyRightRep` on `A = k[Xᵢⱼ] = MvPolynomial (Fin N × Fin N) k`
(`PolynomialGLRightAction.lean`). It is missing-infrastructure **piece (2)** of the
kernel-lemma-K′ core (issue #4896, route doc `progress/kernel-lemma-K-route.md`):
the graded data that turns the `GL × GL`-equivariant Cauchy multiplicity decomposition
into the `ν_N = 0` conclusion for the determinant quotient `A/det`.

## The grading is `GL_N`-invariant

Right translation `R_g` sends each variable `X_{ij}` to a homogeneous degree-`1`
element `∑_l g_{lj} X_{il}` (`polyRightRep_apply_X`), so as an algebra hom it
preserves the total-degree grading:

* `rTransAlgHom_isHomogeneous` / `polyRightRep_isHomogeneous` — `R_g` preserves
  `IsHomogeneous d`;
* `polyRightHomogeneousSubrep k N d` — the total-degree-`d` homogeneous component
  `homogeneousSubmodule (Fin N × Fin N) k d` packaged as a `Subrepresentation` of
  `polyRightRep`. The same component is also a subrepresentation of the
  determinant-character twist `A ⊗ χ` (`polyRightTwistHomogeneousSubrep`), since the
  twist only rescales by `det(g)`.

## `det` is homogeneous of degree `N`

* `detPoly_isHomogeneous` — the generic determinant `detPoly = det(Xᵢⱼ)` is
  homogeneous of degree `N` (it is a signed sum of products of `N` distinct
  variables).
* `mulDet_isHomogeneous` / `mulDet_homogeneousSubmodule_le` — consequently
  `mulDet = (detPoly · ·)` raises total degree by `N`, sending the degree-`d`
  component into the degree-`(N + d)` component.

## The per-degree short exact sequence

In each degree `d ≥ N`, multiplication by `det` realizes the determinant ideal's
degree-`d` slice as the image of the degree-`(d - N)` slice:

* `detSubmodule_inf_homogeneous` — `(det) ∩ A_d = mulDet '' A_{d-N}` (the principal
  ideal `(det)` is a graded submodule, with degree-`d` part `det · A_{d-N}`). This
  is the exactness in the middle of the right-`GL_N`-equivariant sequence

  `0 → A_{d-N} ⊗ χ  --mulDet-->  A_d  --mk-->  (A/det)_d → 0`.

  The left map `mulDet` is injective (`mulDet_injective`, `DetShiftIso.lean`) and
  `GL_N`-equivariant up to the determinant-character twist `χ`
  (`mulDet_intertwine`, `detShiftLinearEquiv_intertwine`, `DetShiftIso.lean`,
  already sorry-free); the right map is the quotient projection
  (`quotDetRep`). The degree-`d` part of `A/det` is therefore
  `A_d / (det · A_{d-N})`.

## Consumer

The #4896 part-(a) assembly (`CauchyDetQuotient.lean`,
`quotDetRep_irreducible_constituent_lastWeight_zero`) reads the `ν_N = 0`
constituent condition off this graded sequence together with the Cauchy
multiplicity decomposition: `det` shifts every constituent's highest weight by
`(1, …, 1)`, so `A/det = A / (det · A)` keeps exactly the constituents with
`ν_N = 0`.
-/

namespace Etingof.PolyRightGrading

open MvPolynomial Etingof.PolynomialGLAction Etingof.DetLocalization
  Etingof.KernelLemmaKPrime Etingof.DetShiftIso

variable {k : Type*} [Field k] {N : ℕ}

/-! ### The grading is `GL_N`-invariant -/

/-- **Right translation preserves the total-degree grading.** The algebra
endomorphism `rTransAlgHom M` sends each variable to a homogeneous degree-`1`
element (`∑_l M_{lj} X_{il}`), so it preserves `IsHomogeneous d` for every `d`. -/
theorem rTransAlgHom_isHomogeneous (M : Matrix (Fin N) (Fin N) k) {d : ℕ}
    {f : MvPolynomial (Fin N × Fin N) k} (hf : f.IsHomogeneous d) :
    (rTransAlgHom M f).IsHomogeneous d := by
  have hgen : ∀ ij : Fin N × Fin N,
      (∑ l : Fin N, M l ij.2 • MvPolynomial.X (ij.1, l) :
        MvPolynomial (Fin N × Fin N) k).IsHomogeneous 1 := by
    intro ij
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    refine Submodule.sum_mem _ fun l _ => ?_
    exact Submodule.smul_mem _ _
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k _))
  have h := hf.aeval (fun ij => ∑ l : Fin N, M l ij.2 • MvPolynomial.X (ij.1, l)) hgen
  rwa [one_mul] at h

/-- **Right translation preserves the total-degree grading** (the `GL_N`-action
version of `rTransAlgHom_isHomogeneous`). -/
theorem polyRightRep_isHomogeneous (g : Matrix.GeneralLinearGroup (Fin N) k) {d : ℕ}
    {f : MvPolynomial (Fin N × Fin N) k} (hf : f.IsHomogeneous d) :
    (polyRightRep k N g f).IsHomogeneous d := by
  rw [polyRightRep_apply]
  exact rTransAlgHom_isHomogeneous _ hf

/-- **The total-degree-`d` homogeneous component is a subrepresentation** of the
right-translation rep `polyRightRep`. This packages `rTransAlgHom_isHomogeneous`:
each graded piece `A_d` is right-`GL_N`-stable. -/
noncomputable def polyRightHomogeneousSubrep (k : Type*) [Field k] (N : ℕ) (d : ℕ) :
    Subrepresentation (polyRightRep k N) where
  toSubmodule := MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d
  apply_mem_toSubmodule g _f hf :=
    (MvPolynomial.mem_homogeneousSubmodule d _).2
      (polyRightRep_isHomogeneous g ((MvPolynomial.mem_homogeneousSubmodule d _).1 hf))

@[simp] theorem polyRightHomogeneousSubrep_toSubmodule (d : ℕ) :
    (polyRightHomogeneousSubrep k N d).toSubmodule
      = MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d :=
  rfl

/-- **The grading is also invariant under the determinant-character twist** `A ⊗ χ`:
`charTwistRep (detChar) (polyRightRep)` only rescales `polyRightRep` by `det(g)`, and
homogeneity is closed under scaling. -/
theorem charTwist_polyRightRep_isHomogeneous (g : Matrix.GeneralLinearGroup (Fin N) k)
    {d : ℕ} {f : MvPolynomial (Fin N × Fin N) k} (hf : f.IsHomogeneous d) :
    (charTwistRep (detChar k N) (polyRightRep k N) g f).IsHomogeneous d := by
  rw [charTwistRep_apply, ← MvPolynomial.mem_homogeneousSubmodule]
  exact Submodule.smul_mem _ _
    ((MvPolynomial.mem_homogeneousSubmodule d _).2 (polyRightRep_isHomogeneous g hf))

/-- **The degree-`d` component as a subrepresentation of the twisted rep `A ⊗ χ`.**
This is the left-hand object of the per-degree short exact sequence (shifted to
degree `d - N` below). -/
noncomputable def polyRightTwistHomogeneousSubrep (k : Type*) [Field k] (N : ℕ) (d : ℕ) :
    Subrepresentation (charTwistRep (detChar k N) (polyRightRep k N)) where
  toSubmodule := MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d
  apply_mem_toSubmodule g _f hf :=
    (MvPolynomial.mem_homogeneousSubmodule d _).2
      (charTwist_polyRightRep_isHomogeneous g ((MvPolynomial.mem_homogeneousSubmodule d _).1 hf))

/-! ### `det` is homogeneous of degree `N` -/

/-- **The generic determinant is homogeneous of degree `N`.** `detPoly = det(Xᵢⱼ)`
is the signed sum `∑_σ ε(σ) ∏_i X_{σ(i),i}` of products of `N` distinct degree-`1`
variables, so every monomial has total degree `N`. -/
theorem detPoly_isHomogeneous : (detPoly k N).IsHomogeneous N := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, detPoly, Matrix.det_apply]
  apply Submodule.sum_mem
  intro σ _
  have hprod : (∏ i : Fin N, Matrix.mvPolynomialX (Fin N) (Fin N) k (σ i) i)
      ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k N := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin N))
      (fun i => Matrix.mvPolynomialX (Fin N) (Fin N) k (σ i) i) (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X k (σ i, i))
    simpa using h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rw [hσ, one_smul]; exact hprod
  · have hneg : ((-1 : ℤˣ)) •
        (∏ i : Fin N, Matrix.mvPolynomialX (Fin N) (Fin N) k (σ i) i)
        = -(∏ i : Fin N, Matrix.mvPolynomialX (Fin N) (Fin N) k (σ i) i) := by
      rw [Units.smul_def]; simp
    rw [hσ, hneg]
    exact Submodule.neg_mem _ hprod

/-- **Multiplication by `det` raises total degree by `N`.** If `Q` is homogeneous of
degree `d`, then `mulDet Q = detPoly · Q` is homogeneous of degree `N + d`. -/
theorem mulDet_isHomogeneous {d : ℕ} {Q : MvPolynomial (Fin N × Fin N) k}
    (hQ : Q.IsHomogeneous d) : (mulDet k N Q).IsHomogeneous (N + d) := by
  rw [mulDet_apply]
  exact detPoly_isHomogeneous.mul hQ

/-- **`mulDet` maps the degree-`d` component into the degree-`(N + d)` component.**
The submodule-level form of `mulDet_isHomogeneous`. -/
theorem mulDet_homogeneousSubmodule_le (d : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map (mulDet k N)
      ≤ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k (N + d) := by
  rintro _ ⟨Q, hQ, rfl⟩
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
    (mulDet_isHomogeneous ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hQ))

/-! ### The per-degree short exact sequence -/

/-- **Multiplying by `det` commutes with extracting the degree-shifted homogeneous
component.** Since `detPoly` is homogeneous of degree `N`, the degree-`(N + e)`
component of `detPoly · Q` is `detPoly` times the degree-`e` component of `Q`. This
is the computation that makes the determinant ideal a *graded* submodule. -/
theorem homogeneousComponent_detPoly_mul (Q : MvPolynomial (Fin N × Fin N) k) (e : ℕ) :
    MvPolynomial.homogeneousComponent (N + e) (detPoly k N * Q)
      = detPoly k N * MvPolynomial.homogeneousComponent e Q := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent Q, Finset.mul_sum, map_sum]
  rw [show (∑ j ∈ Finset.range (Q.totalDegree + 1),
        MvPolynomial.homogeneousComponent (N + e)
          (detPoly k N * MvPolynomial.homogeneousComponent j Q))
      = ∑ j ∈ Finset.range (Q.totalDegree + 1),
          (if e = j then detPoly k N * MvPolynomial.homogeneousComponent j Q else 0) from
        Finset.sum_congr rfl fun j _ => by
          rw [MvPolynomial.homogeneousComponent_of_mem
            ((MvPolynomial.mem_homogeneousSubmodule (N + j) _).2
              (detPoly_isHomogeneous.mul
                (MvPolynomial.homogeneousComponent_isHomogeneous j Q)))]
          exact if_congr (by omega) rfl rfl]
  rw [Finset.sum_ite_eq]
  split
  · rfl
  · next h =>
    have he : Q.totalDegree < e := by simp only [Finset.mem_range, not_lt] at h; omega
    rw [MvPolynomial.homogeneousComponent_eq_zero e Q he, mul_zero]

/-- **The determinant ideal is graded: exactness in the middle of the per-degree
sequence.** For `d ≥ N`, the degree-`d` slice of the determinant ideal `(det)` is
exactly the image under `mulDet` of the degree-`(d - N)` component:

  `(det) ∩ A_d = mulDet '' A_{d - N}`.

This is the kernel-equals-image statement of the right-`GL_N`-equivariant short
exact sequence `0 → A_{d-N} ⊗ χ → A_d → (A/det)_d → 0`: the cokernel of
`mulDet : A_{d-N} → A_d` is the degree-`d` part `A_d / (det · A_{d-N})` of the
quotient `A/det`. -/
theorem detSubmodule_inf_homogeneous (d : ℕ) (hd : N ≤ d) :
    detSubmodule k N ⊓ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d
      = (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k (d - N)).map (mulDet k N) := by
  have hNd : N + (d - N) = d := by omega
  apply le_antisymm
  · rintro x ⟨hxdet, hxhom⟩
    rw [← range_mulDet] at hxdet
    obtain ⟨Q, hQ⟩ := LinearMap.mem_range.1 hxdet
    rw [mulDet_apply] at hQ
    refine ⟨MvPolynomial.homogeneousComponent (d - N) Q,
      MvPolynomial.homogeneousComponent_mem _ _, ?_⟩
    rw [mulDet_apply, ← homogeneousComponent_detPoly_mul Q (d - N),
      hNd, hQ, MvPolynomial.homogeneousComponent_of_mem hxhom]
    simp
  · rintro y ⟨Q, hQ, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← range_mulDet]; exact ⟨Q, rfl⟩
    · refine (MvPolynomial.mem_homogeneousSubmodule d _).2 ?_
      rw [mulDet_apply]
      have h := detPoly_isHomogeneous.mul ((MvPolynomial.mem_homogeneousSubmodule (d - N) _).1 hQ)
      rwa [hNd] at h

end Etingof.PolyRightGrading

import EtingofRepresentationTheory.Chapter5.SchurWeylFormalCharacterIso

/-!
# Constituent-character extraction (Schur-Weyl character bookkeeping, issue #4962)

This file isolates the generic **constituent-character extraction** step used by the
`#4905` assembly of `quotDetRep_irreducible_constituent_lastWeight_zero`
(`CauchyDetQuotient.lean`).

The main result, `simple_constituent_formalCharacter_eq_schurPoly_mem`, says: if a finite
direct sum of simple summands (the abstract Schur-Weyl simples produced by
`decompose_polynomial_gl_rep`) carries a polynomial `GL_N(k)`-representation `M` whose formal
character is a nonnegative `ℕ`-combination of *distinct* Schur polynomials
`∑_{ν ∈ S} c_ν · S_ν`, then any **simple** `GL_N`-rep `L` admitting a `GL_N`-equivariant
injection into `M` has `formalCharacter L = S_ν` for some `ν ∈ S` with `c_ν > 0`.

## Proof route

1. **Decompose `M`.** `decompose_polynomial_gl_rep` (#2482) writes `M.asModule` as a finite
   `GL_N`-equivariant direct sum `⨁_{j : Fin p} (L_f j).asModule` of abstract simples, each
   schurPoly-classified: `formalCharacter (L_f j) = S_{lam_cl (f j)}` along an injective
   class assignment.
2. **Character match.** Pushing `formalCharacter` through the decomposition
   (`formalCharacter_directSum` + `formalCharacter_eq_of_rep_iso`) gives
   `formalCharacter M = ∑_j S_{lam_cl (f j)}`. Equating with the hypothesis
   `∑_{ν ∈ S} c_ν · S_ν` and using `schurPoly_linearIndependent`, the two coefficient
   `Finsupp`s agree.
3. **Locate `L`.** `L` embeds (as a simple submodule) into `⨁_j (L_f j).asModule`, so
   `isSimpleModule_iso_of_inj_into_directSum_simple` identifies `L ≅ L_f j₀` for some `j₀`,
   whence `formalCharacter L = S_{lam_cl (f j₀)}`.
4. **Conclude.** Evaluating the matched coefficient `Finsupp`s at `lam_cl (f j₀)`: the left
   side is `≥ 1` (the `j₀` summand contributes), so the right side
   `if lam_cl (f j₀) ∈ S then c_… else 0` is positive, forcing `lam_cl (f j₀) ∈ S` and
   `c_… > 0`.

The downstream consumer (`#4905`) applies this to `M = quotDetDegreeFDRep k N d`, whose
character is supported on partitions `ν` with `ν_N = 0`, to conclude the extracted `ν` has
`0 ∈ Set.range ν`.
-/

open CategoryTheory MvPolynomial DirectSum

noncomputable section

universe u

namespace Etingof.ConstituentCharacterExtraction

variable {R : Type*} [Ring R]

/-- A simple module admitting an injective `R`-linear map into a finite direct sum of simple
modules `⨁ i, L i` is isomorphic to one of the summands `L i`.

This is the single-summand specialisation of the isotypic-extraction lemma
`SemisimpleIsotypic.submodule_of_directSum_simple_iso_directSum`: the image of the injection
is a simple submodule of `⨁ i, L i`, hence isomorphic to one of the coordinate lines
`range (lof i) ≅ L i` (`Submodule.linearEquiv_of_le_sSup`). -/
theorem isSimpleModule_iso_of_inj_into_directSum_simple
    {ι : Type*} [Finite ι] (L : ι → Type*)
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)]
    (hsimp : ∀ i, IsSimpleModule R (L i))
    {T : Type*} [AddCommGroup T] [Module R T] [IsSimpleModule R T]
    (ψ : T →ₗ[R] DirectSum ι L) (hψ : Function.Injective ψ) :
    ∃ i, Nonempty (T ≃ₗ[R] L i) := by
  classical
  -- `T ≅ range ψ`, a simple submodule of `⨁ i, L i`.
  set Tsub : Submodule R (DirectSum ι L) := LinearMap.range ψ with hTsub
  have eT : T ≃ₗ[R] Tsub := LinearEquiv.ofInjective ψ hψ
  haveI : IsSimpleModule R Tsub := (LinearEquiv.isSimpleModule_iff eT).mp ‹_›
  -- The coordinate lines `range (lof i)` of the ambient direct sum.
  set cs : Set (Submodule R (DirectSum ι L)) :=
    Set.range (fun i => LinearMap.range (DirectSum.lof R ι L i)) with hcs
  have hlof_inj : ∀ i, Function.Injective (DirectSum.lof R ι L i) := fun i =>
    Function.LeftInverse.injective (g := DirectSum.component R ι L i)
      (fun b => DirectSum.component.lof_self R i b)
  -- Each coordinate line is simple (isomorphic to `L i`).
  have hcs_simple : ∀ m : cs, IsSimpleModule R (m : Submodule R (DirectSum ι L)) := by
    rintro ⟨m, i, rfl⟩
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hlof_inj i)).symm
  haveI := hcs_simple
  -- The coordinate lines span the whole module.
  have hcs_top : sSup cs = ⊤ := by
    rw [hcs, sSup_range]
    exact DFinsupp.iSup_range_lsingle
  have hTle : Tsub ≤ sSup cs := by rw [hcs_top]; exact le_top
  obtain ⟨m, hm, ⟨e'⟩⟩ := Tsub.linearEquiv_of_le_sSup cs hTle
  obtain ⟨i, rfl⟩ := hm
  exact ⟨i, ⟨eT.trans (e'.trans (LinearEquiv.ofInjective _ (hlof_inj i)).symm)⟩⟩

end Etingof.ConstituentCharacterExtraction

namespace Etingof

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- **Constituent-character extraction (issue #4962).** Let `M` be a polynomial
`GL_N(k)`-representation (algebraic, weight-space-spanning, homogeneous of degree `n`) whose
formal character is a nonnegative `ℕ`-combination of *distinct* Schur polynomials
`∑_{ν ∈ S} c_ν · S_ν`. Then any **simple** `GL_N(k)`-representation `L` that admits a
`GL_N`-equivariant injection into `M` has `formalCharacter L = S_ν` for some `ν ∈ S` with
`c_ν > 0`.

The `ν` here range over the antitone-weight subtype `{l : Fin N → ℕ // Antitone l}` (matching
the classification API `schurPoly_linearIndependent` / `decompose_polynomial_gl_rep`); a
consumer indexing `S` by `BoundedPartition` reads off `ν.parts := ν.val`. -/
theorem simple_constituent_formalCharacter_eq_schurPoly_mem (N n : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n)
    (S : Finset {l : Fin N → ℕ // Antitone l})
    (c : {l : Fin N → ℕ // Antitone l} → ℕ)
    (hchar : formalCharacter k N M = ∑ ν ∈ S, (c ν : ℚ) • schurPoly N ν.val)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k] M)
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = M.ρ g (φ v)) :
    ∃ ν ∈ S, 0 < c ν ∧ formalCharacter k N L = schurPoly N ν.val := by
  classical
  -- (1) Decompose `M.asModule` into abstract simples, schurPoly-classified.
  obtain ⟨ι, hιFin, hιDec, Lf, hLfsimp, ⟨lam_cl, lam_inj, hchar_cl⟩, p, f, ⟨eM⟩⟩ :=
    Etingof.PolynomialGLDecomposition.decompose_polynomial_gl_rep k N n M halg h_span h_homog
  -- (2) Push `formalCharacter` through the decomposition: `char M = ∑_j S_{lam_cl (f j)}`.
  have hφM : Representation.asModule M.ρ
      ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
        Representation.asModule (Representation.directSum (fun j : Fin p => (Lf (f j)).ρ)) :=
    eM ≪≫ₗ (Representation.asModule_directSum_equiv (fun j : Fin p => (Lf (f j)).ρ)).symm
  have hM_sum : formalCharacter k N M = ∑ j : Fin p, schurPoly N (lam_cl (f j)).val := by
    have hchar_eq : formalCharacter k N M
        = formalCharacter k N
          (FDRep.of (Representation.directSum (fun j : Fin p => (Lf (f j)).ρ))) := by
      have h0 := formalCharacter_eq_of_rep_iso k N M.ρ
        (Representation.directSum (fun j : Fin p => (Lf (f j)).ρ))
        (Representation.kEquivOfAsModuleEquiv hφM)
        (fun g v => Representation.kEquivOfAsModuleEquiv_intertwines hφM g v)
      rwa [formalCharacter_FDRep_of_ρ] at h0
    rw [hchar_eq,
      formalCharacter_directSum k N (fun j : Fin p => (Lf (f j) : Type u))
        (fun j : Fin p => (Lf (f j)).ρ)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [formalCharacter_FDRep_of_ρ, hchar_cl (f j)]
  -- (3) `L` embeds into `⨁_j (Lf (f j)).asModule`; simplicity pins `L ≅ Lf (f j₀)`.
  haveI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ) := hLsimp
  let φR : Representation.asModule L.ρ
      →ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)] Representation.asModule M.ρ :=
    Representation.asModuleHomOfIntertwiner φ hφ_equiv
  have hφRinj : Function.Injective φR := hφ_inj
  let ψ : Representation.asModule L.ρ
      →ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
        DirectSum (Fin p) (fun j => Representation.asModule (Lf (f j)).ρ) :=
    eM.toLinearMap ∘ₗ φR
  have hψinj : Function.Injective ψ := eM.injective.comp hφRinj
  obtain ⟨j₀, ⟨eLj⟩⟩ :=
    ConstituentCharacterExtraction.isSimpleModule_iso_of_inj_into_directSum_simple
      (R := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (fun j : Fin p => Representation.asModule (Lf (f j)).ρ)
      (fun j => hLfsimp (f j)) ψ hψinj
  set x : {l : Fin N → ℕ // Antitone l} := lam_cl (f j₀) with hx
  -- (4) `char L = S_{lam_cl (f j₀)} = S_x`.
  have hcharL : formalCharacter k N L = schurPoly N x.val := by
    have h0 := formalCharacter_eq_of_rep_iso k N L.ρ (Lf (f j₀)).ρ
      (Representation.kEquivOfAsModuleEquiv eLj)
      (fun g v => Representation.kEquivOfAsModuleEquiv_intertwines eLj g v)
    rw [formalCharacter_FDRep_of_ρ, formalCharacter_FDRep_of_ρ] at h0
    rw [h0, hchar_cl (f j₀)]
  -- (5) Match coefficient `Finsupp`s via `schurPoly_linearIndependent`, then read off at `x`.
  have hcoeff : (∑ j : Fin p, Finsupp.single (lam_cl (f j)) (1 : ℚ))
      = ∑ ν ∈ S, Finsupp.single ν (c ν : ℚ) := by
    apply schurPoly_linearIndependent N
    rw [map_sum, map_sum]
    simp only [Finsupp.linearCombination_single, one_smul]
    rw [← hM_sum, hchar]
  have hLHSpos : 0 < (∑ j : Fin p, Finsupp.single (lam_cl (f j)) (1 : ℚ)) x := by
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_pos' (fun j _ => ?_) ⟨j₀, Finset.mem_univ _, ?_⟩
    · rw [Finsupp.single_apply]; split <;> norm_num
    · rw [Finsupp.single_apply, if_pos hx.symm]; norm_num
  rw [hcoeff, Finsupp.finset_sum_apply] at hLHSpos
  simp only [Finsupp.single_apply] at hLHSpos
  rw [Finset.sum_ite_eq' S x (fun ν => (c ν : ℚ))] at hLHSpos
  by_cases hxS : x ∈ S
  · rw [if_pos hxS] at hLHSpos
    exact ⟨x, hxS, by exact_mod_cast hLHSpos, hcharL⟩
  · rw [if_neg hxS] at hLHSpos
    exact absurd hLHSpos (lt_irrefl 0)

end Etingof

end

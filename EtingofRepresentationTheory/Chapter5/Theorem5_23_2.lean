import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_23_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Theorem5_23_2Core
import EtingofRepresentationTheory.Chapter5.PolynomialGLSemisimple
import EtingofRepresentationTheory.Chapter5.DetClearing
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep

/-!
# Theorem 5.23.2: Complete Reducibility and Peter-Weyl for GL(V)

(i) Every finite dimensional algebraic representation of GL(V) is completely
reducible and decomposes into summands Lλ (which are pairwise nonisomorphic).

(ii) (Peter-Weyl for GL(V)) The algebra R of polynomial functions on GL(V),
as a representation of GL(V) × GL(V), decomposes as:
  R ≅ ⊕_λ L*λ ⊗ Lλ

## Mathlib correspondence

Complete reducibility for semisimple groups is partially in Mathlib.
The Peter-Weyl decomposition for GL(V) is not.
-/

open CategoryTheory
open scoped TensorProduct

noncomputable section

namespace Etingof

open Etingof.KernelLemmaKPrime

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-- **Theorem 5.23.2 (i)**: Every finite-dimensional algebraic representation of
`GL_n(k)` is completely reducible. That is, if `ρ` is an algebraic representation
of `GL_n(k)` on a finite-dimensional `k`-vector space `Y`, then `Y` decomposes as
a direct sum of irreducible subrepresentations.

This is stated faithfully as semisimplicity of `Y` **as a module over the group
algebra `k[GL_n(k)]`** — i.e. semisimplicity of the representation `ρ`, which is
the precise meaning of "completely reducible". This is genuine `GL_n`-equivariant
content: the group algebra `k[GL_n(k)]` is *not* a semisimple ring (`GL_n(k)` is
infinite), so this is NOT automatic for an arbitrary module; it holds precisely
because the representation is *algebraic*.

(Contrast the previous formalization, which asserted only `IsSemisimpleModule k Y`
— semisimplicity of `Y` as a plain `k`-vector space — which is trivially true for
*any* vector space over a field and carries no representation-theoretic content.)

**Proof (Etingof, §5.23).** There is an equivariant embedding `ξ : Y → Y ⊗ R`,
`⟨u, ξ(v)⟩(g) = u(g v)` for `u ∈ Y*` (with trivial `GL`-action on the first
tensor factor), so it suffices to treat a subrepresentation `Y ⊆ Rᵐ`. Every
element of `R = k[gᵢⱼ][1/det]` is a polynomial in `gᵢⱼ` times a nonpositive power
of `det(g)`, so `R` is a quotient of a direct sum of representations
`Sʳ(V ⊗ V*) ⊗ (∧ᴺ V*)^{⊗s}` (trivial `GL`-action on the `V*` factor). Hence `Y`
embeds into a direct sum of representations `V^{⊗n} ⊗ (∧ᴺ V*)^{⊗s}`, each of which
is completely reducible by Schur-Weyl duality (Theorem 5.18.4 / 5.22.1); a
subrepresentation of a semisimple module is semisimple, so `Y` is semisimple.

The finer statement of the book — that the irreducible summands are the `Lλ` and
are pairwise nonisomorphic — is the highest-weight classification, which requires
the GL-rep classification infrastructure (cf. `iso_of_formalCharacter_eq_schurPoly`)
and is tracked separately.

**Formalized proof.** Rather than the embedding-into-`Sʳ(V ⊗ V*)` argument above
(which is one valid route), this discharges complete reducibility through the
`det`-twist reduction to the polynomial case:

1. *det-clearing* (`IsAlgebraicRepresentation.exists_detPow_twist_isPolynomial`):
   some power `s` makes the twist `g ↦ det(g)^s • ρ(g)` a *polynomial*
   (`det⁻¹`-free) representation.
2. The twist is the genuine representation `charTwistRep (det^s) ρ`.
3. *homogeneous splitting + decompose* (`polynomialRep_isSemisimple`): a
   polynomial `GL_N`-representation is semisimple as a `k[GL_N]`-module (split into
   total-degree components, each handled by `decompose_polynomial_gl_rep`).
4. *untwist* (`isSemisimpleModule_charTwistRep`): twisting back by `det^{-s}`
   (a one-dimensional character) preserves semisimplicity, and
   `det^{-s} · det^s = 1` recovers `ρ`.

`k` is fixed at universe `0` here (e.g. `ℂ`), matching the polynomial-decomposition
machinery (`decompose_polynomial_gl_rep`) it is built on.
(Etingof Theorem 5.23.2, part i) -/
theorem Theorem5_23_2_i
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ)
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : Etingof.IsAlgebraicRepresentation n ⇑ρ) :
    IsSemisimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule := by
  classical
  -- Step 1 (det-clearing): some `det^s`-twist of `ρ` is a polynomial representation.
  obtain ⟨s, hpoly⟩ := halg.exists_detPow_twist_isPolynomial
  -- Step 2: realize the twist as the genuine representation `charTwistRep (det^s) ρ`.
  have hcoe : ⇑(charTwistRep (detChar k n ^ s) ρ)
      = fun g => ((Matrix.GeneralLinearGroup.det g : k) ^ s) • ρ g := by
    funext g
    show ((detChar k n ^ s) g : k) • ρ g = _
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  have hpoly_tw : IsPolynomialRepresentation n ⇑(charTwistRep (detChar k n ^ s) ρ) := by
    rw [hcoe]; exact hpoly
  -- Steps 3-4 (homogeneous splitting + decompose): the polynomial twist is semisimple.
  have hss_tw : IsSemisimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (charTwistRep (detChar k n ^ s) ρ).asModule := by
    have h := PolynomialGLSemisimple.polynomialRep_isSemisimple k n
      (FDRep.of (charTwistRep (detChar k n ^ s) ρ))
      (by rw [FDRep.of_ρ']; exact hpoly_tw)
    rwa [FDRep.of_ρ'] at h
  -- Step 5 (untwist): twisting back by `det^{-s}` recovers `ρ`, preserving semisimplicity.
  have huntwist : charTwistRep (detChar k n ^ s)⁻¹
      (charTwistRep (detChar k n ^ s) ρ) = ρ := by
    ext g v
    rw [charTwistRep_apply, charTwistRep_apply, smul_smul, ← Units.val_mul,
      ← MonoidHom.mul_apply, inv_mul_cancel, MonoidHom.one_apply, Units.val_one, one_smul]
  have hfin := isSemisimpleModule_charTwistRep (detChar k n ^ s)⁻¹
    (charTwistRep (detChar k n ^ s) ρ) (hss := hss_tw)
  rwa [huntwist] at hfin

/-- The coordinate ring of `GL_n(k)`: the polynomial ring `k[Xᵢⱼ, D]` where `D`
represents `1/det`. This models the algebra `R` of regular (polynomial) functions
on `GL_n(k)`. -/
noncomputable abbrev GLCoordinateRing (n : ℕ) (k : Type*) [Field k] :=
  MvPolynomial (GLCoordVars n) k


/-- **Theorem 5.23.2 (ii)** (Peter-Weyl for GL(V)): The coordinate ring `R` of
`GL_n(k)`, as a representation of `GL_n(k) × GL_n(k)` via `(g,h) · φ(x) = φ(g⁻¹xh)`,
decomposes as `R ≅ ⊕_λ L*_λ ⊗ L_λ`, where the sum ranges over all dominant weights
`λ = (λ₁ ≥ ⋯ ≥ λ_n)` with `λᵢ ∈ ℤ`, and `L*_λ` is the contragredient of `L_λ`.

**Superseded by the genuine equivariant statement.** The genuine
`GL_n × GL_n`-equivariant Peter-Weyl isomorphism is now
`Theorem5_23_2_ii_equivariant` in `Chapter5.Theorem5_23_2_PeterWeyl` (#5396): it
intertwines the left/right translation bi-action on `R = k[gᵢⱼ][1/det]`
(`localBiRep`) with the action on `⊕_λ L*_λ ⊗ L_λ` (`peterWeylRHS`). The bare
rank iso below is retained only as scaffolding.

**⚠ Partial formalization.** The statement below asserts only a *bare `k`-linear*
isomorphism `R ≃ₗ[k] ⊕_λ L*_λ ⊗ L_λ`, proved by matching ranks
(`nonempty_linearEquiv_of_rank_eq`): both sides are countably-infinite-dimensional
free `k`-modules for `n ≥ 1`, so this iso holds for *any* two such modules and
carries **no** `GL_n × GL_n`-equivariant content — the actual mathematical theorem.
Capturing the full Peter-Weyl decomposition (a `GL_n × GL_n`-equivariant iso)
requires representation structures that do not yet exist in the project: a
`GL_n × GL_n`-action on the *localized* coordinate ring `k[gᵢⱼ][1/det]` (including
the `1/det` variable, on which `(g,h)` acts by `det(g)/det(h)`), the GL-action on
each `Lλ` / `L*_λ` (the det-twisted `schurModuleRep`), and the matching
`GL_n × GL_n`-action on the direct sum. This equivariant strengthening is tracked
as a follow-up issue (the rank iso below is retained only as scaffolding for it).
(Etingof Theorem 5.23.2, part ii) -/
-- The rank of the coordinate ring `k[GL_n]` equals the rank of the direct sum
-- `⊕_λ L*_λ ⊗ L_λ` over all dominant weights. Both sides are free `k`-modules;
-- for `n ≥ 1` both are countably-infinite-dimensional (the LHS has basis indexed
-- by monomials in `n² + 1` variables, the RHS by a countable union of finite bases).
-- Note: For `n = 0` the formalization of `GLCoordinateRing` includes a spurious
-- variable for `1/det` that is mathematically redundant, making the LHS
-- infinite-dimensional while the RHS is 1-dimensional. The statement as formalized
-- is only correct for `n ≥ 1`.

-- The coordinate ring has rank ℵ₀: its monomial basis is indexed by the countably
-- infinite type `(GLCoordVars n →₀ ℕ)` (GLCoordVars n is finite nonempty).
private theorem glCoordinateRing_rank (n : ℕ) :
    Module.rank k (GLCoordinateRing n k) = Cardinal.aleph0 := by
  haveI : Nonempty (GLCoordVars n) := ⟨Sum.inr ()⟩
  haveI : Infinite (GLCoordVars n →₀ ℕ) :=
    @Finsupp.infinite_of_right (GLCoordVars n) ℕ _ _ ⟨Sum.inr ()⟩
  have hcard : Cardinal.mk (GLCoordVars n →₀ ℕ) = Cardinal.aleph0 := Cardinal.mk_eq_aleph0 _
  have hbasis := (MvPolynomial.basisMonomials (GLCoordVars n) k).mk_eq_rank
  rw [hcard, Cardinal.lift_aleph0, Cardinal.lift_id'] at hbasis
  exact hbasis.symm

-- The direct sum ⊕_λ L*_λ ⊗ L_λ has rank ≤ ℵ₀: DominantWeight n is countable and
-- each summand is finite-dimensional.
set_option maxHeartbeats 400000 in
-- Heartbeat increase needed for cardinal arithmetic in calc chain
private theorem directSum_rank_le_aleph0 (n : ℕ) :
    Module.rank k (DirectSum (DominantWeight n) fun lam =>
      (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) ≤ Cardinal.aleph0 := by
  set F := fun lam : DominantWeight n =>
    (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)
  rw [rank_directSum]
  -- Upper bound: sum of ranks ≤ #ι * sup(ranks) ≤ ℵ₀ * ℵ₀ = ℵ₀
  have h_sup : ⨆ lam : DominantWeight n, Module.rank k (F lam) ≤ Cardinal.aleph0 := by
    apply ciSup_le'
    intro lam
    haveI : Module.Finite k (AlgIrrepGLDual n lam k) :=
      AlgIrrepGL.finite n lam.w0Twist k
    haveI : Module.Finite k (AlgIrrepGL n lam k) :=
      AlgIrrepGL.finite n lam k
    exact (Module.rank_lt_aleph0 k (F lam)).le
  calc Cardinal.sum (fun lam => Module.rank k (F lam))
      -- v4.29.0: Cardinal.sum_le_iSup_lift renamed to Cardinal.sum_le_lift_mk_mul_iSup_lift
      ≤ _ := Cardinal.sum_le_lift_mk_mul_iSup_lift _
    _ ≤ Cardinal.aleph0 * Cardinal.aleph0 := by
        apply mul_le_mul'
        · rw [Cardinal.lift_le_aleph0]; exact Cardinal.mk_le_aleph0
        -- v4.29.0: the new lemma's RHS supremum carries an identity `lift.{0,u}`; rewrite it away.
        · have hlift : (fun i => Cardinal.lift.{0} (Module.rank k (F i))) =
              fun lam => Module.rank k (F lam) := by
            funext lam; exact Cardinal.lift_id' _
          rw [hlift]; exact h_sup
    _ = Cardinal.aleph0 := Cardinal.aleph0_mul_aleph0

-- The one-row dominant weight (m, 0, ..., 0) : DominantWeight n
private def oneRowWeight (n : ℕ) (m : ℕ) (hn : 0 < n) : DominantWeight n :=
  ⟨fun i => if i = ⟨0, hn⟩ then (m : ℤ) else 0, by
    intro i j hij
    by_cases hi : i = ⟨0, hn⟩ <;> by_cases hj : j = ⟨0, hn⟩ <;> simp [hi, hj]
    exfalso; apply hi; subst hj
    exact Fin.ext (show i.val = 0 by exact Nat.le_zero.mp hij)⟩

private theorem oneRowWeight_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (oneRowWeight n · hn) := by
  intro m₁ m₂ h
  have := congr_arg (fun w : DominantWeight n => w.val ⟨0, hn⟩) h
  simp [oneRowWeight] at this
  exact_mod_cast this

private theorem oneRowWeight_shift (n : ℕ) (m : ℕ) (hn : 0 < n) :
    (oneRowWeight n m hn).shift = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [DominantWeight.shift, oneRowWeight]
    -- The last entry of the weight: if Fin.last n = ⟨0, hn⟩ then m else 0
    split_ifs with h
    · -- n = 0 case: last entry is m, shift = (-m).toNat = 0 (since m : ℕ cast to ℤ ≥ 0)
      simp
    · -- n ≥ 1 case: last entry is 0, shift = (-0).toNat = 0
      simp

private theorem oneRowWeight_toNatWeight (n : ℕ) (m : ℕ) (hn : 0 < n) :
    (oneRowWeight n m hn).toNatWeight = fun i => if i = ⟨0, hn⟩ then m else 0 := by
  ext i
  simp only [DominantWeight.toNatWeight, oneRowWeight]
  have : DominantWeight.shift (oneRowWeight n m hn) = 0 := oneRowWeight_shift n m hn
  unfold oneRowWeight at this
  rw [this]
  split_ifs <;> simp

-- The direct sum ⊕_λ L*_λ ⊗ L_λ has rank ≥ ℵ₀: for n ≥ 1, every summand is
-- nontrivial (the Schur module for any partition with ≤ n parts on k^n is nonzero
-- in characteristic 0), and `DominantWeight n` is infinite.
set_option maxHeartbeats 800000 in
private theorem directSum_rank_ge_aleph0 [CharZero k] (n : ℕ) (hn : 0 < n) :
    Cardinal.aleph0 ≤ Module.rank k (DirectSum (DominantWeight n) fun lam =>
      (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) := by
  set F := fun lam : DominantWeight n =>
    (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)
  -- For each m : ℕ, the summand at oneRowWeight n m hn is nonzero
  -- First show AlgIrrepGL n lam k is nonzero for one-row weights
  have hne : ∀ m : ℕ, Nontrivial (AlgIrrepGL n (oneRowWeight n m hn) k) := by
    intro m
    -- toNatWeight is antitone (follows from the ℤ-valued weight being antitone)
    have hanti : Antitone (oneRowWeight n m hn).toNatWeight := by
      rw [oneRowWeight_toNatWeight]
      intro i j hij
      by_cases hi : i = ⟨0, hn⟩ <;> by_cases hj : j = ⟨0, hn⟩ <;> simp [hi, hj]
      exfalso; apply hi; subst hj
      exact Fin.ext (show i.val = 0 by exact Nat.le_zero.mp hij)
    have hbot := schurModuleSubmodule_ne_bot (k := k) n (oneRowWeight n m hn).toNatWeight hanti
    rw [ne_eq, ← Submodule.subsingleton_iff_eq_bot] at hbot
    exact not_subsingleton_iff_nontrivial.mp hbot
  rw [rank_directSum]
  -- The sum ∑_λ rank(F λ) ≥ ℵ₀ because there are ℵ₀ many distinct one-row weights,
  -- each giving a nontrivial summand (rank ≥ 1).
  -- Step 1: Each summand at a one-row weight has rank ≥ 1
  have h1 : ∀ m : ℕ, 1 ≤ Module.rank k (F (oneRowWeight n m hn)) := by
    intro m
    haveI := hne m
    -- AlgIrrepGLDual is also nontrivial (it's a SchurModule for the w0-twisted weight)
    haveI : Nontrivial (AlgIrrepGLDual n (oneRowWeight n m hn) k) := by
      have hanti : Antitone (oneRowWeight n m hn).w0Twist.toNatWeight := by
        intro i j hij
        -- Antitone: i ≤ j → f j ≤ f i
        -- Goal: w0Twist.toNatWeight j ≤ w0Twist.toNatWeight i
        unfold DominantWeight.w0Twist DominantWeight.toNatWeight
        apply Int.toNat_le_toNat
        gcongr
        simp only [neg_le_neg_iff]
        -- Need: lam(i.rev) ≤ lam(j.rev), i.e., lam at the rev-image of i ≤ that of j
        -- Since i ≤ j, j.rev ≤ i.rev, and lam is antitone
        exact (oneRowWeight n m hn).property (Fin.rev_anti hij)
      exact not_subsingleton_iff_nontrivial.mp
        ((ne_eq .. ▸ Submodule.subsingleton_iff_eq_bot.not).mpr
          (schurModuleSubmodule_ne_bot (k := k) n _ hanti))
    exact Cardinal.one_le_iff_ne_zero.mpr (rank_pos (R := k)).ne'
  -- Step 2: The cardinal sum over all dominant weights is ≥ the sum over one-row weights
  -- ∑_{λ : DW} rank(F λ) ≥ ∑_{m : ℕ} rank(F(oneRowWeight n m hn)) ≥ ∑_{m:ℕ} 1 = ℵ₀
  calc Cardinal.aleph0
      = Cardinal.sum (fun _ : ℕ => (1 : Cardinal)) := by simp
    _ ≤ Cardinal.sum (fun m : ℕ => Module.rank k (F (oneRowWeight n m hn))) :=
        Cardinal.sum_le_sum _ _ h1
    _ ≤ Cardinal.sum (fun lam => Module.rank k (F lam)) := by
        -- Sub-sum ≤ full sum via the injection oneRowWeight
        rw [Cardinal.sum, Cardinal.sum]
        exact ⟨⟨fun ⟨m, x⟩ => ⟨oneRowWeight n m hn, x⟩, fun ⟨m₁, x₁⟩ ⟨m₂, x₂⟩ h => by
          simp only [Sigma.mk.inj_iff] at h
          obtain ⟨hm, hx⟩ := h
          have hm' := oneRowWeight_injective n hn hm
          subst hm'
          exact Sigma.ext rfl (by exact hx)⟩⟩

private theorem peterWeyl_rank_eq [CharZero k] (n : ℕ) (hn : 0 < n) :
    Module.rank k (GLCoordinateRing n k) =
      Module.rank k (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k)) := by
  rw [glCoordinateRing_rank]
  exact le_antisymm (directSum_rank_le_aleph0 n) (directSum_rank_ge_aleph0 n hn) |>.symm

theorem Theorem5_23_2_ii [CharZero k]
    (n : ℕ) (hn : 0 < n) :
    Nonempty (GLCoordinateRing n k ≃ₗ[k]
      (DirectSum (DominantWeight n) fun lam =>
        (AlgIrrepGLDual n lam k ⊗[k] AlgIrrepGL n lam k))) :=
  nonempty_linearEquiv_of_rank_eq (peterWeyl_rank_eq n hn)

end Etingof

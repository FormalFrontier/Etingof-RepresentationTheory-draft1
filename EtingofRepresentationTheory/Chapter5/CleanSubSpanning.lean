import EtingofRepresentationTheory.Chapter5.CleanFormalCharacterAdditivity
import EtingofRepresentationTheory.Chapter5.FormalCharacterTorusTrace

/-!
# DetInvElim-clean sub-of-spanning-is-spanning (issue #5086, parent #5081 / #5078)

The constituent-character extractor peels a `GL_N`-invariant submodule `S ≤ M` off a
weight-spanning algebraic `FDRep` `M` and applies the short-exact-sequence additivity
`formalCharacter_add_of_shortExact`. That additivity needs **both** the total `M` and the
sub `S` to be ℕ-weight-spanning. The total-spanning is threaded through the induction;
the sub-spanning is the technical crux discharged here.

The genuine mathematical content (independent of the `subFDRep` packaging that lives in the
sibling `CleanInductionHelpers.lean`, #5081) is:

> For a torus-invariant submodule `R ≤ M` of a weight-spanning `FDRep` `M`, the weight
> spaces of `M` *cut down to `R`* still span `R`:  `⨆_μ (M_μ ⊓ R) = R`.

Via the clean `glWeightSpace_inf_range` (in `CleanFormalCharacterAdditivity.lean`) this is
exactly equivalent to "the sub-representation on `R` is weight-spanning", which is the
`hStop` consumed by `formalCharacter_add_of_invariant_submodule`. The `subFDRep`-level
wrapper `subFDRep_weight_spanning` is the trivial `glWeightSpace_inf_range` glue and is
added in `CleanInductionHelpers.lean` once `subFDRep` lands; it consumes the main theorem
`torusInvariant_iSup_inf_glWeightSpace_eq` below.

## Mechanism (single generic diagonal element)

The submodule lattice is **not** distributive, so `inf_iSup_eq` does not apply — the
eigenspace/invariance structure is essential. We pick a single diagonal torus element
`diag(t)` whose torus characters `χ_μ(t) = ∏_i (t i)^{μ i}` are pairwise distinct over the
finite weight support (`exists_separating_torus`). Each weight space `M_μ` is then exactly
the generalised eigenspace of `f := M.ρ (diag t)` at the eigenvalue `χ_μ(t)`
(`genEigenspace_diagTorus_eq_glWeightSpace`), and off the character set the generalised
eigenspaces vanish (`genEigenspace_diagTorus_eq_bot`). Since `R` is `f`-invariant, Mathlib's
`Submodule.eq_iSup_inf_genEigenspace` decomposes `R = ⨆_λ (R ⊓ f.genEigenspace λ)`, and the
per-eigenvalue pieces match the weight pieces.
-/

open MvPolynomial

namespace Etingof.CleanCharExtraction

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-- The torus character `χ_μ(t) = ∏_i (t i)^{μ i}` of a weight `μ` at a torus tuple `t`. -/
private def torusChar (N : ℕ) (t : Fin N → kˣ) (μ : Fin N →₀ ℕ) : k :=
  ∏ i, (t i : k) ^ (μ i)

/-- **Squeeze for independent families.** If `A i ≤ B i` termwise, the `B i` are
sup-independent, and the two families have the same supremum, then they agree termwise.
Pure lattice fact (modular law + independence); no finite-dimensionality needed. -/
private theorem eq_of_le_of_iSupIndep_of_iSup_eq {M' : Type*} [AddCommGroup M'] [Module k M']
    {ι : Type*} {A B : ι → Submodule k M'} (hAB : ∀ i, A i ≤ B i) (hB : iSupIndep B)
    (hsup : ⨆ i, A i = ⨆ i, B i) (i : ι) : A i = B i := by
  refine le_antisymm (hAB i) ?_
  have hBi_le : B i ≤ ⨆ j, A j := hsup ▸ le_iSup B i
  have hdisj := (iSupIndep_def.mp hB) i
  calc B i = B i ⊓ ⨆ j, A j := (inf_eq_left.mpr hBi_le).symm
    _ ≤ B i ⊓ (A i ⊔ ⨆ (j) (_ : j ≠ i), A j) := by
        refine inf_le_inf_left _ (iSup_le fun j => ?_)
        rcases eq_or_ne j i with rfl | hj
        · exact le_sup_left
        · exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ i) => A j) j hj)
    _ = A i ⊔ (⨆ (j) (_ : j ≠ i), A j) ⊓ B i := by
        rw [inf_comm]; exact sup_inf_assoc_of_le _ (hAB i)
    _ ≤ A i ⊔ ⊥ := by
        refine sup_le_sup_left ?_ _
        refine le_trans (inf_le_inf_right (B i) (iSup₂_mono fun j _ => hAB j)) ?_
        rw [inf_comm]; exact disjoint_iff_inf_le.mp hdisj
    _ = A i := by simp

/-- Base-`B` positional representation is injective on tuples with all coordinates `< B`. -/
private theorem sum_base_pow_injOn {B : ℕ} (hB : 1 ≤ B) :
    ∀ {n : ℕ} (f g : Fin n → ℕ), (∀ i, f i < B) → (∀ i, g i < B) →
      (∑ i : Fin n, B ^ (i : ℕ) * f i) = (∑ i : Fin n, B ^ (i : ℕ) * g i) → f = g := by
  intro n
  induction n with
  | zero => intro f g _ _ _; funext i; exact i.elim0
  | succ n ih =>
      intro f g hf hg h
      have key : ∀ (p : Fin (n + 1) → ℕ),
          (∑ i : Fin (n + 1), B ^ (i : ℕ) * p i)
            = p 0 + B * ∑ i : Fin n, B ^ (i : ℕ) * p i.succ := by
        intro p
        rw [Fin.sum_univ_succ]
        congr 1
        · simp
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Fin.val_succ, pow_succ']; ring
      rw [key f, key g] at h
      have h0 : f 0 = g 0 := by
        have e1 : (f 0 + B * ∑ i : Fin n, B ^ (i : ℕ) * f i.succ) % B = f 0 := by
          rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (hf 0)
        have e2 : (g 0 + B * ∑ i : Fin n, B ^ (i : ℕ) * g i.succ) % B = g 0 := by
          rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (hg 0)
        rw [← e1, ← e2, h]
      rw [h0] at h
      have hSfg : (∑ i : Fin n, B ^ (i : ℕ) * f i.succ)
          = ∑ i : Fin n, B ^ (i : ℕ) * g i.succ :=
        Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h)
      have htail := ih (fun i => f i.succ) (fun i => g i.succ)
        (fun i => hf i.succ) (fun i => hg i.succ) hSfg
      funext i
      exact Fin.cases h0 (fun j => congrFun htail j) i

/-- **A separating diagonal torus element exists.** Over the infinite field `k` there is a
torus tuple `t` whose characters `χ_μ(t)` are pairwise distinct over the finite set of
weights with nonzero weight space. We take `t i = 2^(B^i)` for a base `B` exceeding every
coordinate of a supported weight; then `χ_μ(t) = 2^(∑ μ_i B^i)`, and the base-`B` encodings
are distinct, while `2` has infinite multiplicative order (`CharZero`). -/
theorem exists_separating_torus (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) :
    ∃ t : Fin N → kˣ, Set.InjOn (torusChar N t)
      {μ : Fin N →₀ ℕ | glWeightSpace k N M (fun i => μ i) ≠ ⊥} := by
  classical
  have hpow2 : Function.Injective (fun n : ℕ => (2 : k) ^ n) := by
    have h2 : (2 : k) = ((2 : ℕ) : k) := by norm_num
    intro a b h
    simp only [h2, ← Nat.cast_pow] at h
    exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h)
  set S := (glWeightSpace_finite_support k N M).toFinset with hS
  set B := (S.sup fun μ => ∑ i, μ i) + 1 with hBdef
  have hB1 : 1 ≤ B := Nat.le_add_left 1 _
  have hbound : ∀ μ ∈ S, ∀ i, μ i < B := by
    intro μ hμ i
    have h1 : μ i ≤ ∑ j, μ j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : (∑ j, μ j) ≤ S.sup fun μ => ∑ i, μ i :=
      Finset.le_sup (f := fun μ : Fin N →₀ ℕ => ∑ i, μ i) hμ
    omega
  set u : kˣ := Units.mk0 (2 : k) (by norm_num) with hu
  have huval : (u : k) = 2 := by rw [hu]; rfl
  have hchar : ∀ ρ : Fin N →₀ ℕ,
      torusChar N (fun i => u ^ (B ^ (i : ℕ))) ρ
        = (2 : k) ^ (∑ i : Fin N, B ^ (i : ℕ) * ρ i) := by
    intro ρ
    have hterm : ∀ i : Fin N,
        ((u ^ (B ^ (i : ℕ)) : kˣ) : k) ^ (ρ i) = (2 : k) ^ (B ^ (i : ℕ) * ρ i) := by
      intro i
      rw [Units.val_pow_eq_pow_val, huval, ← pow_mul]
    simp only [torusChar, hterm]
    rw [Finset.prod_pow_eq_pow_sum]
  refine ⟨fun i => u ^ (B ^ (i : ℕ)), ?_⟩
  intro μ hμ ν hν hμν
  rw [Set.mem_setOf_eq] at hμ hν
  have hμS : μ ∈ S := (glWeightSpace_finite_support k N M).mem_toFinset.mpr hμ
  have hνS : ν ∈ S := (glWeightSpace_finite_support k N M).mem_toFinset.mpr hν
  rw [hchar μ, hchar ν] at hμν
  have hE : (∑ i : Fin N, B ^ (i : ℕ) * μ i) = ∑ i : Fin N, B ^ (i : ℕ) * ν i := hpow2 hμν
  have hfun : (fun i => μ i) = (fun i => ν i) :=
    sum_base_pow_injOn hB1 (fun i => μ i) (fun i => ν i)
      (fun i => hbound μ hμS i) (fun i => hbound ν hνS i) hE
  exact Finsupp.ext fun i => congrFun hfun i

/-- Every weight vector of weight `μ` is an eigenvector of `M.ρ (diag t)` with eigenvalue
`χ_μ(t)`, so the weight space sits inside the generalised eigenspace. -/
theorem glWeightSpace_le_genEigenspace_diagTorus (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (t : Fin N → kˣ) (μ : Fin N →₀ ℕ) :
    glWeightSpace k N M (fun i => μ i)
      ≤ Module.End.genEigenspace (M.ρ (Etingof.diagTorus k N t)) (torusChar N t μ) ⊤ := by
  intro v hv
  have hev : M.ρ (Etingof.diagTorus k N t) v = torusChar N t μ • v := by
    simpa [torusChar] using Etingof.glWeightSpace_diagTorus_apply M (fun i => μ i) t hv
  exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hev)

/-- **Diagonalisation (matching).** For a separating torus, the generalised eigenspace of
`f := M.ρ (diag t)` at the character `χ_ν(t)` is exactly the weight space `M_ν`. -/
theorem genEigenspace_diagTorus_eq_glWeightSpace (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (t : Fin N → kˣ)
    (hinj : Set.InjOn (torusChar N t)
      {μ : Fin N →₀ ℕ | glWeightSpace k N M (fun i => μ i) ≠ ⊥})
    (hMtop : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N M (fun i => μ i) = ⊤)
    (ν : Fin N →₀ ℕ) (hν : glWeightSpace k N M (fun i => ν i) ≠ ⊥) :
    Module.End.genEigenspace (M.ρ (Etingof.diagTorus k N t)) (torusChar N t ν) ⊤
      = glWeightSpace k N M (fun i => ν i) := by
  classical
  set fop : Module.End k M := M.ρ (Etingof.diagTorus k N t) with hfop
  set A : {μ : Fin N →₀ ℕ // glWeightSpace k N M (fun i => μ i) ≠ ⊥} → Submodule k M :=
    fun μ => glWeightSpace k N M (fun i => μ.val i) with hA
  set B : {μ : Fin N →₀ ℕ // glWeightSpace k N M (fun i => μ i) ≠ ⊥} → Submodule k M :=
    fun μ => fop.genEigenspace (torusChar N t μ.val) ⊤ with hB
  have hAB : ∀ μ, A μ ≤ B μ := fun μ =>
    glWeightSpace_le_genEigenspace_diagTorus N M t μ.val
  have hcinj : Function.Injective
      (fun μ : {μ : Fin N →₀ ℕ // glWeightSpace k N M (fun i => μ i) ≠ ⊥} =>
        torusChar N t μ.val) := by
    intro μ₁ μ₂ h
    exact Subtype.ext (hinj μ₁.2 μ₂.2 h)
  have hBindep : iSupIndep B := (Module.End.independent_genEigenspace fop ⊤).comp hcinj
  have hAsup : ⨆ μ, A μ = ⊤ := by
    rw [eq_top_iff, ← hMtop]
    refine iSup_le fun μ => ?_
    by_cases hμ : glWeightSpace k N M (fun i => μ i) = ⊥
    · rw [hμ]; exact bot_le
    · exact le_iSup A ⟨μ, hμ⟩
  have hBsup : ⨆ μ, B μ = ⊤ := by rw [eq_top_iff, ← hAsup]; exact iSup_mono hAB
  have hsup : ⨆ μ, A μ = ⨆ μ, B μ := by rw [hAsup, hBsup]
  exact (eq_of_le_of_iSupIndep_of_iSup_eq hAB hBindep hsup ⟨ν, hν⟩).symm

/-- **Vanishing off the character set.** For a separating torus, the generalised eigenspace
of `f := M.ρ (diag t)` at any value that is not a character of a supported weight is `⊥`. -/
theorem genEigenspace_diagTorus_eq_bot (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (t : Fin N → kˣ)
    (hinj : Set.InjOn (torusChar N t)
      {μ : Fin N →₀ ℕ | glWeightSpace k N M (fun i => μ i) ≠ ⊥})
    (hMtop : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N M (fun i => μ i) = ⊤)
    (lam : k)
    (hlam : ∀ ν : Fin N →₀ ℕ, glWeightSpace k N M (fun i => ν i) ≠ ⊥ → torusChar N t ν ≠ lam) :
    Module.End.genEigenspace (M.ρ (Etingof.diagTorus k N t)) lam ⊤ = ⊥ := by
  classical
  set fop : Module.End k M := M.ρ (Etingof.diagTorus k N t) with hfop
  -- The generalised eigenspaces at the *supported* characters already span ⊤ (via H1).
  have hGtop : (⨆ ν : {μ : Fin N →₀ ℕ // glWeightSpace k N M (fun i => μ i) ≠ ⊥},
      fop.genEigenspace (torusChar N t ν.val) ⊤) = ⊤ := by
    have h1 : ∀ ν : {μ : Fin N →₀ ℕ // glWeightSpace k N M (fun i => μ i) ≠ ⊥},
        fop.genEigenspace (torusChar N t ν.val) ⊤ = glWeightSpace k N M (fun i => ν.val i) :=
      fun ν => genEigenspace_diagTorus_eq_glWeightSpace N M t hinj hMtop ν.val ν.2
    calc (⨆ ν : {μ : Fin N →₀ ℕ // glWeightSpace k N M (fun i => μ i) ≠ ⊥},
            fop.genEigenspace (torusChar N t ν.val) ⊤)
        = ⨆ ν : {μ : Fin N →₀ ℕ // glWeightSpace k N M (fun i => μ i) ≠ ⊥},
            glWeightSpace k N M (fun i => ν.val i) := iSup_congr h1
      _ = ⊤ := by
          rw [eq_top_iff, ← hMtop]
          refine iSup_le fun μ => ?_
          by_cases hμ : glWeightSpace k N M (fun i => μ i) = ⊥
          · rw [hμ]; exact bot_le
          · exact le_iSup (fun ν : {μ : Fin N →₀ ℕ // glWeightSpace k N M (fun i => μ i) ≠ ⊥} =>
              glWeightSpace k N M (fun i => ν.val i)) ⟨μ, hμ⟩
  -- Independence of the *full* eigenspace family separates `lam` from the supported ones.
  have hdisj := (iSupIndep_def.mp (Module.End.independent_genEigenspace fop ⊤)) lam
  have hle : (⨆ ν : {μ : Fin N →₀ ℕ // glWeightSpace k N M (fun i => μ i) ≠ ⊥},
      fop.genEigenspace (torusChar N t ν.val) ⊤)
        ≤ ⨆ (ρ) (_ : ρ ≠ lam), fop.genEigenspace ρ ⊤ := by
    refine iSup_le fun ν => ?_
    exact le_iSup₂ (f := fun ρ (_ : ρ ≠ lam) => fop.genEigenspace ρ ⊤)
      (torusChar N t ν.val) (hlam ν.val ν.2)
  rw [eq_bot_iff]
  calc fop.genEigenspace lam ⊤
      = fop.genEigenspace lam ⊤ ⊓ ⊤ := by rw [inf_top_eq]
    _ = fop.genEigenspace lam ⊤ ⊓ (⨆ ν : {μ : Fin N →₀ ℕ //
          glWeightSpace k N M (fun i => μ i) ≠ ⊥}, fop.genEigenspace (torusChar N t ν.val) ⊤) := by
        rw [hGtop]
    _ ≤ fop.genEigenspace lam ⊤ ⊓ (⨆ (ρ) (_ : ρ ≠ lam), fop.genEigenspace ρ ⊤) :=
        inf_le_inf_left _ hle
    _ ≤ ⊥ := disjoint_iff_inf_le.mp hdisj

/-- **Sub-of-spanning-is-spanning (the crux).** For a `GL_N`-invariant submodule `R` of a
weight-spanning `FDRep` `M`, the weight spaces cut down to `R` still span `R`. -/
theorem torusInvariant_iSup_inf_glWeightSpace_eq (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (R : Submodule k M)
    (hR : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k), ∀ v ∈ R, M.ρ g v ∈ R)
    (hMtop : ⨆ μ : Fin N →₀ ℕ, glWeightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ μ : Fin N →₀ ℕ, (glWeightSpace k N M (fun i => μ i) ⊓ R) = R := by
  classical
  obtain ⟨t, hinj⟩ := exists_separating_torus N M
  set f : Module.End k M := M.ρ (Etingof.diagTorus k N t) with hf
  -- `R` is invariant under `f`, and `f`'s generalised eigenspaces span (alg. closed).
  have hRinv : ∀ x ∈ R, f x ∈ R := hR (Etingof.diagTorus k N t)
  have hspan : ⨆ lam : k, f.genEigenspace lam ⊤ = ⊤ :=
    Module.End.iSup_maxGenEigenspace_eq_top f
  -- Mathlib's invariant-submodule decomposition along the eigenspaces of `f`.
  have hRdecomp : R = ⨆ lam : k, R ⊓ f.genEigenspace lam ⊤ :=
    Submodule.eq_iSup_inf_genEigenspace (⊤ : ℕ∞) hRinv hspan
  refine le_antisymm (iSup_le fun μ => inf_le_right) ?_
  conv_lhs => rw [hRdecomp]
  refine iSup_le fun lam => ?_
  by_cases hcase : ∃ ν : Fin N →₀ ℕ,
      glWeightSpace k N M (fun i => ν i) ≠ ⊥ ∧ torusChar N t ν = lam
  · obtain ⟨ν, hν, hcν⟩ := hcase
    have hG : f.genEigenspace lam ⊤ = glWeightSpace k N M (fun i => ν i) := by
      rw [← hcν]
      exact genEigenspace_diagTorus_eq_glWeightSpace N M t hinj hMtop ν hν
    rw [hG, inf_comm]
    exact le_iSup (fun μ : Fin N →₀ ℕ => glWeightSpace k N M (fun i => μ i) ⊓ R) ν
  · push_neg at hcase
    have hbot : f.genEigenspace lam ⊤ = ⊥ :=
      genEigenspace_diagTorus_eq_bot N M t hinj hMtop lam hcase
    rw [hbot, inf_bot_eq]
    exact bot_le

end Etingof.CleanCharExtraction

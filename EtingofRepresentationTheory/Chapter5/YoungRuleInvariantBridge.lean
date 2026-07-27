import EtingofRepresentationTheory.Chapter5.YoungRuleKostkaBridge

/-!
# Frobenius reciprocity bridge for Young's rule

This file identifies the representation-theoretic multiplicity space in Young's rule with the
row-invariant subspace of the corresponding Specht module.  It isolates the remaining
combinatorial content of Young's rule precisely: a basis of that invariant subspace indexed by
semistandard tableaux of the prescribed content.
-/

namespace Etingof

noncomputable section

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)
private abbrev Q (n : ℕ) (mu : Nat.Partition n) := G n ⧸ RowSubgroup n mu

private abbrev identityCosetVector (n : ℕ) (mu : Nat.Partition n) :
    PermutationModule n mu :=
  Finsupp.single (QuotientGroup.mk (1 : G n)) 1

/-- The row-invariant subspace of `V_nu` for the row subgroup attached to `mu`.

Evaluation at the identity coset identifies this subspace with
`Hom_{S_n}(U_mu, V_nu)` below. -/
noncomputable def YoungRuleRowInvariants
    (n : ℕ) (mu nu : Nat.Partition n) : Submodule ℂ ↥(SpechtModule n nu) where
  carrier := {v | ∀ p ∈ RowSubgroup n mu,
    MonoidAlgebra.of ℂ (G n) p * (v : SymGroupAlgebra n) = (v : SymGroupAlgebra n)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw p hp
    simp only [Submodule.coe_add, mul_add, hv p hp, hw p hp]
  smul_mem' := by
    intro c v hv p hp
    change MonoidAlgebra.of ℂ (G n) p * (c • (v : SymGroupAlgebra n)) =
      c • (v : SymGroupAlgebra n)
    rw [Algebra.mul_smul_comm, hv p hp]

/-- A group element acts on a basis vector of the permutation module by translating its coset. -/
private theorem permMod_smul_eq (n : ℕ) (mu : Nat.Partition n)
    (a : SymGroupAlgebra n) (x : PermutationModule n mu) :
    a • x = (Representation.ofMulAction ℂ (G n) (Q n mu)).asAlgebraHom a x := rfl

private theorem of_smul_single (n : ℕ) (mu : Nat.Partition n)
    (g : G n) (q : Q n mu) (c : ℂ) :
    (MonoidAlgebra.of ℂ _ g : SymGroupAlgebra n) •
        (Finsupp.single q c : PermutationModule n mu) =
      Finsupp.single (g • q) c := by
  simp [permMod_smul_eq, Representation.ofMulAction_single]

private theorem permMod_smul_assoc (n : ℕ) (mu : Nat.Partition n)
    (r : ℂ) (a : SymGroupAlgebra n) (x : PermutationModule n mu) :
    (r • a) • x = r • (a • x) := by
  change (Representation.ofMulAction ℂ (G n) (Q n mu)).asAlgebraHom (r • a) x =
    r • (Representation.ofMulAction ℂ (G n) (Q n mu)).asAlgebraHom a x
  simp only [map_smul, LinearMap.smul_apply]

/-- Row-subgroup elements fix the identity coset. -/
private theorem rowSubgroup_fixes_identity (n : ℕ) (mu : Nat.Partition n)
    (p : G n) (hp : p ∈ RowSubgroup n mu) :
    p • (QuotientGroup.mk 1 : Q n mu) = QuotientGroup.mk 1 := by
  change QuotientGroup.mk (p * 1) = QuotientGroup.mk 1
  rw [mul_one, QuotientGroup.eq]
  simpa using (RowSubgroup n mu).inv_mem hp

/-- Every equivariant map out of `U_mu` is determined by its value on the identity coset. -/
private theorem equivariantMap_ext (n : ℕ) (mu nu : Nat.Partition n)
    (f g : PermutationModule n mu →ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu))
    (h : f (identityCosetVector n mu) = g (identityCosetVector n mu)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single q c =>
      obtain ⟨σ, rfl⟩ := Quotient.exists_rep q
      have htranslate :
          (MonoidAlgebra.of ℂ _ σ : SymGroupAlgebra n) • identityCosetVector n mu =
            (Finsupp.single (QuotientGroup.mk σ) 1 : PermutationModule n mu) := by
        rw [of_smul_single]
        rfl
      have hsingle :
          (Finsupp.single (QuotientGroup.mk σ) c : PermutationModule n mu) =
            (c • (MonoidAlgebra.of ℂ _ σ : SymGroupAlgebra n)) •
              identityCosetVector n mu := by
        rw [permMod_smul_assoc, htranslate]
        simp
      rw [hsingle, map_smul, map_smul, h]

/-- Evaluation at the identity coset, landing in the row-invariant subspace. -/
noncomputable def youngRuleEvaluation (n : ℕ) (mu nu : Nat.Partition n) :
    (PermutationModule n mu →ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu)) →ₗ[ℂ]
      ↥(YoungRuleRowInvariants n mu nu) where
  toFun f := ⟨f (identityCosetVector n mu), by
    intro p hp
    have hfix : (MonoidAlgebra.of ℂ _ p : SymGroupAlgebra n) •
        identityCosetVector n mu = identityCosetVector n mu := by
      rw [of_smul_single, rowSubgroup_fixes_identity n mu p hp]
    exact congrArg Subtype.val (show
      (MonoidAlgebra.of ℂ _ p : SymGroupAlgebra n) • f (identityCosetVector n mu) =
        f (identityCosetVector n mu) by rw [← f.map_smul, hfix])⟩
  map_add' f g := by ext; rfl
  map_smul' c f := by ext; rfl

/-- Coset-representative independence, using row invariance of the target vector. -/
private theorem cosetRep_equivariance (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(YoungRuleRowInvariants n mu nu)) (σ : G n) (q : Q n mu) :
    MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) * (v.1 : SymGroupAlgebra n) =
      MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ (Quotient.out q) *
        (v.1 : SymGroupAlgebra n) := by
  have hEq : QuotientGroup.mk (Quotient.out (σ • q)) =
      (QuotientGroup.mk (σ * Quotient.out q) : Q n mu) := by
    rw [QuotientGroup.out_eq']
    change σ • q = QuotientGroup.mk (σ * Quotient.out q)
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have hmem := QuotientGroup.eq.mp hEq
  have hfactor : MonoidAlgebra.of ℂ _ σ * MonoidAlgebra.of ℂ _ (Quotient.out q) =
      MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) *
        MonoidAlgebra.of ℂ _ ((Quotient.out (σ • q))⁻¹ * (σ * Quotient.out q)) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [hfactor, mul_assoc, v.2 _ hmem]

private noncomputable def rowInvariantValue (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(YoungRuleRowInvariants n mu nu)) (q : Q n mu) : ↥(SpechtModule n nu) :=
  (MonoidAlgebra.of ℂ _ (Quotient.out q) : SymGroupAlgebra n) • v.1

private noncomputable def rowInvariantHomC (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(YoungRuleRowInvariants n mu nu)) :
    PermutationModule n mu →ₗ[ℂ] ↥(SpechtModule n nu) :=
  Finsupp.lift ↥(SpechtModule n nu) ℂ (Q n mu) (rowInvariantValue n mu nu v)

@[simp] private theorem rowInvariantHomC_single (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(YoungRuleRowInvariants n mu nu)) (q : Q n mu) (c : ℂ) :
    rowInvariantHomC n mu nu v (Finsupp.single q c) =
      c • rowInvariantValue n mu nu v q := by
  simp [rowInvariantHomC, rowInvariantValue]

/-- The equivariant map represented by a row-invariant vector. -/
noncomputable def rowInvariantHom (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(YoungRuleRowInvariants n mu nu)) :
    PermutationModule n mu →ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu) where
  toFun := rowInvariantHomC n mu nu v
  map_add' := (rowInvariantHomC n mu nu v).map_add
  map_smul' a x := by
    change rowInvariantHomC n mu nu v (a • x) = a • rowInvariantHomC n mu nu v x
    induction a using MonoidAlgebra.induction_on with
    | hM σ =>
        induction x using Finsupp.induction_linear with
        | zero => simp
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
        | single q c =>
            rw [of_smul_single, rowInvariantHomC_single, rowInvariantHomC_single]
            apply Subtype.ext
            simp only [rowInvariantValue, SetLike.val_smul]
            change c • (MonoidAlgebra.of ℂ _ (Quotient.out (σ • q)) *
                (v.1 : SymGroupAlgebra n)) =
              MonoidAlgebra.of ℂ _ σ *
                (c • (MonoidAlgebra.of ℂ _ (Quotient.out q) *
                  (v.1 : SymGroupAlgebra n)))
            rw [Algebra.mul_smul_comm]
            congr 1
            simpa only [mul_assoc] using cosetRep_equivariance n mu nu v σ q
    | hadd a b ha hb => rw [add_smul, map_add, ha, hb, add_smul]
    | hsmul r a ha => rw [permMod_smul_assoc, map_smul, ha, smul_assoc]

private theorem rowInvariantHom_apply_identity (n : ℕ) (mu nu : Nat.Partition n)
    (v : ↥(YoungRuleRowInvariants n mu nu)) :
    rowInvariantHom n mu nu v (identityCosetVector n mu) = v.1 := by
  change rowInvariantHomC n mu nu v (identityCosetVector n mu) = v.1
  rw [rowInvariantHomC_single]
  apply Subtype.ext
  change (1 : ℂ) • (MonoidAlgebra.of ℂ _
    (Quotient.out (QuotientGroup.mk (1 : G n) : Q n mu)) *
      (v.1 : SymGroupAlgebra n)) = (v.1 : SymGroupAlgebra n)
  rw [one_smul]
  apply v.2
  have hEq : (QuotientGroup.mk (1 : G n) : Q n mu) =
      QuotientGroup.mk (Quotient.out (QuotientGroup.mk (1 : G n) : Q n mu)) :=
    (QuotientGroup.out_eq' _).symm
  simpa using QuotientGroup.eq.mp hEq

/-- **Frobenius reciprocity for the concrete Young permutation module.** Evaluation at the
identity coset is a linear equivalence from the Young-rule Hom space to the row-invariant
subspace of the Specht module. -/
noncomputable def youngRuleHomEquivRowInvariants (n : ℕ)
    (mu nu : Nat.Partition n) :
    (PermutationModule n mu →ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu)) ≃ₗ[ℂ]
      ↥(YoungRuleRowInvariants n mu nu) :=
  LinearEquiv.ofBijective (youngRuleEvaluation n mu nu) ⟨
    fun f g h => equivariantMap_ext n mu nu f g (congrArg Subtype.val h),
    fun v => ⟨rowInvariantHom n mu nu v, by
      apply Subtype.ext
      exact rowInvariantHom_apply_identity n mu nu v⟩⟩

/-- The Young-rule multiplicity is the dimension of the corresponding row-invariant space. -/
theorem youngRuleMultiplicity_eq_finrank_rowInvariants (n : ℕ)
    (mu nu : Nat.Partition n) :
    YoungRuleMultiplicity n mu nu = Module.finrank ℂ (YoungRuleRowInvariants n mu nu) := by
  change Module.finrank ℂ
      (PermutationModule n mu →ₗ[SymGroupAlgebra n] ↥(SpechtModule n nu)) = _
  exact (youngRuleHomEquivRowInvariants n mu nu).finrank_eq

/-- The exact remaining datum in Young's rule: a basis of row invariants indexed by the
semistandard tableaux of shape `nu` and content `mu`. -/
abbrev YoungRuleTableauBasis (n : ℕ) (mu nu : Nat.Partition n) :=
  Module.Basis (KostkaTableau n nu mu) ℂ ↥(YoungRuleRowInvariants n mu nu)

/-- A tableau-indexed basis of row invariants immediately identifies the two Kostka notions. -/
theorem youngRuleMultiplicity_eq_kostkaNumber_of_tableauBasis (n : ℕ)
    (mu nu : Nat.Partition n) (b : YoungRuleTableauBasis n mu nu) :
    YoungRuleMultiplicity n mu nu = KostkaNumber n nu mu := by
  letI := Fintype.ofFinite (KostkaTableau n nu mu)
  rw [youngRuleMultiplicity_eq_finrank_rowInvariants,
    Module.finrank_eq_card_basis b, kostkaNumber_eq_card_kostkaTableau,
    Nat.card_eq_fintype_card]

end

end Etingof

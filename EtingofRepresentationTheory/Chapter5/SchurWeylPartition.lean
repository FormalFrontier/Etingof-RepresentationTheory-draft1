import EtingofRepresentationTheory.Chapter5.SchurWeylBimoduleFull
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_ClassificationGeneral
import EtingofRepresentationTheory.Infrastructure.SimpleModuleCount

/-!
# Schur-Weyl duality, part (iii): partition-indexed decomposition

Schur-Weyl duality re-indexed: the abstract bimodule decomposition
`Theorem5_18_4_bimodule_decomposition_full` is re-indexed by partitions of `n`,
giving the book's statement `Theorem5_18_4_partition_decomposition` (Etingof
Theorem 5.18.4(iii) / Corollary 5.19.2).

The Specht labelling is produced by `spechtLabelEmbedding`: each simple summand
`Sᵢ`, restricted along the surjection `k[Sₙ] ↠ symGroupImage`, is classified as
an actual `SpechtModuleK k n λ`.  Distinctness of the `Sᵢ` makes the resulting
label map injective.  Re-indexing along this genuine label (and inserting zero
summands on partitions outside its image) gives the partition-indexed statement.
-/

open scoped TensorProduct DirectSum
open Etingof

namespace Etingof

universe u v

/-! ### Generic `DirectSum` plumbing for the partition reindexing -/

section DirectSumHelpers

/-- Apply a family of linear equivalences summand-wise to a direct sum. -/
noncomputable def directSumCongrRight {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    {A B : ι → Type*} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)]
    (f : ∀ i, A i ≃ₗ[R] B i) : (⨁ i, A i) ≃ₗ[R] ⨁ i, B i :=
  LinearEquiv.ofLinear
    (DirectSum.toModule R ι _ (fun i => (DirectSum.lof R ι B i).comp (f i).toLinearMap))
    (DirectSum.toModule R ι _ (fun i => (DirectSum.lof R ι A i).comp (f i).symm.toLinearMap))
    (by
      refine DirectSum.linearMap_ext R fun i => ?_
      ext x
      simp [DirectSum.toModule_lof])
    (by
      refine DirectSum.linearMap_ext R fun i => ?_
      ext x
      simp [DirectSum.toModule_lof])

/-- Linear version of `DFinsupp.sigmaCurryEquiv`: a sigma-indexed direct sum is an
iterated direct sum. -/
noncomputable def directSumSigmaLequiv {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} [∀ i, DecidableEq (α i)]
    (δ : ∀ i, α i → Type*) [∀ i j, AddCommMonoid (δ i j)] [∀ i j, Module R (δ i j)] :
    (⨁ s : (Σ i, α i), δ s.1 s.2) ≃ₗ[R] ⨁ i, ⨁ j, δ i j :=
  { DirectSum.sigmaLcurry R (δ := δ) with
    invFun := DirectSum.sigmaLuncurry R (δ := δ)
    left_inv := (DFinsupp.sigmaCurryEquiv (δ := δ)).left_inv
    right_inv := (DFinsupp.sigmaCurryEquiv (δ := δ)).right_inv }

/-- A direct sum over a unique index type collapses to its single summand. -/
noncomputable def directSumUniqueEquiv {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    [Unique ι] (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (⨁ i, M i) ≃ₗ[R] M default :=
  { toFun := fun f => f default
    map_add' := fun f g => DFinsupp.add_apply f g default
    map_smul' := fun r f => DFinsupp.smul_apply r f default
    invFun := fun x => DirectSum.lof R ι M default x
    left_inv := fun f => by
      refine DFinsupp.ext fun i => ?_
      rw [Subsingleton.elim i default]
      simp
    right_inv := fun x => by simp }

/-- Tensor product of two direct sums over a `Subsingleton` index collapses to the
direct sum of the summand-wise tensor products. -/
noncomputable def directSumTensorSubsingleton {k : Type*} [CommRing k]
    {F : Type*} [Fintype F] [DecidableEq F] [Subsingleton F]
    (A B : F → Type*) [∀ f, AddCommGroup (A f)] [∀ f, Module k (A f)]
    [∀ f, AddCommGroup (B f)] [∀ f, Module k (B f)] :
    ((⨁ f, A f) ⊗[k] (⨁ f, B f)) ≃ₗ[k] ⨁ f, (A f ⊗[k] B f) :=
  let g : F × F ≃ F :=
    { toFun := Prod.fst
      invFun := fun f => (f, f)
      left_inv := fun p => Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  (TensorProduct.directSum k k A B) ≪≫ₗ DirectSum.lequivCongrLeft k g

end DirectSumHelpers

variable (k : Type u) [Field k]
  (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-! ### `|ConjClasses(Sₙ)| ≤ p(n)` -/

/-- The cycle-type map `ConjClasses(Sₙ) → Nat.Partition n`. -/
private def conjClassToPartition :
    ConjClasses (Equiv.Perm (Fin n)) → Nat.Partition n :=
  Quotient.lift
    (fun σ => (Fintype.card_fin n) ▸ σ.partition)
    (fun _ _ h => congrArg (Fintype.card_fin n ▸ ·) (Equiv.Perm.partition_eq_of_isConj.mp h))

private lemma conjClassToPartition_injective :
    Function.Injective (conjClassToPartition n) := by
  intro a b h
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b, rfl⟩ := b.mk_surjective
  change (Fintype.card_fin n ▸ a.partition) = (Fintype.card_fin n ▸ b.partition) at h
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  have : ∀ (m : ℕ) (hm : m = n) (p q : m.Partition),
      (hm ▸ p : Nat.Partition n) = (hm ▸ q : Nat.Partition n) → p = q := by
    intro m hm; subst hm; intro p q hpq; exact hpq
  exact this _ (Fintype.card_fin n) _ _ h

/-- `|ConjClasses(Sₙ)| ≤ |Nat.Partition n|`, via the injection by cycle type. -/
private lemma card_conjClasses_le_card_partition :
    Fintype.card (ConjClasses (Equiv.Perm (Fin n))) ≤ Fintype.card (Nat.Partition n) :=
  Fintype.card_le_of_injective _ (conjClassToPartition_injective n)

/-! ### The surjection `k[Sₙ] ↠ symGroupImage`. -/

/-- The corestriction of `symGroupAlgHom` to its image `symGroupImage k V n`, as a
surjective `k`-algebra homomorphism `k[Sₙ] →ₐ[k] ↥(symGroupImage k V n)`. -/
noncomputable def symGroupAlgHomToImage :
    MonoidAlgebra k (Equiv.Perm (Fin n)) →ₐ[k] ↥(symGroupImage k V n) :=
  AlgHom.codRestrict (symGroupAlgHom k V n) (symGroupImage k V n)
    (fun a => by rw [← symGroupAlgHom_range]; exact ⟨a, rfl⟩)

theorem symGroupAlgHomToImage_val (a : MonoidAlgebra k (Equiv.Perm (Fin n))) :
    (symGroupAlgHomToImage k V n a : Module.End k (TensorPower k V n)) =
      symGroupAlgHom k V n a := rfl

theorem symGroupAlgHomToImage_surjective :
    Function.Surjective (symGroupAlgHomToImage k V n) := by
  intro b
  obtain ⟨a, ha⟩ : (b : Module.End k (TensorPower k V n)) ∈ (symGroupAlgHom k V n).range := by
    rw [symGroupAlgHom_range]; exact b.prop
  exact ⟨a, Subtype.ext ha⟩

/-! ### The cardinality bound `Fintype.card ι ≤ p(n)`. -/

/-- `n!` is invertible in a characteristic-zero field; packaged as the
`Invertible (Fintype.card (Perm (Fin n)) : k)` instance needed for Corollary 4.2.2. -/
noncomputable instance invertible_card_perm [CharZero k] :
    Invertible (Fintype.card (Equiv.Perm (Fin n)) : k) := by
  apply invertibleOfNonzero
  rw [Fintype.card_perm, Fintype.card_fin]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-- For any family of pairwise non-isomorphic simple
`symGroupImage k V n`-modules (finite over `k`) indexed by a `Fintype` `ι`, we have
`card ι ≤ p(n)`. Restricting along the surjection `k[Sₙ] ↠ symGroupImage` turns each
into a simple `k[Sₙ]`-module, and there are at most `|ConjClasses(Sₙ)| ≤ p(n)` of
those (Corollary 4.2.2). -/
theorem card_le_card_partition [IsAlgClosed k] [CharZero k]
    {ι : Type} [Fintype ι]
    (S : ι → Type*) [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    [∀ i, Module (symGroupImage k V n) (S i)]
    [∀ i, IsScalarTower k (symGroupImage k V n) (S i)]
    [∀ i, IsSimpleModule (symGroupImage k V n) (S i)]
    (hdist : ∀ i j, Nonempty (S i ≃ₗ[symGroupImage k V n] S j) → i = j) :
    Fintype.card ι ≤ Fintype.card (Nat.Partition n) := by
  set q := symGroupAlgHomToImage k V n with hq
  have hq_surj := symGroupAlgHomToImage_surjective k V n
  -- restrict scalars along `q : k[Sₙ] →ₐ symGroupImage`
  letI modS : ∀ i, Module (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i =>
    Module.compHom (S i) q.toRingHom
  have hsmul : ∀ (i) (r : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : S i),
      r • x = q r • x := fun i r x => rfl
  haveI towS : ∀ i, IsScalarTower k (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i => by
    refine ⟨fun c r x => ?_⟩
    rw [hsmul, hsmul, map_smul, smul_assoc]
  haveI : RingHomSurjective q.toRingHom := ⟨hq_surj⟩
  haveI simpS : ∀ i, IsSimpleModule (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i =>
    isSimpleModule_of_surjective_ringHom
      (R := MonoidAlgebra k (Equiv.Perm (Fin n)))
      (S := symGroupImage k V n) (X := S i) q.toRingHom (hsmul i)
  have hdist' : ∀ i j,
      Nonempty (S i ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))] S j) → i = j := by
    intro i j ⟨f⟩
    refine hdist i j ⟨?_⟩
    refine { f.toAddEquiv with map_smul' := fun a x => ?_ }
    obtain ⟨r, rfl⟩ := hq_surj a
    change f (q r • x) = q r • f x
    rw [← hsmul, ← hsmul, f.map_smul]
  calc Fintype.card ι
      ≤ Fintype.card (ConjClasses (Equiv.Perm (Fin n))) :=
        card_le_card_conjClasses' (k := k) (G := Equiv.Perm (Fin n)) S hdist'
    _ ≤ Fintype.card (Nat.Partition n) := card_conjClasses_le_card_partition n

set_option maxHeartbeats 1600000 in
-- Classification plus two scalar-restriction transports exceed the defaults.
set_option synthInstance.maxHeartbeats 800000 in
-- The same transports also trigger deep scalar-tower instance search.
/-- A family of pairwise nonisomorphic simple `symGroupImage`-modules has a
canonical-up-to-choice *genuine Specht* labelling.

Unlike `Function.Embedding.nonempty_of_card_le`, this embedding is obtained by
restricting each module along `k[Sₙ] ↠ symGroupImage` and applying the Specht
classification theorem.  The returned linear equivalences explicitly
intertwine the group-algebra action. -/
theorem spechtLabelEmbedding [IsAlgClosed k] [CharZero k]
    {ι : Type}
    (S : ι → Type*) [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    [∀ i, Module (symGroupImage k V n) (S i)]
    [∀ i, IsScalarTower k (symGroupImage k V n) (S i)]
    [∀ i, IsSimpleModule (symGroupImage k V n) (S i)]
    (hdist : ∀ i j, Nonempty (S i ≃ₗ[symGroupImage k V n] S j) → i = j) :
    ∃ (label : ι ↪ Nat.Partition n)
      (specht : ∀ i, S i ≃ₗ[k] ↥(SpechtModuleK k n (label i))),
      ∀ (i : ι) (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : S i),
        specht i ((symGroupAlgHomToImage k V n a) • x) = a • specht i x := by
  classical
  let q := symGroupAlgHomToImage k V n
  have hq_surj : Function.Surjective q := symGroupAlgHomToImage_surjective k V n
  letI restrictedModule : ∀ i,
      Module (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i =>
    Module.compHom (S i) q.toRingHom
  have hsmul : ∀ (i) (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : S i),
      a • x = q a • x := fun _ _ _ => rfl
  haveI restrictedTower : ∀ i,
      IsScalarTower k (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i => by
    refine ⟨fun c a x => ?_⟩
    rw [hsmul, hsmul, map_smul, smul_assoc]
  haveI : RingHomSurjective q.toRingHom := ⟨hq_surj⟩
  haveI restrictedSimple : ∀ i,
      IsSimpleModule (MonoidAlgebra k (Equiv.Perm (Fin n))) (S i) := fun i =>
    isSimpleModule_of_surjective_ringHom
      (R := MonoidAlgebra k (Equiv.Perm (Fin n)))
      (S := symGroupImage k V n) (X := S i) q.toRingHom (hsmul i)
  choose label hlabel using fun i => classification_general_u k n (S i)
  let spechtIso : ∀ i, S i ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))]
      ↥(SpechtModuleK k n (label i)) := fun i => Classical.choice (hlabel i)
  have hlabel_injective : Function.Injective label := by
    intro i j hij
    have hmid : Nonempty
        (↥(SpechtModuleK k n (label i)) ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))]
          ↥(SpechtModuleK k n (label j))) := by
      rw [hij]
      exact ⟨LinearEquiv.refl _ _⟩
    obtain ⟨mid⟩ := hmid
    let f := (spechtIso i).trans (mid.trans (spechtIso j).symm)
    apply hdist i j
    refine ⟨{ f.toAddEquiv with map_smul' := fun a x => ?_ }⟩
    obtain ⟨r, rfl⟩ := hq_surj a
    change f (q r • x) = q r • f x
    rw [← hsmul i, ← hsmul j, f.map_smul]
  let labelEmbedding : ι ↪ Nat.Partition n := ⟨label, hlabel_injective⟩
  let specht : ∀ i, S i ≃ₗ[k] ↥(SpechtModuleK k n (labelEmbedding i)) :=
    fun i => LinearEquiv.restrictScalars k (spechtIso i)
  refine ⟨labelEmbedding, specht, ?_⟩
  intro i a x
  dsimp only [specht, labelEmbedding]
  rw [← hsmul i]
  exact (spechtIso i).map_smul a x

/-! ### The partition-indexed decomposition. -/

/-- Schur-Weyl duality: partition-indexed decomposition of `V^⊗n`.

This form is valid for every `n`; partitions whose simple modules do not occur
are represented by zero summands.  Its reindexing uses the genuine Specht label
from `spechtLabelEmbedding`, rather than an arbitrary cardinality embedding. -/
theorem Theorem5_18_4_partition_decomposition
    [IsAlgClosed k] [CharZero k] :
    ∃ (S : Nat.Partition n → Type (max u v))
      (_ : ∀ p, AddCommGroup (S p))
      (_ : ∀ p, Module k (S p))
      (_ : ∀ p, Module (symGroupImage k V n) (S p))
      (L : Nat.Partition n → Type (max u v))
      (_ : ∀ p, AddCommGroup (L p))
      (_ : ∀ p, Module k (L p))
      (_ : ∀ p, Module (diagonalActionImage k V n) (L p)),
      (∀ p, IsSimpleModule (symGroupImage k V n) (S p) ∨ Subsingleton (S p)) ∧
      (∀ p, IsSimpleModule (diagonalActionImage k V n) (L p) ∨ Subsingleton (L p)) ∧
      (∀ p q, ¬ Subsingleton (L p) →
        Nonempty (L p ≃ₗ[diagonalActionImage k V n] L q) → p = q) ∧
      Nonempty (TensorPower k V n ≃ₗ[k]
        DirectSum (Nat.Partition n)
          (fun p => S p ⊗[k] L p)) := by
  classical
  obtain ⟨ι, fι, dι, S, acgS, modkS, modAS, towS, simpS, distS, finS,
      L, acgL, modkL, modBL, simpL, hLdist, ⟨iso⟩⟩ :=
    Theorem5_18_4_bimodule_decomposition_full k V n
  haveI := fι; haveI := dι
  letI := acgS
  letI := modkS
  letI := modAS
  haveI := towS
  haveI := simpS
  haveI := finS
  letI := acgL
  letI := modkL
  letI := modBL
  haveI := simpL
  -- The genuine Specht labelling, obtained from classification rather than an
  -- arbitrary cardinality embedding.  The equivalences and action laws are
  -- not needed by the zero-padding plumbing below, but certify that `e i` is
  -- the actual Specht label of `S i`.
  obtain ⟨e, _specht, _spechtAction⟩ := spechtLabelEmbedding k V n S distS
  -- the fibre over each partition: empty or a singleton
  set Fib : Nat.Partition n → Type := fun p => { i : ι // e i = p } with hFib
  haveI fibSub : ∀ p, Subsingleton (Fib p) := fun p =>
    ⟨fun a b => Subtype.ext (e.injective (a.2.trans b.2.symm))⟩
  -- the partition-indexed families: direct sums over the fibres
  refine ⟨fun p => ⨁ j : Fib p, S j.1, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun p => ⨁ j : Fib p, L j.1,
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, ?_, ?_, ?_, ?_⟩
  · -- each `S' p` is simple or subsingleton
    intro p
    by_cases hp : Nonempty (Fib p)
    · haveI : Nonempty (Fib p) := hp
      haveI : Unique (Fib p) := uniqueOfSubsingleton (Classical.choice hp)
      exact Or.inl (IsSimpleModule.congr
        (directSumUniqueEquiv (R := symGroupImage k V n) (fun j : Fib p => S j.1)))
    · rw [not_nonempty_iff] at hp
      haveI : IsEmpty (Fib p) := hp
      exact Or.inr inferInstance
  · -- each `L' p` is simple or subsingleton
    intro p
    by_cases hp : Nonempty (Fib p)
    · haveI : Nonempty (Fib p) := hp
      haveI : Unique (Fib p) := uniqueOfSubsingleton (Classical.choice hp)
      exact Or.inl (IsSimpleModule.congr
        (directSumUniqueEquiv (R := diagonalActionImage k V n) (fun j : Fib p => L j.1)))
    · rw [not_nonempty_iff] at hp
      haveI : IsEmpty (Fib p) := hp
      exact Or.inr inferInstance
  · -- distinctness of the nonzero `L' p`
    rintro p q hp_nss ⟨f⟩
    have hpne : Nonempty (Fib p) := by
      by_contra h
      rw [not_nonempty_iff] at h
      haveI : IsEmpty (Fib p) := h
      exact hp_nss inferInstance
    haveI : Nonempty (Fib p) := hpne
    haveI : Unique (Fib p) := uniqueOfSubsingleton (Classical.choice hpne)
    have hqne : Nonempty (Fib q) := by
      by_contra h
      rw [not_nonempty_iff] at h
      haveI : IsEmpty (Fib q) := h
      haveI : Subsingleton (⨁ j : Fib q, L j.1) := inferInstance
      exact hp_nss ⟨fun a b => f.injective (Subsingleton.elim (f a) (f b))⟩
    haveI : Nonempty (Fib q) := hqne
    haveI : Unique (Fib q) := uniqueOfSubsingleton (Classical.choice hqne)
    let eqp := directSumUniqueEquiv (R := diagonalActionImage k V n) (fun j : Fib p => L j.1)
    let eqq := directSumUniqueEquiv (R := diagonalActionImage k V n) (fun j : Fib q => L j.1)
    have hidx := hLdist (default : Fib p).1 (default : Fib q).1 ⟨eqp.symm ≪≫ₗ f ≪≫ₗ eqq⟩
    calc p = e (default : Fib p).1 := (default : Fib p).2.symm
      _ = e (default : Fib q).1 := by rw [hidx]
      _ = q := (default : Fib q).2
  · -- the decomposition iso
    refine ⟨iso ≪≫ₗ ?_⟩
    refine DirectSum.lequivCongrLeft k (Equiv.sigmaFiberEquiv (e : ι → Nat.Partition n)).symm
      ≪≫ₗ directSumSigmaLequiv (R := k) (fun p (j : Fib p) => S j.1 ⊗[k] L j.1)
      ≪≫ₗ directSumCongrRight (fun p =>
        (directSumTensorSubsingleton (fun j : Fib p => S j.1) (fun j : Fib p => L j.1)).symm)

end Etingof

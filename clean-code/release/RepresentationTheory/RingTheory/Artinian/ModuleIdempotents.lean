/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.RingModuleAuxiliary
import RepresentationTheory.RingTheory.Ideal.IdempotentLifting
import RepresentationTheory.Algebra.Module.EndomorphismDichotomy
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Idempotents and modules over Artinian rings

This module develops idempotent decompositions and projective-module constructions for
finite-dimensional Artinian algebras.
-/

open scoped DirectSum

universe uA

variable {k : Type*} [Field k]
variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]

namespace RepresentationTheory.RingTheory.Artinian.ModuleIdempotents

/-- A finite nontrivial module over an Artinian ring has a coatom among its submodules. -/
theorem exists_isCoatom_submodule
    {R : Type*} [Ring R] [IsArtinianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    ∃ (N : Submodule R M), IsCoatom N := by

  haveI : IsNoetherian R M := ((IsArtinianRing.tfae R M).out 0 1).mp ‹Module.Finite R M›

  haveI : WellFoundedGT (Submodule R M) := isNoetherian_iff'.mp inferInstance
  haveI : IsCoatomic (Submodule R M) :=
    isCoatomic_of_orderTop_gt_wellFounded (wellFounded_gt)
  obtain h | ⟨N, hN_coatom, _⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Submodule R M)
  · exact absurd h bot_ne_top
  · exact ⟨N, hN_coatom⟩

/-- For an exhaustive finite family of simple modules, every finite nontrivial module determines an index together with a nonzero map. -/
theorem exists_index_and_nonzero_map
    {R : Type u} [Ring R] [IsArtinianRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, IsSimpleModule R (M i)]
    (hM_exhaustive : ∀ (S : Type v) [AddCommGroup S] [Module R S] [IsSimpleModule R S],
      ∃ i, Nonempty (S ≃ₗ[R] M i))
    {Q : Type v} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Nontrivial Q] :
    ∃ (j₀ : ι) (f : Q →ₗ[R] M j₀), f ≠ 0 := by

  obtain ⟨N, hN_coatom⟩ := exists_isCoatom_submodule (R := R) (M := Q)

  haveI : IsSimpleModule R (Q ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN_coatom

  obtain ⟨j₀, ⟨e⟩⟩ := hM_exhaustive (Q ⧸ N)

  refine ⟨j₀, e.toLinearMap.comp N.mkQ, ?_⟩
  intro h

  have hzero : ∀ q : Q, e (N.mkQ q) = 0 := fun q => by
    have := LinearMap.congr_fun h q
    simpa using this

  have hmkQ : ∀ q : Q, N.mkQ q = 0 := fun q => by
    have := hzero q; rwa [map_eq_zero_iff e e.injective] at this

  exact hN_coatom.1 (Submodule.eq_top_iff'.mpr fun q => by
    specialize hmkQ q
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmkQ)

/-- Any two simple modules over a simple Artinian ring are linearly equivalent. -/
theorem nonempty_linearEquiv_of_simple_artinian
    {R : Type*} [Ring R] [IsSimpleRing R] [IsArtinianRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R N] :
    Nonempty (M ≃ₗ[R] N) := by

  let eM := LinearEquiv.ofInjective (LinearMap.inl R M N) LinearMap.inl_injective
  let eN := LinearEquiv.ofInjective (LinearMap.inr R M N) LinearMap.inr_injective
  haveI : IsSimpleModule R (LinearMap.range (LinearMap.inl R M N)) :=
    IsSimpleModule.congr eM.symm
  haveI : IsSimpleModule R (LinearMap.range (LinearMap.inr R M N)) :=
    IsSimpleModule.congr eN.symm

  have hiso := IsSimpleRing.isIsotypic R (M × N)
    (LinearMap.range (LinearMap.inl R M N))
  obtain ⟨f⟩ := hiso (LinearMap.range (LinearMap.inr R M N))
  exact ⟨eM.trans (f.symm.trans eN.symm)⟩

section MatrixIdempotents

variable {R : Type*} [CommSemiring R]

/-- A diagonal matrix unit is an idempotent element. -/
lemma isIdempotentElem_matrix_single {ι : Type*} [DecidableEq ι] [Fintype ι]
    (i₀ : ι) :
    IsIdempotentElem (Matrix.single i₀ i₀ (1 : R)) := by
  unfold IsIdempotentElem
  rw [Matrix.single_mul_single_same]
  simp

/-- Coordinate-supported elements built from idempotents form an orthogonal family in a finite product. -/
lemma orthogonalIdempotents_pi_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Semiring (S i)]
    (e : ∀ i, S i) (he : ∀ i, IsIdempotentElem (e i)) :
    OrthogonalIdempotents (fun i => (Pi.single i (e i) : ∀ j, S j)) := by
  constructor
  · intro i
    simp only [IsIdempotentElem, ← Pi.single_mul]
    congr 1; exact he i
  · intro i j hij
    ext l
    by_cases hi : i = l
    · subst hi; simp [hij]
    · simp [hi]

/-- Sandwiching a matrix by a diagonal matrix unit extracts its corresponding diagonal entry. -/
lemma matrix_single_mul_mul_matrix_single {ι : Type*} [DecidableEq ι] [Fintype ι]
    (i₀ : ι) (X : Matrix ι ι R) :
    Matrix.single i₀ i₀ (1 : R) * X * Matrix.single i₀ i₀ (1 : R) =
      X i₀ i₀ • Matrix.single i₀ i₀ (1 : R) := by
  simp [Matrix.smul_single, mul_comm]

end MatrixIdempotents

/-- Associates a linear endomorphism over the base field to an element acting on a module. -/
noncomputable def module_scalar_linearMap (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [SMulCommClass A k M] (a : A) : M →ₗ[k] M where
  toFun m := a • m
  map_add' := smul_add a
  map_smul' c m := smul_comm a c m

/-- Associates a submodule over the base field to an element acting on a module. -/
noncomputable def module_scalar_submodule (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [SMulCommClass A k M] (a : A) : Submodule k M :=
  LinearMap.range (module_scalar_linearMap (k := k) (A := A) M a)

section CentralAction

/-- The coordinate units form a complete family of orthogonal idempotents in a finite product of semirings. -/
lemma completeOrthogonalIdempotents_pi_single_one {n : ℕ} {S : Fin n → Type*}
    [∀ i, Semiring (S i)] :
    CompleteOrthogonalIdempotents (Pi.single (M := S) · 1) :=
  CompleteOrthogonalIdempotents.single S

/-- A coordinate unit commutes with every element of a finite product of semirings. -/
lemma pi_single_one_mul_comm {n : ℕ} {S : Fin n → Type*}
    [∀ i, Semiring (S i)] (l : Fin n) (x : ∀ i, S i) :
    (Pi.single l (1 : S l)) * x = x * (Pi.single l (1 : S l)) := by
  rw [← Pi.single_mul_left, ← Pi.single_mul_right]; simp

end CentralAction

/--
For a finite pairwise nonisomorphic family of simple modules, there are pairwise orthogonal
idempotents whose associated submodules have Kronecker-delta dimensions.
-/
lemma exists_orthogonal_idempotents_with_finrank
    [IsAlgClosed k] [IsArtinianRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) :
    ∃ (e : ι → A),
      (∀ i, IsIdempotentElem (e i)) ∧
      (∀ i j, i ≠ j → e i * e j = 0) ∧
      (∀ i j, Module.finrank k (module_scalar_submodule (k := k) (A := A) (M j) (e i)) =
        if i = j then 1 else 0) := by

  haveI : IsSemiprimaryRing A := inferInstance
  haveI hss : IsSemisimpleRing (A ⧸ Ring.jacobson A) := IsSemiprimaryRing.isSemisimpleRing
  have hnil := IsSemiprimaryRing.isNilpotent (R := A)

  have hann : ∀ i, Ring.jacobson A ≤ Module.annihilator A (M i) :=
    fun i => IsSemisimpleModule.jacobson_le_annihilator A (M i)

  have hsmul_eq : ∀ (a a' : A) (j : ι) (m : M j),
      Ideal.Quotient.mk (Ring.jacobson A) a = Ideal.Quotient.mk (Ring.jacobson A) a' →
      a • m = a' • m := by
    intro a a' j m hq
    have hmem : a - a' ∈ Ring.jacobson A := Ideal.Quotient.eq.mp hq
    have h0 := Module.mem_annihilator.mp (hann j hmem) m
    rwa [sub_smul, sub_eq_zero] at h0

  have hsmulRange_eq : ∀ (a a' : A) (j : ι),
      Ideal.Quotient.mk (Ring.jacobson A) a = Ideal.Quotient.mk (Ring.jacobson A) a' →
      module_scalar_submodule (k := k) (A := A) (M j) a = module_scalar_submodule (k := k) (A := A) (M j) a' := by
    intro a a' j hq
    have : module_scalar_linearMap (k := k) (A := A) (M j) a = module_scalar_linearMap (k := k) (A := A) (M j) a' := by
      ext m; exact hsmul_eq a a' j m hq
    simp only [module_scalar_submodule, this]

  let π := Ideal.Quotient.mk (Ring.jacobson A)
  suffices ∃ (ebar : ι → A ⧸ Ring.jacobson A),
      OrthogonalIdempotents ebar ∧
      ∀ i j (a : A), π a = ebar i →
        Module.finrank k (module_scalar_submodule (k := k) (A := A) (M j) a) =
          if i = j then 1 else 0 by

    obtain ⟨ebar, hebar_orth, hebar_rank⟩ := this

    have hker : ∀ x ∈ RingHom.ker π, IsNilpotent x := by
      intro x hx
      rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
      obtain ⟨n, hn⟩ := hnil
      exact ⟨n, by
        have := Ideal.pow_mem_pow hx n
        rw [hn] at this
        exact Ideal.mem_bot.mp this⟩

    have hebar_range : ∀ i, ebar i ∈ π.range :=
      fun i => Ideal.Quotient.mk_surjective (ebar i)

    obtain ⟨e, he_orth, he_lift⟩ :=
      OrthogonalIdempotents.lift_of_isNilpotent_ker π hker hebar_orth hebar_range

    refine ⟨e, he_orth.idem, fun i j hij => he_orth.ortho hij, fun i j => ?_⟩

    exact hebar_rank i j (e i) (congr_fun he_lift i)

  haveI : Module.Finite k (A ⧸ Ring.jacobson A) := inferInstance
  obtain ⟨n, d, hd, ⟨WA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ Ring.jacobson A)

  suffices ∃ (σ : ι → Fin n),
      Function.Injective σ ∧
      ∀ i j (a : A), π a = WA.symm
          (Pi.single (σ i)
            (Matrix.single (0 : Fin (d (σ i))) 0 (1 : k))) →
        Module.finrank k (module_scalar_submodule (k := k) (A := A) (M j) a) =
          if i = j then 1 else 0 by

    obtain ⟨σ, hσ_inj, hσ_rank⟩ := this

    let ebar : ι → A ⧸ Ring.jacobson A := fun i =>
      WA.symm (Pi.single (σ i) (Matrix.single (0 : Fin (d (σ i))) 0 (1 : k)))
    refine ⟨ebar, ?_, fun i j a ha => hσ_rank i j a ha⟩

    have horth_prod : OrthogonalIdempotents
        (fun i => (Pi.single (σ i) (Matrix.single (0 : Fin (d (σ i))) 0 (1 : k)) :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) k)) := by
      have h_base := orthogonalIdempotents_pi_single
        (fun l => Matrix (Fin (d l)) (Fin (d l)) k)
        (fun l => Matrix.single (0 : Fin (d l)) 0 (1 : k))
        (fun l => isIdempotentElem_matrix_single (0 : Fin (d l)))
      exact h_base.embedding ⟨σ, hσ_inj⟩

    have := horth_prod.map WA.symm.toRingEquiv.toRingHom

    convert this using 1
    funext i
    rfl

  have hWA_mul : ∀ x y : ∀ l, Matrix (Fin (d l)) (Fin (d l)) k,
      WA.symm x * WA.symm y = WA.symm (x * y) := fun x y => (map_mul WA.symm x y).symm

  let c : Fin n → A ⧸ Ring.jacobson A := fun l => WA.symm (Pi.single l 1)

  have hc_comm : ∀ (l : Fin n) (q : A ⧸ Ring.jacobson A), c l * q = q * c l := by
    intro l q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    change WA.symm (Pi.single l 1) * π b = π b * WA.symm (Pi.single l 1)
    rw [show π b = WA.symm (WA (π b)) from (WA.symm_apply_apply _).symm]
    rw [hWA_mul, hWA_mul]
    congr 1
    exact pi_single_one_mul_comm l (WA (π b))

  have hsmulRange_A_sub : ∀ (j : ι) (l : Fin n) (a : A) (ha : π a = c l),
      ∀ (b : A) (x : M j), x ∈ module_scalar_submodule (k := k) (A := A) (M j) a →
        b • x ∈ module_scalar_submodule (k := k) (A := A) (M j) a := by
    intro j l a ha b x ⟨m, hm⟩
    rw [← hm]

    have hcomm : π (b * a) = π (a * b) := by
      rw [map_mul, map_mul, ha]; exact (hc_comm l (π b)).symm
    change b • (a • m) ∈ module_scalar_submodule (k := k) (A := A) (M j) a
    rw [← mul_smul, hsmul_eq _ _ j _ hcomm, mul_smul]
    exact ⟨b • m, rfl⟩

  have hsmulRange_bot_or_top : ∀ (j : ι) (l : Fin n) (a : A) (ha : π a = c l),
      module_scalar_submodule (k := k) (A := A) (M j) a = ⊥ ∨
        module_scalar_submodule (k := k) (A := A) (M j) a = ⊤ := by
    intro j l a ha

    let N : Submodule A (M j) :=
      { carrier := (module_scalar_submodule (k := k) (A := A) (M j) a : Set (M j))
        add_mem' := (module_scalar_submodule (k := k) (A := A) (M j) a).add_mem
        zero_mem' := (module_scalar_submodule (k := k) (A := A) (M j) a).zero_mem
        smul_mem' := fun b x hx => hsmulRange_A_sub j l a ha b x hx }
    rcases IsSimpleOrder.eq_bot_or_eq_top N with h | h
    · left; ext x; constructor
      · intro hx
        have : x ∈ N := hx
        rw [h] at this; exact (Submodule.mem_bot A).mp this
      · intro hx; rw [hx]; exact (module_scalar_submodule (k := k) (A := A) (M j) a).zero_mem
    · right; ext x; constructor
      · intro _; exact Submodule.mem_top
      · intro _
        have : x ∈ N := by rw [h]; exact Submodule.mem_top
        exact this

  have hcoi := completeOrthogonalIdempotents_pi_single_one
    (S := fun l => Matrix (Fin (d l)) (Fin (d l)) k)

  have hc_sum : ∑ l, c l = 1 := by
    change ∑ l, WA.symm (Pi.single l 1) = 1
    rw [← map_sum]; rw [hcoi.complete]; exact map_one WA.symm
  have hblock_exists : ∀ j : ι, ∃ l : Fin n, ∀ a : A,
      π a = WA.symm (Pi.single l 1) →
      module_scalar_submodule (k := k) (A := A) (M j) a = ⊤ := by
    intro j

    by_contra h_none
    push Not at h_none

    have hall_bot : ∀ l : Fin n, ∀ a : A, π a = c l →
        module_scalar_submodule (k := k) (A := A) (M j) a = ⊥ := by
      intro l a ha
      obtain ⟨a₀, ha₀, hne⟩ := h_none l
      rcases hsmulRange_bot_or_top j l a₀ ha₀ with h | h
      ·
        rwa [hsmulRange_eq a a₀ j (ha.trans ha₀.symm)]
      · exact absurd h hne

    haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
    obtain ⟨m, hm⟩ := exists_ne (0 : M j)
    apply hm

    have hlift : ∀ l : Fin n, ∃ a : A, π a = c l :=
      fun l => Ideal.Quotient.mk_surjective (c l)
    choose a_l ha_l using hlift

    have hsum_img : π (∑ l, a_l l) = 1 := by
      rw [map_sum]; simp_rw [ha_l]; exact hc_sum

    have hsum_act : (∑ l, a_l l) • m = m := by
      have := hsmul_eq (∑ l, a_l l) 1 j m (by rw [hsum_img, map_one])
      rwa [one_smul] at this

    rw [← hsum_act, Finset.sum_smul]

    apply Finset.sum_eq_zero
    intro l _
    have h0 := hall_bot l (a_l l) (ha_l l)

    have : a_l l • m ∈ module_scalar_submodule (k := k) (A := A) (M j) (a_l l) := ⟨m, rfl⟩
    rw [h0] at this; exact (Submodule.mem_bot k).mp this

  have hblock_unique : ∀ j : ι, ∀ l₁ l₂ : Fin n,
      (∀ a : A, π a = WA.symm (Pi.single l₁ 1) →
        module_scalar_submodule (k := k) (A := A) (M j) a = ⊤) →
      (∀ a : A, π a = WA.symm (Pi.single l₂ 1) →
        module_scalar_submodule (k := k) (A := A) (M j) a = ⊤) →
      l₁ = l₂ := by
    intro j l₁ l₂ h₁ h₂
    by_contra hne

    have horth : c l₁ * c l₂ = 0 :=
      (hcoi.toOrthogonalIdempotents.map WA.symm.toRingEquiv.toRingHom).ortho hne

    obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective (c l₁)
    obtain ⟨a₂, ha₂⟩ := Ideal.Quotient.mk_surjective (c l₂)

    have h₂_top := h₂ a₂ ha₂

    have hprod_img : π (a₁ * a₂) = 0 := by rw [map_mul, ha₁, ha₂, horth]

    have hprod_zero : ∀ m : M j, (a₁ * a₂) • m = 0 := by
      intro m
      have h0 := hsmul_eq (a₁ * a₂) 0 j m (by rw [hprod_img, map_zero])
      rwa [zero_smul] at h0

    have h₁_top := h₁ a₁ ha₁

    haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)

    have ha₁_zero : ∀ m : M j, a₁ • m = 0 := by
      intro m

      have : m ∈ module_scalar_submodule (k := k) (A := A) (M j) a₂ := by
        rw [h₂_top]; exact Submodule.mem_top
      obtain ⟨m₀, hm₀⟩ := this

      change a₂ • m₀ = m at hm₀
      rw [← hm₀, ← mul_smul]
      exact hprod_zero m₀

    have : module_scalar_submodule (k := k) (A := A) (M j) a₁ = ⊥ := by
      ext x; simp only [Submodule.mem_bot]; constructor
      · rintro ⟨m, rfl⟩; exact ha₁_zero m
      · intro hx; rw [hx]; exact (module_scalar_submodule (k := k) (A := A) (M j) a₁).zero_mem
    rw [this] at h₁_top

    exact bot_ne_top h₁_top

  let σ : ι → Fin n := fun j => (hblock_exists j).choose
  have hσ_spec : ∀ j a, π a = WA.symm (Pi.single (σ j) 1) →
      module_scalar_submodule (k := k) (A := A) (M j) a = ⊤ :=
    fun j => (hblock_exists j).choose_spec

  have hc_idem : ∀ l', IsIdempotentElem (c l') :=
    (hcoi.toOrthogonalIdempotents.map WA.symm.toRingEquiv.toRingHom).idem

  have hc_identity : ∀ (p : ι) (a : A) (ha : π a = c (σ p)),
      ∀ m : M p, a • m = m := by
    intro p a ha m
    have h_top := hσ_spec p a ha
    have ⟨m₀, hm₀⟩ : m ∈ module_scalar_submodule (k := k) (A := A) (M p) a := by
      rw [h_top]; exact Submodule.mem_top
    change a • m₀ = m at hm₀
    rw [← hm₀, ← mul_smul]
    exact hsmul_eq (a * a) a p m₀ (by rw [map_mul, ha, (hc_idem (σ p)).eq])

  have hc_zero : ∀ (p : ι) (l' : Fin n) (hl' : l' ≠ σ p) (a : A)
      (ha : π a = c l'), ∀ m : M p, a • m = 0 := by
    intro p l' hl' a ha m
    rcases hsmulRange_bot_or_top p l' a ha with h | h
    · have : a • m ∈ module_scalar_submodule (k := k) (A := A) (M p) a := ⟨m, rfl⟩
      rw [h] at this; exact (Submodule.mem_bot k).mp this
    · exfalso; exact hl' (hblock_unique p l' (σ p)
        (fun a' ha' => hsmulRange_eq a' a p (ha'.trans ha.symm) ▸ h) (hσ_spec p))

  have hσ_inj : Function.Injective σ := by
    intro i j hij
    apply hM i j

    set l := σ i with hl_def
    have hlj : σ j = l := hij.symm

    let lft : (A ⧸ Ring.jacobson A) → A := fun q => (Ideal.Quotient.mk_surjective q).choose
    have hlft : ∀ q, π (lft q) = q := fun q =>
      (Ideal.Quotient.mk_surjective q).choose_spec

    let matAct : ∀ p : ι, Matrix (Fin (d l)) (Fin (d l)) k → M p → M p :=
      fun p mat m => lft (WA.symm (Pi.single l mat)) • m

    have hdecomp : ∀ (p : ι) (hp : σ p = l) (a : A) (m : M p),
        a • m = matAct p ((WA (π a)) l) m := by
      intro p hp a m
      have hid := hc_identity p (lft (c l)) (by rw [hlft]; exact (congrArg c hp).symm ▸ rfl)
      conv_lhs => rw [show a • m = (a * lft (c l)) • m from by rw [mul_smul, hid m]]

      apply hsmul_eq
      rw [map_mul, hlft]

      rw [hlft]

      conv_lhs => rw [show π a = WA.symm (WA (π a)) from (WA.symm_apply_apply _).symm,
                       show c l = WA.symm (Pi.single l 1) from rfl]
      rw [hWA_mul]; congr 1; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · simp [Pi.mul_apply, show l ≠ l' from fun h => hl' h.symm]

    have hpi_single_mul : ∀ (x y : Matrix (Fin (d l)) (Fin (d l)) k),
        Pi.single l x * Pi.single l y =
          (Pi.single l (x * y) : ∀ l', Matrix (Fin (d l')) (Fin (d l')) k) := by
      intro x y; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · have hne : l ≠ l' := fun h => hl' h.symm
        simp [Pi.mul_apply, hne]
    have hmatAct_mul : ∀ (p : ι) (mat1 mat2 : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p),
        matAct p (mat1 * mat2) m = matAct p mat1 (matAct p mat2 m) := by
      intro p mat1 mat2 m
      change lft (WA.symm (Pi.single l (mat1 * mat2))) • m =
        lft (WA.symm (Pi.single l mat1)) • (lft (WA.symm (Pi.single l mat2)) • m)
      rw [← mul_smul]; apply hsmul_eq
      rw [map_mul, hlft, hlft]; conv_rhs => rw [hlft]
      rw [hWA_mul, hpi_single_mul]
    have hmatAct_add : ∀ (p : ι) (mat1 mat2 : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p),
        matAct p (mat1 + mat2) m = matAct p mat1 m + matAct p mat2 m := by
      intro p mat1 mat2 m
      change lft (WA.symm (Pi.single l (mat1 + mat2))) • m =
        lft (WA.symm (Pi.single l mat1)) • m + lft (WA.symm (Pi.single l mat2)) • m
      rw [← add_smul]; apply hsmul_eq
      rw [map_add, hlft, hlft]; conv_rhs => rw [hlft]
      rw [show WA.symm (Pi.single l mat1) + WA.symm (Pi.single l mat2) =
            WA.symm (Pi.single l mat1 + Pi.single l mat2) from (map_add WA.symm _ _).symm]
      congr 1; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · have hne : l ≠ l' := fun h => hl' h.symm
        simp [hne]
    have hmatAct_one : ∀ (p : ι) (hp : σ p = l) (m : M p), matAct p 1 m = m := by
      intro p hp m
      exact hc_identity p (lft (c l)) (by rw [hlft]; exact (congrArg c hp).symm ▸ rfl) m
    have hmatAct_zero : ∀ (p : ι) (m : M p), matAct p 0 m = 0 := by
      intro p m
      have : lft (WA.symm (Pi.single l 0)) • m = (0 : A) • m := by
        apply hsmul_eq; rw [hlft, map_zero, Pi.single_zero, map_zero]
      exact this.trans (zero_smul A m)

    letI instMi : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M i) :=
      { smul := matAct i
        one_smul := hmatAct_one i rfl
        mul_smul := hmatAct_mul i
        smul_zero := fun _ => smul_zero _
        smul_add := fun _ => smul_add _
        add_smul := hmatAct_add i
        zero_smul := hmatAct_zero i }
    letI instMj : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M j) :=
      { smul := matAct j
        one_smul := hmatAct_one j hlj
        mul_smul := hmatAct_mul j
        smul_zero := fun _ => smul_zero _
        smul_add := fun _ => smul_add _
        add_smul := hmatAct_add j
        zero_smul := hmatAct_zero j }

    have hMatSimple : ∀ (p : ι) (hp : σ p = l) (inst : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M p)),
        (∀ (mat : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p), mat • m = matAct p mat m) →
        @IsSimpleModule (Matrix (Fin (d l)) (Fin (d l)) k) _ (M p) _ inst := by
      intro p hp inst hsmul_def
      haveI : Nontrivial (M p) := IsSimpleModule.nontrivial A (M p)
      exact
        { eq_bot_or_eq_top := fun N => by
            let N_A : Submodule A (M p) :=
              { carrier := N.carrier
                add_mem' := N.add_mem'
                zero_mem' := N.zero_mem'
                smul_mem' := fun a x hx => by
                  rw [hdecomp p hp a x, ← hsmul_def]; exact N.smul_mem _ hx }
            rcases IsSimpleOrder.eq_bot_or_eq_top N_A with h | h
            · left; ext x; simp only [Submodule.mem_bot]
              exact ⟨fun hx => (Submodule.eq_bot_iff _).mp h x hx,
                     fun hx => hx ▸ N.zero_mem⟩
            · right; ext x
              exact ⟨fun _ => trivial,
                     fun _ => (Submodule.eq_top_iff'.mp h x : x ∈ N_A)⟩ }
    haveI hSimMi := hMatSimple i rfl instMi (fun _ _ => rfl)
    haveI hSimMj := hMatSimple j hlj instMj (fun _ _ => rfl)

    haveI : IsSimpleRing (Matrix (Fin (d l)) (Fin (d l)) k) := by
      haveI := hd l; exact IsSimpleRing.matrix (Fin (d l)) k
    haveI : IsArtinianRing (Matrix (Fin (d l)) (Fin (d l)) k) := inferInstance
    obtain ⟨f⟩ := @nonempty_linearEquiv_of_simple_artinian
      (Matrix (Fin (d l)) (Fin (d l)) k) _ _ _ (M i) (M j) _ instMi hSimMi _ instMj hSimMj

    exact ⟨{ toFun := f
             invFun := f.symm
             left_inv := f.left_inv
             right_inv := f.right_inv
             map_add' := f.map_add
             map_smul' := fun a m => by

               simp only [RingHom.id_apply]
               rw [hdecomp i rfl a m, hdecomp j hlj a (f m)]
               exact f.map_smul ((WA (π a)) l) m }⟩

  have hrank : ∀ i j (a : A), π a = WA.symm
      (Pi.single (σ i) (Matrix.single (0 : Fin (d (σ i))) 0 (1 : k))) →
      Module.finrank k (module_scalar_submodule (k := k) (A := A) (M j) a) =
        if i = j then 1 else 0 := by
    intro i j a ha
    split_ifs with hij
    ·
      subst hij

      set l := σ i with hl_def

      have ha_idem : ∀ m : M i, a • (a • m) = a • m := by
        intro m; rw [← mul_smul]
        exact hsmul_eq (a * a) a i m (by
          rw [map_mul, ha, hWA_mul]; congr 1
          rw [← Pi.single_mul_left, Pi.single_eq_same]; congr 1
          exact (isIdempotentElem_matrix_single (0 : Fin (d l))).eq)

      have ha_ne_zero : ∃ m₀ : M i, a • m₀ ≠ 0 := by
        by_contra hall; push Not at hall
        have h_prod_zero : ∀ (b₁ b₂ : A) (m : M i), (b₁ * a * b₂) • m = 0 := by
          intro b₁ b₂ m
          rw [mul_smul, mul_smul, hall, smul_zero]
        haveI : Nontrivial (M i) := IsSimpleModule.nontrivial A (M i)
        obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M i)
        apply hm₀

        have h_sum_eq_c : ∑ j : Fin (d l),
            WA.symm (Pi.single l (Matrix.single j (0 : Fin (d l)) 1)) *
            WA.symm (Pi.single l (Matrix.single (0 : Fin (d l)) 0 1)) *
            WA.symm (Pi.single l (Matrix.single (0 : Fin (d l)) j 1)) = c l := by

          simp_rw [hWA_mul, ← Pi.single_mul_left, Pi.single_eq_same,
            Matrix.single_mul_mul_single, one_mul, mul_one]
          simp_rw [show (Matrix.single (0 : Fin (d l)) (0 : Fin (d l)) (1 : k))
            (0 : Fin (d l)) (0 : Fin (d l)) = 1 from by simp]

          rw [show c l = WA.symm (Pi.single l 1) from rfl]
          rw [show ∑ x, WA.symm (Pi.single l (Matrix.single x x (1 : k))) =
            WA.symm (∑ x, Pi.single l (Matrix.single x x (1 : k))) from
            (map_sum WA.symm.toRingHom _ _).symm]
          congr 1
          funext l'; by_cases hl' : l' = l
          · subst hl'; simp only [Pi.single_eq_same, Finset.sum_apply]
            ext r s
            simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
            split_ifs with h
            · subst h; simp [Finset.mem_univ]
            · apply Finset.sum_eq_zero; intro x _
              simp [show ¬(x = r ∧ x = s) from fun ⟨h1, h2⟩ => h (h1.symm.trans h2)]
          · simp [Finset.sum_apply, hl']

        let b₁ : Fin (d l) → A := fun j =>
          (Ideal.Quotient.mk_surjective (WA.symm (Pi.single l (Matrix.single j (0 : Fin (d l)) 1)))).choose
        let b₂ : Fin (d l) → A := fun j =>
          (Ideal.Quotient.mk_surjective (WA.symm (Pi.single l (Matrix.single (0 : Fin (d l)) j 1)))).choose
        have hb₁ : ∀ j, π (b₁ j) = WA.symm (Pi.single l (Matrix.single j (0 : Fin (d l)) 1)) :=
          fun j => (Ideal.Quotient.mk_surjective _).choose_spec
        have hb₂ : ∀ j, π (b₂ j) = WA.symm (Pi.single l (Matrix.single (0 : Fin (d l)) j 1)) :=
          fun j => (Ideal.Quotient.mk_surjective _).choose_spec
        have hsum_zero : (∑ j, b₁ j * a * b₂ j) • m₀ = 0 := by
          rw [Finset.sum_smul]; exact Finset.sum_eq_zero (fun j _ => h_prod_zero _ _ m₀)
        have hsum_lifts : π (∑ j, b₁ j * a * b₂ j) = c l := by
          rw [map_sum]; simp_rw [map_mul, hb₁, hb₂, ha]; exact h_sum_eq_c
        rw [← hc_identity i _ hsum_lifts m₀]; exact hsum_zero

      obtain ⟨m₀, hm₀⟩ := ha_ne_zero
      set v₀ := a • m₀ with hv₀_def
      have hav₀ : a • v₀ = v₀ := ha_idem m₀

      have hscalar : ∀ m' : M i, a • m' ∈ Submodule.span k {v₀} := by
        intro m'
        haveI : Nontrivial (M i) := IsSimpleModule.nontrivial A (M i)

        have hgen : Submodule.span A {v₀} = ⊤ := by
          rcases IsSimpleOrder.eq_bot_or_eq_top (Submodule.span A {v₀}) with h | h
          · exfalso; exact hm₀ ((Submodule.eq_bot_iff _).mp h v₀ (Submodule.subset_span rfl))
          · exact h
        have hm'_mem : m' ∈ Submodule.span A {v₀} := hgen ▸ Submodule.mem_top
        rw [Submodule.mem_span_singleton] at hm'_mem
        obtain ⟨b, rfl⟩ := hm'_mem

        rw [← mul_smul]
        have hab_eq : (a * b) • v₀ = (a * b * a) • v₀ := by
          conv_lhs => rw [← hav₀]; rw [← mul_smul]
        rw [hab_eq]

        set c_val := (WA (π b)) l 0 0 with hc_val_def
        have hpi_aba : π (a * b * a) = π ((algebraMap k A c_val) * a) := by

          apply WA.injective
          have hWAa : WA (π a) = Pi.single l
              (Matrix.single (0 : Fin (d l)) 0 (1 : k)) := by
            rw [ha]; exact WA.apply_symm_apply _

          simp only [map_mul, hWAa]

          rw [← Pi.single_mul_left, ← Pi.single_mul_left,
              Pi.single_eq_same, matrix_single_mul_mul_matrix_single]

          rw [Ideal.Quotient.mk_algebraMap, WA.commutes]

          ext l'; by_cases hl' : l' = l
          · subst hl'
            simp only [Pi.single_eq_same, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
              Pi.smul_apply, Pi.one_apply, Matrix.smul_apply, smul_eq_mul, one_mul,
              smul_mul_assoc, hc_val_def]
          · simp [Pi.mul_apply, hl']

        have : (a * b * a) • v₀ = c_val • v₀ := by
          have h := hsmul_eq (a * b * a) ((algebraMap k A c_val) * a) i v₀ hpi_aba
          rw [h, mul_smul, hav₀, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem _ c_val (Submodule.subset_span rfl)

      have hspan : module_scalar_submodule (k := k) (A := A) (M i) a = Submodule.span k {v₀} := by
        ext w; constructor
        · rintro ⟨m', rfl⟩; exact hscalar m'
        · intro hw
          rw [Submodule.mem_span_singleton] at hw
          obtain ⟨c_val, rfl⟩ := hw
          exact ⟨c_val • m₀, by simp [module_scalar_linearMap, hv₀_def]⟩
      rw [hspan]; exact finrank_span_singleton hm₀
    ·

      have hσ_ne : σ i ≠ σ j := fun h => hij (hσ_inj h)

      obtain ⟨a_c, ha_c⟩ := Ideal.Quotient.mk_surjective (c (σ i))
      have hc_bot : module_scalar_submodule (k := k) (A := A) (M j) a_c = ⊥ := by
        rcases hsmulRange_bot_or_top j (σ i) a_c ha_c with h | h
        · exact h
        ·
          exfalso; exact hσ_ne (hblock_unique j (σ i) (σ j)
            (fun a' ha' => hsmulRange_eq a' a_c j (ha'.trans ha_c.symm) ▸ h)
            (hσ_spec j))

      have hc_zero : ∀ m : M j, a_c • m = 0 := by
        intro m
        have : a_c • m ∈ module_scalar_submodule (k := k) (A := A) (M j) a_c := ⟨m, rfl⟩
        rw [hc_bot] at this; exact (Submodule.mem_bot k).mp this

      have hfactor : π a = c (σ i) * π a := by
        rw [ha, show c (σ i) = WA.symm (Pi.single (σ i) 1) from rfl, hWA_mul]
        congr 1
        rw [← Pi.single_mul_left]; simp

      have ha_zero : ∀ m : M j, a • m = 0 := by
        intro m
        have := hsmul_eq (a_c * a) a j m (by rw [map_mul, ha_c]; exact hfactor.symm)
        rw [mul_smul] at this
        rw [← this, hc_zero]

      have hbot : module_scalar_submodule (k := k) (A := A) (M j) a = ⊥ := by
        ext x; simp only [Submodule.mem_bot]; constructor
        · rintro ⟨m, rfl⟩; exact ha_zero m
        · intro hx; rw [hx]; exact (module_scalar_submodule (k := k) (A := A) (M j) a).zero_mem
      rw [hbot]; simp
  exact ⟨σ, hσ_inj, hrank⟩

/-- The cyclic submodule generated by an idempotent is projective. -/
lemma projective_span_singleton (e : A) (he : IsIdempotentElem e) :
    Module.Projective A ↥(Submodule.span A ({e} : Set A)) := by

  set S := Submodule.span A ({e} : Set A) with hS_def
  have he_mem : ∀ a : A, a * e ∈ S :=
    fun a => Submodule.smul_mem _ a (Submodule.subset_span rfl)

  let retr : A →ₗ[A] S :=
    { toFun := fun a => ⟨a * e, he_mem a⟩
      map_add' := fun x y => by ext; simp [add_mul]
      map_smul' := fun r x => by ext; simp [mul_assoc] }

  have h_split : retr.comp S.subtype = LinearMap.id := by
    ext ⟨x, hx⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.subtype_apply, retr]
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    simp [mul_assoc, IsIdempotentElem.eq he]
  exact Module.Projective.of_split S.subtype retr h_split

/-- The cyclic submodule generated by one element of a ring is finite over that ring. -/
lemma finite_span_singleton (e : A) :
    Module.Finite A ↥(Submodule.span A ({e} : Set A)) :=
  inferInstance

/-- Conjugate elements generate linearly equivalent cyclic submodules. -/
def span_singleton_linearEquiv_of_conjugate
    (e₁ e₂ : A) (u : Aˣ) (hconj : ↑u * e₁ * ↑u⁻¹ = e₂) :
    ↥(Submodule.span A ({e₁} : Set A)) ≃ₗ[A]
    ↥(Submodule.span A ({e₂} : Set A)) where
  toFun := fun ⟨x, hx⟩ => by
    refine ⟨x * ↑u⁻¹, ?_⟩
    rw [Submodule.mem_span_singleton] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    refine ⟨a * ↑u⁻¹, ?_⟩
    simp only [smul_eq_mul]

    rw [← hconj]

    simp only [← mul_assoc]
    rw [show a * ↑u⁻¹ * ↑u = a from by rw [mul_assoc, Units.inv_mul, mul_one]]
  invFun := fun ⟨y, hy⟩ => by
    refine ⟨y * ↑u, ?_⟩
    rw [Submodule.mem_span_singleton] at hy ⊢
    obtain ⟨b, rfl⟩ := hy
    refine ⟨b * ↑u, ?_⟩
    simp only [smul_eq_mul]

    rw [← hconj]
    simp only [← mul_assoc]
    rw [show b * ↑u * e₁ * ↑u⁻¹ * ↑u = b * ↑u * e₁ from by
      rw [mul_assoc (b * ↑u * e₁), Units.inv_mul, mul_one]]
  left_inv := fun ⟨x, _⟩ => by
    ext; change x * ↑u⁻¹ * ↑u = x
    rw [mul_assoc, Units.inv_mul, mul_one]
  right_inv := fun ⟨y, _⟩ => by
    ext; change y * ↑u * ↑u⁻¹ = y
    rw [mul_assoc, Units.mul_inv, mul_one]
  map_add' := fun ⟨x, _⟩ ⟨y, _⟩ => by ext; simp [add_mul]
  map_smul' := fun r ⟨x, _⟩ => by ext; change r * x * ↑u⁻¹ = r * (x * ↑u⁻¹); rw [mul_assoc]

/-- The cyclic submodules generated by a complete family of orthogonal idempotents form an internal direct sum. -/
lemma isInternal_span_singleton_of_completeOrthogonalIdempotents
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → A) (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal (fun i => Submodule.span A ({e i} : Set A)) := by
  set N := fun i => Submodule.span A ({e i} : Set A) with hN

  have hmem : ∀ i (x : A), x ∈ N i ↔ ∃ a, a * e i = x := by
    intro i x; rw [hN, Submodule.mem_span_singleton]; rfl

  have hmul_right : ∀ i j (a : A), a * e i * e j = if i = j then a * e i else 0 := by
    intro i j a
    split_ifs with hij
    · subst hij; rw [mul_assoc, he.toOrthogonalIdempotents.idem]
    · rw [mul_assoc, he.toOrthogonalIdempotents.ortho hij, mul_zero]

  have hmul_component : ∀ k j (x : ↥(N j)), (↑x : A) * e k = if j = k then ↑x else 0 := by
    intro k j ⟨x, hx⟩
    rw [hmem] at hx; obtain ⟨c, rfl⟩ := hx
    simp [hmul_right]

  have hextract : ∀ (f : ⨁ j, ↥(N j)) (k : ι),
      (DirectSum.coeLinearMap N f) * e k = ↑(f k) := by
    intro f k
    have hsum : DirectSum.coeLinearMap N f = ∑ j, ↑(f j) := by
      conv_lhs =>
        rw [show f = ∑ j ∈ Finset.univ, DirectSum.of _ j (f j) from
          (DirectSum.sum_univ_of f).symm]
      simp [DirectSum.coeLinearMap_of]
    rw [hsum, Finset.sum_mul]
    conv_lhs =>
      arg 2; ext j
      rw [hmul_component k j (f j)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  constructor
  ·
    intro f g hfg
    have hfg' : DirectSum.coeLinearMap N f = DirectSum.coeLinearMap N g := hfg
    have hcomp : ∀ i, (f i : A) = (g i : A) := by
      intro i
      have h1 := hextract f i
      have h2 := hextract g i
      rw [hfg'] at h1
      exact h1.symm.trans h2
    exact DFinsupp.ext fun i => Subtype.ext (hcomp i)
  ·
    intro a
    refine ⟨∑ i, DirectSum.of (fun i => ↥(N i)) i
        ⟨a * e i, Submodule.smul_mem _ a (Submodule.subset_span rfl)⟩, ?_⟩

    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    rw [show ∑ i, a * e i = a * ∑ i, e i from (Finset.mul_sum ..).symm,
      he.complete, mul_one]

/-- An idempotent whose linear-map dimensions select one simple module has a cyclic submodule satisfying the designated module property. -/
lemma span_singleton_satisfies_module_property
    [IsArtinianRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S]
      [IsSimpleModule A S], ∃ i, Nonempty (S ≃ₗ[A] M i))
    (e : A) (he : IsIdempotentElem e)
    (i₀ : ι) (hdim : ∀ j, Module.finrank k
      (↥(Submodule.span A ({e} : Set A)) →ₗ[A] M j) =
      if i₀ = j then 1 else 0) :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A
      ↥(Submodule.span A ({e} : Set A)) := by
  set S := Submodule.span A ({e} : Set A) with hS_def
  constructor
  ·
    have h1 := hdim i₀
    simp only [ite_true] at h1

    by_contra h_triv
    rw [not_nontrivial_iff_subsingleton] at h_triv
    have h0 : Module.finrank k (↥S →ₗ[A] M i₀) = 0 := by
      haveI := h_triv
      haveI : Subsingleton (↥S →ₗ[A] M i₀) :=
        ⟨fun f g => LinearMap.ext fun x => by
          have := Subsingleton.elim x 0
          simp [this]⟩
      exact Module.finrank_zero_of_subsingleton
    linarith
  ·

    intro W₁ W₂ hcompl
    by_contra h_both
    push Not at h_both
    obtain ⟨hW₁, hW₂⟩ := h_both

    set equiv := Submodule.prodEquivOfIsCompl W₁ W₂ hcompl

    let proj₁ : ↥S →ₗ[A] ↥W₁ :=
      (LinearMap.fst A ↥W₁ ↥W₂).comp equiv.symm.toLinearMap
    let proj₂ : ↥S →ₗ[A] ↥W₂ :=
      (LinearMap.snd A ↥W₁ ↥W₂).comp equiv.symm.toLinearMap

    have hM_fin : ∀ j, Module.Finite k (M j) := by
      intro j
      haveI : Nontrivial (M j) := @IsSimpleModule.nontrivial A _ (M j) _ _ _
      obtain ⟨v, hv⟩ := exists_ne (0 : M j)

      let φ : A →ₗ[k] M j := (LinearMap.toSpanSingleton A (M j) v).restrictScalars k
      have hφ_surj : Function.Surjective φ := by
        intro m

        have hrange : LinearMap.range (LinearMap.toSpanSingleton A (M j) v) = ⊤ := by
          rcases IsSimpleOrder.eq_bot_or_eq_top
            (LinearMap.range (LinearMap.toSpanSingleton A (M j) v)) with h | h
          · exfalso
            have hmem : v ∈ LinearMap.range (LinearMap.toSpanSingleton A (M j) v) := by
              exact ⟨1, one_smul A v⟩
            rw [h] at hmem
            simp [Submodule.mem_bot] at hmem
            exact hv hmem
          · exact h
        exact LinearMap.range_eq_top.mp hrange m
      exact Module.Finite.of_surjective φ hφ_surj

    haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
    haveI : IsNoetherianRing A := inferInstance
    haveI : IsNoetherian A ↥S := isNoetherian_submodule' S
    haveI : IsNoetherian A ↥W₁ := isNoetherian_submodule' W₁
    haveI : IsNoetherian A ↥W₂ := isNoetherian_submodule' W₂
    haveI hW₁_nt : Nontrivial ↥W₁ := W₁.nontrivial_iff_ne_bot.mpr hW₁
    haveI hW₂_nt : Nontrivial ↥W₂ := W₂.nontrivial_iff_ne_bot.mpr hW₂

    obtain ⟨N₁, hN₁⟩ := IsCoatomic.exists_coatom (α := Submodule A ↥W₁)
    obtain ⟨N₂, hN₂⟩ := IsCoatomic.exists_coatom (α := Submodule A ↥W₂)

    haveI hsimp₁ : IsSimpleModule A (↥W₁ ⧸ N₁) := isSimpleModule_iff_isCoatom.mpr hN₁
    haveI hsimp₂ : IsSimpleModule A (↥W₂ ⧸ N₂) := isSimpleModule_iff_isCoatom.mpr hN₂

    obtain ⟨j₁, ⟨iso₁⟩⟩ := hM_exhaustive (↥W₁ ⧸ N₁)
    obtain ⟨j₂, ⟨iso₂⟩⟩ := hM_exhaustive (↥W₂ ⧸ N₂)

    let f₁ : ↥S →ₗ[A] M j₁ :=
      iso₁.toLinearMap.comp (N₁.mkQ.comp proj₁)
    let f₂ : ↥S →ₗ[A] M j₂ :=
      iso₂.toLinearMap.comp (N₂.mkQ.comp proj₂)

    have hproj₁_equiv : ∀ (w₁ : ↥W₁) (w₂ : ↥W₂), proj₁ (equiv (w₁, w₂)) = w₁ := by
      intro w₁ w₂
      change (LinearMap.fst A ↥W₁ ↥W₂) (equiv.symm (equiv (w₁, w₂))) = w₁
      rw [equiv.symm_apply_apply]; rfl
    have hproj₂_equiv : ∀ (w₁ : ↥W₁) (w₂ : ↥W₂), proj₂ (equiv (w₁, w₂)) = w₂ := by
      intro w₁ w₂
      change (LinearMap.snd A ↥W₁ ↥W₂) (equiv.symm (equiv (w₁, w₂))) = w₂
      rw [equiv.symm_apply_apply]; rfl

    have hf₁_ne : f₁ ≠ 0 := by
      intro hf
      apply hN₁.1
      rw [Submodule.eq_top_iff']
      intro w
      rw [← Submodule.Quotient.mk_eq_zero]
      have h1 : f₁ (equiv (w, 0)) = 0 := by simp [hf]
      simp only [f₁, LinearMap.comp_apply, hproj₁_equiv] at h1

      change iso₁ (N₁.mkQ w) = 0 at h1
      exact iso₁.map_eq_zero_iff.mp h1

    have hf₂_ne : f₂ ≠ 0 := by
      intro hf
      apply hN₂.1
      rw [Submodule.eq_top_iff']
      intro w
      rw [← Submodule.Quotient.mk_eq_zero]
      have h1 : f₂ (equiv (0, w)) = 0 := by simp [hf]
      simp only [f₂, LinearMap.comp_apply, hproj₂_equiv] at h1
      change iso₂ (N₂.mkQ w) = 0 at h1
      exact iso₂.map_eq_zero_iff.mp h1

    have hHom_fin : ∀ j, Module.Finite k (↥S →ₗ[A] M j) := by
      intro j
      haveI := hM_fin j

      haveI : Module.Finite k ↥S :=
        Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective

      exact Module.Finite.of_injective
        (LinearMap.restrictScalarsₗ k A (↥S) (M j) k)
        (LinearMap.restrictScalars_injective k)
    have hj₁ : j₁ = i₀ := by
      by_contra h
      apply hf₁_ne
      have h0 : Module.finrank k (↥S →ₗ[A] M j₁) = 0 := by
        rw [hdim j₁, if_neg (Ne.symm h)]
      haveI := hHom_fin j₁
      rw [Module.finrank_eq_zero_iff] at h0
      obtain ⟨a, ha_ne, ha_smul⟩ := h0 f₁
      calc f₁ = (1 : k) • f₁ := (one_smul k f₁).symm
        _ = (a⁻¹ * a) • f₁ := by rw [inv_mul_cancel₀ ha_ne]
        _ = a⁻¹ • (a • f₁) := by rw [smul_smul]
        _ = a⁻¹ • 0 := by rw [ha_smul]
        _ = 0 := smul_zero _
    have hj₂ : j₂ = i₀ := by
      by_contra h
      apply hf₂_ne
      have h0 : Module.finrank k (↥S →ₗ[A] M j₂) = 0 := by
        rw [hdim j₂, if_neg (Ne.symm h)]
      haveI := hHom_fin j₂
      rw [Module.finrank_eq_zero_iff] at h0
      obtain ⟨a, ha_ne, ha_smul⟩ := h0 f₂
      calc f₂ = (1 : k) • f₂ := (one_smul k f₂).symm
        _ = (a⁻¹ * a) • f₂ := by rw [inv_mul_cancel₀ ha_ne]
        _ = a⁻¹ • (a • f₂) := by rw [smul_smul]
        _ = a⁻¹ • 0 := by rw [ha_smul]
        _ = 0 := smul_zero _

    have hf₁_W₂ : ∀ (w₂ : ↥W₂), f₁ (equiv (0, w₂)) = 0 := by
      intro w₂
      simp only [f₁, LinearMap.comp_apply, hproj₁_equiv]
      simp [map_zero]

    have hf₂_W₁ : ∀ (w₁ : ↥W₁), f₂ (equiv (w₁, 0)) = 0 := by
      intro w₁
      simp only [f₂, LinearMap.comp_apply, hproj₂_equiv]
      simp [map_zero]

    have hj₁₂ : j₁ = j₂ := hj₁.trans hj₂.symm

    let f₂' : ↥S →ₗ[A] M j₁ := hj₁₂ ▸ f₂
    have hf₂'_ne : f₂' ≠ 0 := by
      intro h; apply hf₂_ne; simp only [f₂'] at h; exact hj₁₂ ▸ h
    have hf₂'_W₁ : ∀ (w₁ : ↥W₁), f₂' (equiv (w₁, 0)) = 0 := by
      intro w₁; simp only [f₂']; subst hj₁₂; exact hf₂_W₁ w₁

    haveI := hHom_fin j₁
    have h_li : LinearIndependent k ![f₁, f₂'] := by
      rw [linearIndependent_fin2]
      refine ⟨?_, ?_⟩
      ·
        simp only [Matrix.cons_val_one]
        exact hf₂'_ne
      · intro a ha

        simp only [Matrix.cons_val_one,
                    Matrix.cons_val_zero] at ha

        exfalso; apply hf₁_ne; ext s
        obtain ⟨⟨w₁, w₂⟩, rfl⟩ := equiv.surjective s
        have h1 := hf₁_W₂ w₂
        have h2 := hf₂'_W₁ w₁
        have : f₁ (equiv (w₁, w₂)) = f₁ (equiv (w₁, 0)) + f₁ (equiv (0, w₂)) := by
          rw [← map_add, ← equiv.map_add]; congr 1; simp [Prod.add_def]
        simp only [LinearMap.zero_apply]
        rw [this, h1, add_zero, ← ha, LinearMap.smul_apply, h2, smul_zero]
    have h_card : Fintype.card (Fin 2) ≤ Module.finrank k (↥S →ₗ[A] M j₁) :=
      h_li.fintype_card_le_finrank
    simp at h_card
    have h1 := hdim j₁
    rw [if_pos hj₁.symm] at h1
    omega

/-- For an idempotent, the dimension of the space of linear maps from its cyclic submodule equals the dimension of the associated submodule. -/
lemma finrank_linearMap_span_eq_associated_submodule
    (e : A) (he : IsIdempotentElem e)
    (M : Type*) [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] [SMulCommClass A k M] :
    Module.finrank k (↥(Submodule.span A ({e} : Set A)) →ₗ[A] M) =
    Module.finrank k ↥(module_scalar_submodule (k := k) (A := A) M e) := by

  set S := Submodule.span A ({e} : Set A) with hS_def
  have he_mem_S : e ∈ S := Submodule.subset_span rfl

  have hfwd_mem : ∀ (φ : S →ₗ[A] M), φ ⟨e, he_mem_S⟩ ∈ module_scalar_submodule (k := k) (A := A) M e := by
    intro φ
    refine ⟨φ ⟨e, he_mem_S⟩, ?_⟩
    change e • φ ⟨e, he_mem_S⟩ = φ ⟨e, he_mem_S⟩
    rw [← φ.map_smul]; congr 1
    exact Subtype.ext (IsIdempotentElem.eq he)

  have hbwd_map_smul : ∀ (m : M) (a : A) (x : S), (a • x.1) • m = a • (x.1 • m) := by
    intro m a x; rw [smul_eq_mul, mul_smul]

  let equiv : (S →ₗ[A] M) ≃ₗ[k] ↥(module_scalar_submodule (k := k) (A := A) M e) :=
    { toFun := fun φ => ⟨φ ⟨e, he_mem_S⟩, hfwd_mem φ⟩
      invFun := fun ⟨m, hm⟩ =>
        { toFun := fun ⟨x, _⟩ => x • m
          map_add' := fun ⟨x, _⟩ ⟨y, _⟩ => by simp [add_smul]
          map_smul' := fun a ⟨x, _⟩ => by simp [mul_smul] }
      left_inv := by
        intro φ; ext ⟨x, hx⟩

        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨a, rfl⟩ := hx

        have he_act : (e : A) • φ ⟨e, he_mem_S⟩ = φ ⟨e, he_mem_S⟩ := by
          conv_rhs => rw [show (⟨e, he_mem_S⟩ : S) = e • ⟨e, he_mem_S⟩ from
            Subtype.ext (IsIdempotentElem.eq he).symm]
          exact (φ.map_smul e ⟨e, he_mem_S⟩).symm
        change (a • e : A) • φ ⟨e, he_mem_S⟩ = φ ⟨a • e, _⟩
        conv_rhs => rw [show (⟨a • e, _⟩ : S) = a • ⟨e, he_mem_S⟩ from rfl]
        rw [φ.map_smul, smul_eq_mul, mul_smul, he_act]
      right_inv := by
        intro ⟨m, hm⟩

        obtain ⟨m₀, hm₀⟩ := hm

        apply Subtype.ext
        change (e : A) • m = m
        rw [← hm₀]
        change e • (e • m₀) = e • m₀
        rw [← mul_smul, IsIdempotentElem.eq he]
      map_add' := fun φ ψ => by ext; simp
      map_smul' := fun c φ => by
        ext; rfl }
  exact equiv.finrank_eq

end RepresentationTheory.RingTheory.Artinian.ModuleIdempotents

section LocalEndomorphismRing

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]

/-- The endomorphism ring of a finite-dimensional module satisfying the ambient module condition is local. -/
theorem RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate.endomorphism_ring_isLocal
    {W : Type*} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W] (hW : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A W) :
    IsLocalRing (Module.End A W) where
  exists_pair_ne := by
    haveI := hW.1
    exact ⟨1, 0, one_ne_zero⟩
  isUnit_or_isUnit_of_add_one := by
    intro a b hab
    rcases RepresentationTheory.Algebra.Module.EndomorphismDichotomy.bijective_or_nilpotent_of_auxiliaryProperty k A W hW a with ha | ha
    · left; exact (Module.End.isUnit_iff a).mpr ha
    · right
      have hb : b = 1 - a := eq_sub_of_add_eq' hab
      rw [hb]; exact ha.isUnit_one_sub

/-- An endomorphism of a finite-dimensional module satisfying the designated module property is nilpotent when its range lies in a proper submodule. -/
theorem RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.isNilpotent_of_range_le_proper
    {W : Type*} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W] (hW : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A W)
    (θ : W →ₗ[A] W) (N : Submodule A W) (hN : N ≠ ⊤) (hθ : LinearMap.range θ ≤ N) :
    IsNilpotent θ := by
  rcases RepresentationTheory.Algebra.Module.EndomorphismDichotomy.bijective_or_nilpotent_of_auxiliaryProperty k A W hW θ with hbij | hnil
  · exfalso
    have hrange : LinearMap.range θ = ⊤ :=
      LinearMap.range_eq_top.mpr hbij.2
    exact hN (top_le_iff.mp (hrange ▸ hθ))
  · exact hnil

/-- Two finite-dimensional projective modules satisfying the designated module property are linearly equivalent if both admit nonzero maps to the same simple module. -/
theorem RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.nonempty_linearEquiv_of_nonzero_maps_to_simple
    {P : Type*} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [FiniteDimensional k P] [Module.Projective A P]
    (hP : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A P)
    {P' : Type*} [AddCommGroup P'] [Module A P'] [Module k P'] [IsScalarTower k A P']
    [FiniteDimensional k P'] [Module.Projective A P']
    (hP' : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A P')
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    (φ : P →ₗ[A] M) (hφ : φ ≠ 0) (ψ : P' →ₗ[A] M) (hψ : ψ ≠ 0) :
    Nonempty (P ≃ₗ[A] P') := by

  have hφ_surj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    exact (eq_bot_or_eq_top (LinearMap.range φ)).resolve_left
      (LinearMap.range_eq_bot.not.mpr hφ)
  have hψ_surj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top]
    exact (eq_bot_or_eq_top (LinearMap.range ψ)).resolve_left
      (LinearMap.range_eq_bot.not.mpr hψ)

  obtain ⟨f, hf⟩ := Module.projective_lifting_property ψ φ hψ_surj
  obtain ⟨g, hg⟩ := Module.projective_lifting_property φ ψ hφ_surj

  have hgf_range :
      LinearMap.range (g.comp f - LinearMap.id) ≤ LinearMap.ker φ := by
    intro y hy
    rw [LinearMap.mem_ker]
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
    rw [← hx]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    have h1 : φ (g (f x)) = ψ (f x) := LinearMap.congr_fun hg (f x)
    have h2 : ψ (f x) = φ x := LinearMap.congr_fun hf x
    rw [map_sub, h1, h2, sub_self]

  have hker_proper : LinearMap.ker φ ≠ ⊤ := by
    intro h; exact hφ (LinearMap.ker_eq_top.mp h)

  have hgf_nilp : IsNilpotent (g.comp f - LinearMap.id) :=
    RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.isNilpotent_of_range_le_proper (k := k) hP _ _
      hker_proper hgf_range
  have hgf_unit : IsUnit (g.comp f) := by
    have heq : g.comp f = LinearMap.id - (-(g.comp f - LinearMap.id)) :=
      by simp only [neg_sub, sub_sub_cancel]
    rw [heq]; exact hgf_nilp.neg.isUnit_one_sub

  have hfg_range :
      LinearMap.range (f.comp g - LinearMap.id) ≤ LinearMap.ker ψ := by
    intro y hy
    rw [LinearMap.mem_ker]
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
    rw [← hx]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    have h1 : ψ (f (g x)) = φ (g x) := LinearMap.congr_fun hf (g x)
    have h2 : φ (g x) = ψ x := LinearMap.congr_fun hg x
    rw [map_sub, h1, h2, sub_self]
  have hker_proper' : LinearMap.ker ψ ≠ ⊤ := by
    intro h; exact hψ (LinearMap.ker_eq_top.mp h)
  have hfg_nilp : IsNilpotent (f.comp g - LinearMap.id) :=
    RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.isNilpotent_of_range_le_proper (k := k) hP' _ _
      hker_proper' hfg_range
  have hfg_unit : IsUnit (f.comp g) := by
    have heq : f.comp g = LinearMap.id - (-(f.comp g - LinearMap.id)) :=
      by simp only [neg_sub, sub_sub_cancel]
    rw [heq]; exact hfg_nilp.neg.isUnit_one_sub

  have hgf_bij : Function.Bijective (g.comp f) :=
    (Module.End.isUnit_iff _).mp hgf_unit
  have hfg_bij : Function.Bijective (f.comp g) :=
    (Module.End.isUnit_iff _).mp hfg_unit
  have f_inj : Function.Injective f := by
    intro x y hxy
    have : (g.comp f) x = (g.comp f) y := by
      simp only [LinearMap.comp_apply]; exact congr_arg g hxy
    exact hgf_bij.1 this
  have f_surj : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := hfg_bij.2 y
    exact ⟨g z, by
      have : f (g z) = (f.comp g) z := rfl
      rw [this, hz]⟩
  exact ⟨LinearEquiv.ofBijective f ⟨f_inj, f_surj⟩⟩

end LocalEndomorphismRing

/-- There exists a family of finite projective modules whose linear-map dimensions against the chosen simple modules are Kronecker deltas and which has the displayed uniqueness property. -/
theorem RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.exists_projective_family_with_finrank_hom
    [IsAlgClosed k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S]
      [IsSimpleModule A S], ∃ i, Nonempty (S ≃ₗ[A] M i)) :
    ∃ (P : ι → Type uA)
      (_ : ∀ i, AddCommGroup (P i))
      (_ : ∀ i, Module A (P i))
      (_ : ∀ i, Module k (P i))
      (_ : ∀ i, IsScalarTower k A (P i))
      (_ : ∀ i, SMulCommClass A k (P i))
      (_ : ∀ i, Module.Projective A (P i))
      (_ : ∀ i, Module.Finite A (P i))
      (_ : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (P i)),
      (∀ i j, Module.finrank k (P i →ₗ[A] M j) =
        if i = j then 1 else 0) ∧

      (∀ i (Q : Type uA) [AddCommGroup Q] [Module A Q] [Module k Q]
          [IsScalarTower k A Q] [SMulCommClass A k Q]
          [Module.Projective A Q] [Module.Finite A Q],
        RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A Q →
        (∀ j, Module.finrank k (Q →ₗ[A] M j) = if i = j then 1 else 0) →
        Nonempty (Q ≃ₗ[A] P i)) := by

  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance

  obtain ⟨e, he_idem, he_orth, he_dim⟩ :=
    RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.exists_orthogonal_idempotents_with_finrank
      (k := k) M hM

  have hdim_hom : ∀ i j, Module.finrank k
      (↥(Submodule.span A ({e i} : Set A)) →ₗ[A] M j) =
      if i = j then 1 else 0 := by
    intro i j
    rw [RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.finrank_linearMap_span_eq_associated_submodule (k := k)
      (e i) (he_idem i)]
    exact he_dim i j
  refine ⟨fun i => ↥(Submodule.span A ({e i} : Set A)),
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance,
    fun i => RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.projective_span_singleton (e i) (he_idem i),
    fun i => RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.finite_span_singleton (e i),
    fun i => RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.span_singleton_satisfies_module_property
      (k := k) M hM hM_exhaustive (e i) (he_idem i) i
      (hdim_hom i),
    hdim_hom, ?_⟩

  intro i Q _ _ _ _ _ _ _ hQ_indec hQ_delta
  haveI : Nontrivial Q := hQ_indec.1
  haveI : FiniteDimensional k Q := Module.Finite.trans A Q
  haveI : Module.Finite A (↥(Submodule.span A ({e i} : Set A))) :=
    RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.finite_span_singleton (e i)
  haveI : FiniteDimensional k (↥(Submodule.span A ({e i} : Set A))) :=
    Module.Finite.trans A _
  haveI : Module.Projective A (↥(Submodule.span A ({e i} : Set A))) :=
    RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.projective_span_singleton (e i) (he_idem i)

  have hQdim : Module.finrank k (Q →ₗ[A] M i) = 1 := by simpa using hQ_delta i
  haveI : Nontrivial (Q →ₗ[A] M i) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hQdim]; norm_num)
  obtain ⟨φ, hφ⟩ := exists_ne (0 : Q →ₗ[A] M i)

  have hPdim : Module.finrank k
      (↥(Submodule.span A ({e i} : Set A)) →ₗ[A] M i) = 1 := by
    simpa using hdim_hom i i
  haveI : Nontrivial (↥(Submodule.span A ({e i} : Set A)) →ₗ[A] M i) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hPdim]; norm_num)
  obtain ⟨ψ, hψ⟩ := exists_ne
    (0 : ↥(Submodule.span A ({e i} : Set A)) →ₗ[A] M i)
  exact RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.nonempty_linearEquiv_of_nonzero_maps_to_simple (k := k) hQ_indec
    (RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.span_singleton_satisfies_module_property (k := k) M hM hM_exhaustive
      (e i) (he_idem i) i (hdim_hom i)) φ hφ ψ hψ

section CompleteSystem

/-- The diagonal matrix units form a complete family of orthogonal idempotents. -/
lemma RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.completeOrthogonalIdempotents_matrix_single
    {R : Type*} [CommSemiring R] {n : ℕ} :
    CompleteOrthogonalIdempotents
      (fun j : Fin n => Matrix.single j j (1 : R)) := by
  refine CompleteOrthogonalIdempotents.iff_ortho_complete.mpr ⟨fun j k' hjk => ?_, ?_⟩
  · change Matrix.single j j 1 * Matrix.single k' k' 1 = 0
    ext r s
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero; intro x _
    by_cases hxj : j = r ∧ j = x <;> by_cases hxk : k' = x ∧ k' = s
    · exact absurd (hxj.2.trans hxk.1.symm) hjk
    all_goals simp_all
  ·
    have : ∑ j : Fin n, Matrix.single j j (1 : R) = Matrix.diagonal (fun _ => 1) := by
      funext r s
      simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply, ite_and]
      simp [Finset.sum_ite_eq']
    rw [this, Matrix.diagonal_one]

/-- The coordinate-supported diagonal matrix units form a complete family of orthogonal idempotents in a finite product. -/
lemma RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.completeOrthogonalIdempotents_pi_matrix_single
    {n : ℕ} {d : Fin n → ℕ}
    {R : Type*} [CommSemiring R] :
    CompleteOrthogonalIdempotents
      (fun (p : Σ l : Fin n, Fin (d l)) =>
        (Pi.single p.1 (Matrix.single p.2 p.2 (1 : R)) :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) R)) := by
  refine CompleteOrthogonalIdempotents.iff_ortho_complete.mpr ⟨fun ⟨l₁, j₁⟩ ⟨l₂, j₂⟩ hpq => ?_, ?_⟩
  ·
    funext k
    simp only [Pi.mul_apply, Pi.zero_apply]
    by_cases h₁ : l₁ = k <;> by_cases h₂ : l₂ = k
    · subst h₁; subst h₂
      simp only [Pi.single_eq_same]
      have h2 : j₁ ≠ j₂ := fun h => hpq (Sigma.ext rfl (heq_of_eq h))
      ext r s
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero; intro x _
      by_cases hxp : j₁ = r ∧ j₁ = x <;> by_cases hxq : j₂ = x ∧ j₂ = s
      · exact absurd (hxp.2.trans hxq.1.symm) h2
      all_goals simp_all
    · simp [h₂]
    · simp [h₁]
    · simp [h₁, h₂]
  ·

    rw [show (∑ x : Σ l : Fin n, Fin (d l),
        (Pi.single x.1 (Matrix.single x.2 x.2 (1 : R)) :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) R)) =
        ∑ l : Fin n, ∑ j : Fin (d l), Pi.single l (Matrix.single j j 1) from
      Fintype.sum_sigma _]

    have key : ∀ l : Fin n, ∑ j : Fin (d l),
        (Pi.single l (Matrix.single j j (1 : R)) :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) R) =
        Pi.single l 1 := by
      intro l
      rw [← completeOrthogonalIdempotents_matrix_single.complete]
      induction Finset.univ (α := Fin (d l)) using Finset.cons_induction with
      | empty => simp
      | cons j s hj ih =>
        simp only [Finset.sum_cons]
        rw [Pi.single_add, ih]
    simp_rw [key]
    exact Finset.univ_sum_single 1

/-- An auxiliary result. -/
lemma RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.auxiliary_result
    [IsAlgClosed k] [IsArtinianRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] M i)) :
    ∃ (e : (Σ i : ι, Fin (Module.finrank k (M i))) → A),
      CompleteOrthogonalIdempotents e ∧
      ∀ (p : Σ i : ι, Fin (Module.finrank k (M i))) (j : ι),
        Module.finrank k (module_scalar_submodule (k := k) (A := A) (M j) (e p)) =
          if p.fst = j then 1 else 0 := by

  haveI : IsSemiprimaryRing A := inferInstance
  haveI hss : IsSemisimpleRing (A ⧸ Ring.jacobson A) := IsSemiprimaryRing.isSemisimpleRing
  have hnil := IsSemiprimaryRing.isNilpotent (R := A)

  have hann : ∀ i, Ring.jacobson A ≤ Module.annihilator A (M i) :=
    fun i => IsSemisimpleModule.jacobson_le_annihilator A (M i)

  let π := Ideal.Quotient.mk (Ring.jacobson A)
  haveI : Module.Finite k (A ⧸ Ring.jacobson A) := inferInstance
  obtain ⟨n, d, hd, ⟨WA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (A ⧸ Ring.jacobson A)

  have hsmul_eq : ∀ (a a' : A) (j : ι) (m : M j),
      π a = π a' → a • m = a' • m := by
    intro a a' j m hq
    have hmem : a - a' ∈ Ring.jacobson A := Ideal.Quotient.eq.mp hq
    have h0 := Module.mem_annihilator.mp (hann j hmem) m
    rwa [sub_smul, sub_eq_zero] at h0
  have hsmulRange_eq : ∀ (a a' : A) (j : ι),
      π a = π a' → module_scalar_submodule (k := k) (A := A) (M j) a = module_scalar_submodule (k := k) (A := A) (M j) a' := by
    intro a a' j hq
    have : module_scalar_linearMap (k := k) (A := A) (M j) a = module_scalar_linearMap (k := k) (A := A) (M j) a' := by
      ext m; exact hsmul_eq a a' j m hq
    simp only [module_scalar_submodule, this]

  let ebar : (Σ l : Fin n, Fin (d l)) → A ⧸ Ring.jacobson A :=
    fun p => WA.symm (Pi.single p.1 (Matrix.single p.2 p.2 (1 : k)))
  have hebar_coi : CompleteOrthogonalIdempotents ebar := by
    have h := completeOrthogonalIdempotents_pi_matrix_single (R := k) (n := n) (d := d)
    exact h.map WA.symm.toRingEquiv.toRingHom

  have hker : ∀ x ∈ RingHom.ker π, IsNilpotent x := by
    intro x hx
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨m, hm⟩ := hnil
    exact ⟨m, by
      have := Ideal.pow_mem_pow hx m
      rw [hm] at this
      exact Ideal.mem_bot.mp this⟩
  have hebar_range : ∀ p, ebar p ∈ π.range :=
    fun p => Ideal.Quotient.mk_surjective (ebar p)
  obtain ⟨e_raw, he_raw_coi, he_raw_lift⟩ :=
    CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker π hker hebar_coi hebar_range

  suffices h_block :
      ∃ (σ : ι → Fin n),
        Function.Bijective σ ∧
        (∀ i, d (σ i) = Module.finrank k (M i)) ∧
        (∀ (p : Σ l : Fin n, Fin (d l)) (j : ι),
          Module.finrank k (module_scalar_submodule (k := k) (A := A) (M j) (e_raw p)) =
            if σ j = p.fst then 1 else 0) by

    obtain ⟨σ, hσ_bij, hd_eq, hrank⟩ := h_block
    let σ_equiv : ι ≃ Fin n := Equiv.ofBijective σ hσ_bij

    let e : (Σ i : ι, Fin (Module.finrank k (M i))) → A :=
      fun p => e_raw ⟨σ p.1, (finCongr (hd_eq p.1).symm) p.2⟩

    have he_coi : CompleteOrthogonalIdempotents e := by

      let reindex : (Σ i : ι, Fin (Module.finrank k (M i))) → (Σ l : Fin n, Fin (d l)) :=
        fun p => ⟨σ p.1, (finCongr (hd_eq p.1).symm) p.2⟩
      have hreindex_bij : Function.Bijective reindex := by
        constructor
        · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
          simp only [reindex, Sigma.mk.injEq] at h
          obtain ⟨hi, hj⟩ := h
          have hi' := hσ_bij.1 hi
          subst hi'
          simp at hj
          exact Sigma.ext rfl (heq_of_eq hj)
        · rintro ⟨l, j⟩
          have hl : σ (σ_equiv.symm l) = l := σ_equiv.apply_symm_apply l
          have hdl : d l = Module.finrank k (M (σ_equiv.symm l)) := by
            have := hd_eq (σ_equiv.symm l); rwa [hl] at this
          refine ⟨⟨σ_equiv.symm l, finCongr hdl j⟩, ?_⟩
          simp only [reindex, Sigma.mk.injEq]
          refine ⟨hl, ?_⟩
          have hdl2 : d (σ (σ_equiv.symm l)) = d l := by rw [hl]
          rw [Fin.heq_ext_iff hdl2]
          simp [finCongr]
      let reindex_equiv := Equiv.ofBijective reindex hreindex_bij
      have hcomp : e = e_raw ∘ reindex_equiv := funext fun ⟨i, j⟩ => rfl
      rw [hcomp]
      have hortho := (OrthogonalIdempotents.equiv reindex_equiv).mpr
        he_raw_coi.toOrthogonalIdempotents
      exact ⟨hortho,
        by simp [Equiv.sum_comp reindex_equiv, he_raw_coi.complete]⟩
    refine ⟨e, he_coi, fun p j => ?_⟩

    change Module.finrank k (module_scalar_submodule (k := k) (A := A) (M j)
      (e_raw ⟨σ p.1, (finCongr (hd_eq p.1).symm) p.2⟩)) =
      if p.fst = j then 1 else 0

    have := hrank ⟨σ p.1, (finCongr (hd_eq p.1).symm) p.2⟩ j
    rw [this]

    congr 1; exact propext ⟨fun h => (hσ_bij.1 h).symm, fun h => congrArg σ h.symm⟩

  have hWA_mul : ∀ x y : ∀ l, Matrix (Fin (d l)) (Fin (d l)) k,
      WA.symm x * WA.symm y = WA.symm (x * y) := fun x y => (map_mul WA.symm x y).symm
  let c : Fin n → A ⧸ Ring.jacobson A := fun l => WA.symm (Pi.single l 1)
  have hc_comm : ∀ (l : Fin n) (q : A ⧸ Ring.jacobson A), c l * q = q * c l := by
    intro l q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    change WA.symm (Pi.single l 1) * π b = π b * WA.symm (Pi.single l 1)
    rw [show π b = WA.symm (WA (π b)) from (WA.symm_apply_apply _).symm]
    rw [hWA_mul, hWA_mul]; congr 1; exact pi_single_one_mul_comm l (WA (π b))
  have hsmulRange_A_sub : ∀ (j : ι) (l : Fin n) (a : A) (ha : π a = c l),
      ∀ (b : A) (x : M j), x ∈ module_scalar_submodule (k := k) (A := A) (M j) a →
        b • x ∈ module_scalar_submodule (k := k) (A := A) (M j) a := by
    intro j l a ha b x ⟨m, hm⟩
    rw [← hm]
    have hcomm : π (b * a) = π (a * b) := by
      rw [map_mul, map_mul, ha]; exact (hc_comm l (π b)).symm
    change b • (a • m) ∈ module_scalar_submodule (k := k) (A := A) (M j) a
    rw [← mul_smul, hsmul_eq _ _ j _ hcomm, mul_smul]; exact ⟨b • m, rfl⟩
  have hsmulRange_bot_or_top : ∀ (j : ι) (l : Fin n) (a : A) (ha : π a = c l),
      module_scalar_submodule (k := k) (A := A) (M j) a = ⊥ ∨
        module_scalar_submodule (k := k) (A := A) (M j) a = ⊤ := by
    intro j l a ha
    let N : Submodule A (M j) :=
      { carrier := (module_scalar_submodule (k := k) (A := A) (M j) a : Set (M j))
        add_mem' := (module_scalar_submodule (k := k) (A := A) (M j) a).add_mem
        zero_mem' := (module_scalar_submodule (k := k) (A := A) (M j) a).zero_mem
        smul_mem' := fun b x hx => hsmulRange_A_sub j l a ha b x hx }
    rcases IsSimpleOrder.eq_bot_or_eq_top N with h | h
    · left; ext x; constructor
      · intro hx; have : x ∈ N := hx; rw [h] at this
        exact (Submodule.mem_bot A).mp this
      · intro hx; rw [hx]; exact (module_scalar_submodule (k := k) (A := A) (M j) a).zero_mem
    · right; ext x; constructor
      · intro _; exact Submodule.mem_top
      · intro _; have : x ∈ N := by rw [h]; exact Submodule.mem_top
        exact this
  have hcoi := completeOrthogonalIdempotents_pi_single_one
    (S := fun l => Matrix (Fin (d l)) (Fin (d l)) k)
  have hc_sum : ∑ l, c l = 1 := by
    change ∑ l, WA.symm (Pi.single l 1) = 1
    rw [← map_sum, hcoi.complete, map_one WA.symm]
  have hblock_exists : ∀ j : ι, ∃ l : Fin n, ∀ a : A,
      π a = WA.symm (Pi.single l 1) →
      module_scalar_submodule (k := k) (A := A) (M j) a = ⊤ := by
    intro j; by_contra h_none; push Not at h_none
    have hall_bot : ∀ l : Fin n, ∀ a : A, π a = c l →
        module_scalar_submodule (k := k) (A := A) (M j) a = ⊥ := by
      intro l a ha
      obtain ⟨a₀, ha₀, hne⟩ := h_none l
      rcases hsmulRange_bot_or_top j l a₀ ha₀ with h | h
      · rwa [hsmulRange_eq a a₀ j (ha.trans ha₀.symm)]
      · exact absurd h hne
    haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
    obtain ⟨m, hm⟩ := exists_ne (0 : M j)
    apply hm
    have hlift : ∀ l : Fin n, ∃ a : A, π a = c l := fun l => Ideal.Quotient.mk_surjective (c l)
    choose a_l ha_l using hlift
    have hsum_img : π (∑ l, a_l l) = 1 := by
      rw [map_sum]; simp_rw [ha_l]; exact hc_sum
    have hsum_act : (∑ l, a_l l) • m = m := by
      have := hsmul_eq (∑ l, a_l l) 1 j m (by rw [hsum_img, map_one])
      rwa [one_smul] at this
    rw [← hsum_act, Finset.sum_smul]
    apply Finset.sum_eq_zero; intro l _
    have h0 := hall_bot l (a_l l) (ha_l l)
    have : a_l l • m ∈ module_scalar_submodule (k := k) (A := A) (M j) (a_l l) := ⟨m, rfl⟩
    rw [h0] at this; exact (Submodule.mem_bot k).mp this
  have hblock_unique : ∀ j : ι, ∀ l₁ l₂ : Fin n,
      (∀ a : A, π a = WA.symm (Pi.single l₁ 1) →
        module_scalar_submodule (k := k) (A := A) (M j) a = ⊤) →
      (∀ a : A, π a = WA.symm (Pi.single l₂ 1) →
        module_scalar_submodule (k := k) (A := A) (M j) a = ⊤) →
      l₁ = l₂ := by
    intro j l₁ l₂ h₁ h₂; by_contra hne
    have horth : c l₁ * c l₂ = 0 :=
      (hcoi.toOrthogonalIdempotents.map WA.symm.toRingEquiv.toRingHom).ortho hne
    obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective (c l₁)
    obtain ⟨a₂, ha₂⟩ := Ideal.Quotient.mk_surjective (c l₂)
    have h₂_top := h₂ a₂ ha₂
    have hprod_img : π (a₁ * a₂) = 0 := by rw [map_mul, ha₁, ha₂, horth]
    have hprod_zero : ∀ m : M j, (a₁ * a₂) • m = 0 := by
      intro m
      have h0 := hsmul_eq (a₁ * a₂) 0 j m (by rw [hprod_img, map_zero])
      rwa [zero_smul] at h0
    have h₁_top := h₁ a₁ ha₁
    haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
    have ha₁_zero : ∀ m : M j, a₁ • m = 0 := by
      intro m
      have : m ∈ module_scalar_submodule (k := k) (A := A) (M j) a₂ := by
        rw [h₂_top]; exact Submodule.mem_top
      obtain ⟨m₀, hm₀⟩ := this; change a₂ • m₀ = m at hm₀
      rw [← hm₀, ← mul_smul]; exact hprod_zero m₀
    have : module_scalar_submodule (k := k) (A := A) (M j) a₁ = ⊥ := by
      ext x; simp only [Submodule.mem_bot]; constructor
      · rintro ⟨m, rfl⟩; exact ha₁_zero m
      · intro hx; rw [hx]; exact (module_scalar_submodule (k := k) (A := A) (M j) a₁).zero_mem
    rw [this] at h₁_top; exact bot_ne_top h₁_top

  let σ : ι → Fin n := fun j => (hblock_exists j).choose
  have hσ_spec : ∀ j a, π a = WA.symm (Pi.single (σ j) 1) →
      module_scalar_submodule (k := k) (A := A) (M j) a = ⊤ :=
    fun j => (hblock_exists j).choose_spec
  have hc_idem : ∀ l', IsIdempotentElem (c l') :=
    (hcoi.toOrthogonalIdempotents.map WA.symm.toRingEquiv.toRingHom).idem
  have hc_identity : ∀ (p : ι) (a : A) (ha : π a = c (σ p)),
      ∀ m : M p, a • m = m := by
    intro p a ha m
    have h_top := hσ_spec p a ha
    have ⟨m₀, hm₀⟩ : m ∈ module_scalar_submodule (k := k) (A := A) (M p) a := by
      rw [h_top]; exact Submodule.mem_top
    change a • m₀ = m at hm₀
    rw [← hm₀, ← mul_smul]
    exact hsmul_eq (a * a) a p m₀ (by rw [map_mul, ha, (hc_idem (σ p)).eq])
  have hc_zero : ∀ (p : ι) (l' : Fin n) (hl' : l' ≠ σ p) (a : A)
      (ha : π a = c l'), ∀ m : M p, a • m = 0 := by
    intro p l' hl' a ha m
    rcases hsmulRange_bot_or_top p l' a ha with h | h
    · have : a • m ∈ module_scalar_submodule (k := k) (A := A) (M p) a := ⟨m, rfl⟩
      rw [h] at this; exact (Submodule.mem_bot k).mp this
    · exfalso; exact hl' (hblock_unique p l' (σ p)
        (fun a' ha' => hsmulRange_eq a' a p (ha'.trans ha.symm) ▸ h) (hσ_spec p))

  have hσ_inj : Function.Injective σ := by
    intro i j hij; apply hM i j
    set l := σ i with hl_def
    have hlj : σ j = l := hij.symm
    let lft : (A ⧸ Ring.jacobson A) → A := fun q => (Ideal.Quotient.mk_surjective q).choose
    have hlft : ∀ q, π (lft q) = q := fun q => (Ideal.Quotient.mk_surjective q).choose_spec
    let matAct : ∀ p : ι, Matrix (Fin (d l)) (Fin (d l)) k → M p → M p :=
      fun p mat m => lft (WA.symm (Pi.single l mat)) • m
    have hdecomp : ∀ (p : ι) (hp : σ p = l) (a : A) (m : M p),
        a • m = matAct p ((WA (π a)) l) m := by
      intro p hp a m
      have hid := hc_identity p (lft (c l)) (by rw [hlft]; exact (congrArg c hp).symm ▸ rfl)
      conv_lhs => rw [show a • m = (a * lft (c l)) • m from by rw [mul_smul, hid m]]
      apply hsmul_eq; simp only [map_mul, hlft]
      conv_lhs => rw [show π a = WA.symm (WA (π a)) from (WA.symm_apply_apply _).symm,
                       show c l = WA.symm (Pi.single l 1) from rfl]
      rw [hWA_mul]; congr 1; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · simp [Pi.mul_apply, show l ≠ l' from fun h => hl' h.symm]
    have hpi_single_mul : ∀ (x y : Matrix (Fin (d l)) (Fin (d l)) k),
        Pi.single l x * Pi.single l y =
          (Pi.single l (x * y) : ∀ l', Matrix (Fin (d l')) (Fin (d l')) k) := by
      intro x y; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · have hne : l ≠ l' := fun h => hl' h.symm
        simp [Pi.mul_apply, hne]
    have hmatAct_mul : ∀ (p : ι) (mat1 mat2 : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p),
        matAct p (mat1 * mat2) m = matAct p mat1 (matAct p mat2 m) := by
      intro p mat1 mat2 m
      change lft (WA.symm (Pi.single l (mat1 * mat2))) • m =
        lft (WA.symm (Pi.single l mat1)) • (lft (WA.symm (Pi.single l mat2)) • m)
      rw [← mul_smul]; apply hsmul_eq
      rw [map_mul, hlft, hlft]; conv_rhs => rw [hlft]
      rw [hWA_mul, hpi_single_mul]
    have hmatAct_add : ∀ (p : ι) (mat1 mat2 : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p),
        matAct p (mat1 + mat2) m = matAct p mat1 m + matAct p mat2 m := by
      intro p mat1 mat2 m
      change lft (WA.symm (Pi.single l (mat1 + mat2))) • m =
        lft (WA.symm (Pi.single l mat1)) • m + lft (WA.symm (Pi.single l mat2)) • m
      rw [← add_smul]; apply hsmul_eq
      rw [map_add, hlft, hlft]; conv_rhs => rw [hlft]
      rw [show WA.symm (Pi.single l mat1) + WA.symm (Pi.single l mat2) =
            WA.symm (Pi.single l mat1 + Pi.single l mat2) from (map_add WA.symm _ _).symm]
      congr 1; funext l'
      by_cases hl' : l' = l
      · subst hl'; simp [Pi.single_eq_same]
      · have hne : l ≠ l' := fun h => hl' h.symm
        simp [hne]
    have hmatAct_one : ∀ (p : ι) (hp : σ p = l) (m : M p), matAct p 1 m = m := by
      intro p hp m
      exact hc_identity p (lft (c l)) (by rw [hlft]; exact (congrArg c hp).symm ▸ rfl) m
    have hmatAct_zero : ∀ (p : ι) (m : M p), matAct p 0 m = 0 := by
      intro p m
      have : lft (WA.symm (Pi.single l 0)) • m = (0 : A) • m := by
        apply hsmul_eq; rw [hlft, map_zero, Pi.single_zero, map_zero]
      exact this.trans (zero_smul A m)
    letI instMi : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M i) :=
      { smul := matAct i
        one_smul := hmatAct_one i rfl
        mul_smul := hmatAct_mul i
        smul_zero := fun _ => smul_zero _
        smul_add := fun _ => smul_add _
        add_smul := hmatAct_add i
        zero_smul := hmatAct_zero i }
    letI instMj : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M j) :=
      { smul := matAct j
        one_smul := hmatAct_one j hlj
        mul_smul := hmatAct_mul j
        smul_zero := fun _ => smul_zero _
        smul_add := fun _ => smul_add _
        add_smul := hmatAct_add j
        zero_smul := hmatAct_zero j }
    have hMatSimple : ∀ (p : ι) (hp : σ p = l)
        (inst : Module (Matrix (Fin (d l)) (Fin (d l)) k) (M p)),
        (∀ (mat : Matrix (Fin (d l)) (Fin (d l)) k) (m : M p), mat • m = matAct p mat m) →
        @IsSimpleModule (Matrix (Fin (d l)) (Fin (d l)) k) _ (M p) _ inst := by
      intro p hp inst hsmul_def
      haveI : Nontrivial (M p) := IsSimpleModule.nontrivial A (M p)
      exact
        { eq_bot_or_eq_top := fun N => by
            let N_A : Submodule A (M p) :=
              { carrier := N.carrier
                add_mem' := N.add_mem'
                zero_mem' := N.zero_mem'
                smul_mem' := fun a x hx => by
                  rw [hdecomp p hp a x, ← hsmul_def]; exact N.smul_mem _ hx }
            rcases IsSimpleOrder.eq_bot_or_eq_top N_A with h | h
            · left; ext x; simp only [Submodule.mem_bot]
              exact ⟨fun hx => (Submodule.eq_bot_iff _).mp h x hx,
                     fun hx => hx ▸ N.zero_mem⟩
            · right; ext x
              exact ⟨fun _ => trivial,
                     fun _ => (Submodule.eq_top_iff'.mp h x : x ∈ N_A)⟩ }
    haveI hSimMi := hMatSimple i rfl instMi (fun _ _ => rfl)
    haveI hSimMj := hMatSimple j hlj instMj (fun _ _ => rfl)
    haveI : IsSimpleRing (Matrix (Fin (d l)) (Fin (d l)) k) := by
      haveI := hd l; exact IsSimpleRing.matrix (Fin (d l)) k
    haveI : IsArtinianRing (Matrix (Fin (d l)) (Fin (d l)) k) := inferInstance
    obtain ⟨f⟩ := @nonempty_linearEquiv_of_simple_artinian
      (Matrix (Fin (d l)) (Fin (d l)) k) _ _ _ (M i) (M j) _ instMi hSimMi _ instMj hSimMj
    exact ⟨{ toFun := f
             invFun := f.symm
             left_inv := f.left_inv
             right_inv := f.right_inv
             map_add' := f.map_add
             map_smul' := fun a m => by
               simp only [RingHom.id_apply]
               rw [hdecomp i rfl a m, hdecomp j hlj a (f m)]
               exact f.map_smul ((WA (π a)) l) m }⟩

  have hrank : ∀ (p : Σ l : Fin n, Fin (d l)) (j : ι),
      Module.finrank k (module_scalar_submodule (k := k) (A := A) (M j) (e_raw p)) =
        if σ j = p.fst then 1 else 0 := by
    intro ⟨l, j_idx⟩ j

    have he_lift : π (e_raw ⟨l, j_idx⟩) =
        WA.symm (Pi.single l (Matrix.single j_idx j_idx (1 : k))) :=
      congr_fun he_raw_lift ⟨l, j_idx⟩
    split_ifs with hlj
    ·
      subst hlj

      have ha_idem : ∀ m : M j, e_raw ⟨σ j, j_idx⟩ • (e_raw ⟨σ j, j_idx⟩ • m) =
          e_raw ⟨σ j, j_idx⟩ • m := by
        intro m; rw [← mul_smul]
        exact hsmul_eq _ _ j m (by
          rw [map_mul, he_lift, hWA_mul]; congr 1
          rw [← Pi.single_mul_left, Pi.single_eq_same]; congr 1
          exact (isIdempotentElem_matrix_single j_idx).eq)

      have ha_ne_zero : ∃ m₀ : M j, e_raw ⟨σ j, j_idx⟩ • m₀ ≠ 0 := by
        by_contra hall; push Not at hall
        have h_prod_zero : ∀ (b₁ b₂ : A) (m : M j),
            (b₁ * e_raw ⟨σ j, j_idx⟩ * b₂) • m = 0 := by
          intro b₁ b₂ m; rw [mul_smul, mul_smul, hall, smul_zero]
        haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
        obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M j)
        apply hm₀

        have h_sum_eq_c : ∑ k' : Fin (d (σ j)),
            WA.symm (Pi.single (σ j) (Matrix.single k' j_idx 1)) *
            WA.symm (Pi.single (σ j) (Matrix.single j_idx j_idx 1)) *
            WA.symm (Pi.single (σ j) (Matrix.single j_idx k' 1)) = c (σ j) := by
          simp_rw [hWA_mul, ← Pi.single_mul_left, Pi.single_eq_same,
            Matrix.single_mul_mul_single, one_mul, mul_one]
          simp_rw [show (Matrix.single j_idx j_idx (1 : k))
            j_idx j_idx = 1 from by simp ]
          rw [show c (σ j) = WA.symm (Pi.single (σ j) 1) from rfl]
          rw [show ∑ x, WA.symm (Pi.single (σ j) (Matrix.single x x (1 : k))) =
            WA.symm (∑ x, Pi.single (σ j) (Matrix.single x x (1 : k))) from
            (map_sum WA.symm.toRingHom _ _).symm]
          congr 1; funext l'; by_cases hl' : l' = σ j
          · subst hl'; simp only [Pi.single_eq_same, Finset.sum_apply]
            ext r s
            simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
            split_ifs with h
            · subst h; simp [Finset.mem_univ]
            · apply Finset.sum_eq_zero; intro x _
              simp [show ¬(x = r ∧ x = s) from fun ⟨h1, h2⟩ => h (h1.symm.trans h2)]
          · simp [Finset.sum_apply, hl']
        let b₁ : Fin (d (σ j)) → A := fun k' =>
          (Ideal.Quotient.mk_surjective (WA.symm (Pi.single (σ j)
            (Matrix.single k' j_idx 1)))).choose
        let b₂ : Fin (d (σ j)) → A := fun k' =>
          (Ideal.Quotient.mk_surjective (WA.symm (Pi.single (σ j)
            (Matrix.single j_idx k' 1)))).choose
        have hb₁ : ∀ k', π (b₁ k') = WA.symm (Pi.single (σ j)
            (Matrix.single k' j_idx 1)) :=
          fun k' => (Ideal.Quotient.mk_surjective _).choose_spec
        have hb₂ : ∀ k', π (b₂ k') = WA.symm (Pi.single (σ j)
            (Matrix.single j_idx k' 1)) :=
          fun k' => (Ideal.Quotient.mk_surjective _).choose_spec
        have hsum_zero : (∑ k', b₁ k' * e_raw ⟨σ j, j_idx⟩ * b₂ k') • m₀ = 0 := by
          rw [Finset.sum_smul]
          exact Finset.sum_eq_zero (fun k' _ => h_prod_zero _ _ m₀)
        have hsum_lifts : π (∑ k', b₁ k' * e_raw ⟨σ j, j_idx⟩ * b₂ k') = c (σ j) := by
          rw [map_sum]; simp_rw [map_mul, hb₁, hb₂, he_lift]; exact h_sum_eq_c
        rw [← hc_identity j _ hsum_lifts m₀]; exact hsum_zero

      obtain ⟨m₀, hm₀⟩ := ha_ne_zero
      set v₀ := e_raw ⟨σ j, j_idx⟩ • m₀ with hv₀_def
      have hav₀ : e_raw ⟨σ j, j_idx⟩ • v₀ = v₀ := ha_idem m₀

      have hscalar : ∀ m' : M j,
          e_raw ⟨σ j, j_idx⟩ • m' ∈ Submodule.span k {v₀} := by
        intro m'
        haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
        have hgen : Submodule.span A {v₀} = ⊤ := by
          rcases IsSimpleOrder.eq_bot_or_eq_top (Submodule.span A {v₀}) with h | h
          · exfalso; exact hm₀ ((Submodule.eq_bot_iff _).mp h v₀ (Submodule.subset_span rfl))
          · exact h
        have hm'_mem : m' ∈ Submodule.span A {v₀} := hgen ▸ Submodule.mem_top
        rw [Submodule.mem_span_singleton] at hm'_mem
        obtain ⟨b, rfl⟩ := hm'_mem
        rw [← mul_smul]
        have hab_eq : (e_raw ⟨σ j, j_idx⟩ * b) • v₀ =
            (e_raw ⟨σ j, j_idx⟩ * b * e_raw ⟨σ j, j_idx⟩) • v₀ := by
          conv_lhs => rw [← hav₀]; rw [← mul_smul]
        rw [hab_eq]
        set c_val := (WA (π b)) (σ j) j_idx j_idx with hc_val_def
        have hpi_aba : π (e_raw ⟨σ j, j_idx⟩ * b * e_raw ⟨σ j, j_idx⟩) =
            π ((algebraMap k A c_val) * e_raw ⟨σ j, j_idx⟩) := by
          apply WA.injective
          have hWAe : WA (π (e_raw ⟨σ j, j_idx⟩)) = Pi.single (σ j)
              (Matrix.single j_idx j_idx (1 : k)) := by
            rw [he_lift]; exact WA.apply_symm_apply _
          simp only [map_mul, hWAe]
          rw [← Pi.single_mul_left, ← Pi.single_mul_left,
              Pi.single_eq_same, matrix_single_mul_mul_matrix_single]
          rw [Ideal.Quotient.mk_algebraMap, WA.commutes]
          ext l'; by_cases hl' : l' = σ j
          · subst hl'
            simp only [Pi.single_eq_same, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
              Pi.smul_apply, Pi.one_apply, Matrix.smul_apply, smul_eq_mul, one_mul,
              smul_mul_assoc, hc_val_def]
          · simp [Pi.mul_apply, hl']
        have : (e_raw ⟨σ j, j_idx⟩ * b * e_raw ⟨σ j, j_idx⟩) • v₀ = c_val • v₀ := by
          have h := hsmul_eq (e_raw ⟨σ j, j_idx⟩ * b * e_raw ⟨σ j, j_idx⟩)
            ((algebraMap k A c_val) * e_raw ⟨σ j, j_idx⟩) j v₀ hpi_aba
          rw [h, mul_smul, hav₀, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem _ c_val (Submodule.subset_span rfl)

      have hspan : module_scalar_submodule (k := k) (A := A) (M j) (e_raw ⟨σ j, j_idx⟩) =
          Submodule.span k {v₀} := by
        ext w; constructor
        · rintro ⟨m', rfl⟩; exact hscalar m'
        · intro hw
          rw [Submodule.mem_span_singleton] at hw
          obtain ⟨c_val, rfl⟩ := hw
          exact ⟨c_val • m₀, by
            simp [module_scalar_linearMap, hv₀_def]⟩
      rw [hspan]; exact finrank_span_singleton hm₀
    ·

      have hfactor : π (e_raw ⟨l, j_idx⟩) = c l * π (e_raw ⟨l, j_idx⟩) := by
        rw [he_lift, show c l = WA.symm (Pi.single l 1) from rfl, hWA_mul]
        congr 1; rw [← Pi.single_mul_left]; simp
      obtain ⟨a_c, ha_c⟩ := Ideal.Quotient.mk_surjective (c l)
      have hc_bot : module_scalar_submodule (k := k) (A := A) (M j) a_c = ⊥ := by
        rcases hsmulRange_bot_or_top j l a_c ha_c with h | h
        · exact h
        · exfalso; exact hlj (hblock_unique j l (σ j)
            (fun a' ha' => hsmulRange_eq a' a_c j (ha'.trans ha_c.symm) ▸ h) (hσ_spec j)).symm
      have ha_zero : ∀ m : M j, e_raw ⟨l, j_idx⟩ • m = 0 := by
        intro m
        have hca_zero : ∀ m : M j, a_c • m = 0 := by
          intro m'
          have : a_c • m' ∈ module_scalar_submodule (k := k) (A := A) (M j) a_c := ⟨m', rfl⟩
          rw [hc_bot] at this; exact (Submodule.mem_bot k).mp this
        have := hsmul_eq (a_c * e_raw ⟨l, j_idx⟩) (e_raw ⟨l, j_idx⟩) j m
          (by rw [map_mul, ha_c]; exact hfactor.symm)
        rw [mul_smul] at this; rw [← this, hca_zero]
      have hbot : module_scalar_submodule (k := k) (A := A) (M j) (e_raw ⟨l, j_idx⟩) = ⊥ := by
        ext x; simp only [Submodule.mem_bot]; constructor
        · rintro ⟨m, rfl⟩; exact ha_zero m
        · intro hx; rw [hx]; exact (module_scalar_submodule (k := k) (A := A) (M j) (e_raw ⟨l, j_idx⟩)).zero_mem
      rw [hbot]; simp

  have hMi_finite : ∀ i, Module.Finite k (M i) := by
    intro i
    haveI : Nontrivial (M i) := IsSimpleModule.nontrivial A (M i)
    obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M i)
    haveI : Module.Finite A (M i) := by
      refine ⟨⟨{m₀}, ?_⟩⟩
      rw [Finset.coe_singleton, eq_top_iff]
      exact le_of_eq ((eq_bot_or_eq_top (Submodule.span A {m₀})).resolve_left (fun h => hm₀ (by
        have := h.le (Submodule.mem_span_singleton_self m₀)
        rwa [Submodule.mem_bot] at this))).symm
    exact Module.Finite.trans A (M i)

  have hd_eq : ∀ i, d (σ i) = Module.finrank k (M i) := by
    intro i
    haveI := hMi_finite i

    have hne_zero : ∀ j : Fin (d (σ i)), ∃ v : M i,
        v ∈ module_scalar_submodule (k := k) (A := A) (M i) (e_raw ⟨σ i, j⟩) ∧ v ≠ 0 := by
      intro j
      have h1 : Module.finrank k (module_scalar_submodule (k := k) (A := A) (M i) (e_raw ⟨σ i, j⟩)) = 1 := by
        have := hrank ⟨σ i, j⟩ i; simp at this; exact this
      have hne_bot : module_scalar_submodule (k := k) (A := A) (M i) (e_raw ⟨σ i, j⟩) ≠ ⊥ := by
        intro hbot; rw [hbot, finrank_bot] at h1; exact absurd h1 (by omega)
      exact (Submodule.ne_bot_iff _).mp hne_bot
    choose v hv_mem hv_ne using hne_zero

    have hv_idem : ∀ j, e_raw ⟨σ i, j⟩ • v j = v j := by
      intro j
      obtain ⟨m, hm⟩ := hv_mem j; change e_raw ⟨σ i, j⟩ • m = v j at hm
      rw [← hm, ← mul_smul]
      exact hsmul_eq _ _ i _ (congrArg π
        (he_raw_coi.toOrthogonalIdempotents.idem ⟨σ i, j⟩))

    have hv_ortho : ∀ j j' : Fin (d (σ i)), j ≠ j' →
        e_raw ⟨σ i, j'⟩ • v j = 0 := by
      intro j j' hjj'
      obtain ⟨m, hm⟩ := hv_mem j; change e_raw ⟨σ i, j⟩ • m = v j at hm
      have hortho : e_raw ⟨σ i, j'⟩ * e_raw ⟨σ i, j⟩ = 0 :=
        he_raw_coi.toOrthogonalIdempotents.ortho (fun h => hjj' (by
          exact (eq_of_heq (Sigma.mk.inj h).2).symm))
      rw [← hm, ← mul_smul]
      exact (hsmul_eq _ 0 i m (congrArg π hortho)).trans (zero_smul A m)

    have hzero_act : ∀ (l : Fin n) (j_idx : Fin (d l)), l ≠ σ i →
        ∀ m : M i, e_raw ⟨l, j_idx⟩ • m = 0 := by
      intro l j_idx hl m
      have h0 := hrank ⟨l, j_idx⟩ i; simp [Ne.symm hl] at h0

      have hmem : e_raw ⟨l, j_idx⟩ • m ∈ module_scalar_submodule (k := k) (A := A) (M i) (e_raw ⟨l, j_idx⟩) :=
        ⟨m, rfl⟩
      rwa [h0, Submodule.mem_bot (R := k)] at hmem

    have hblock_id : ∀ m : M i, ∑ j : Fin (d (σ i)), e_raw ⟨σ i, j⟩ • m = m := by
      intro m
      have hπ_eq : π (∑ p : (Σ l : Fin n, Fin (d l)), e_raw p) = π 1 := by
        have hpw : ∀ p, π (e_raw p) = ebar p := congr_fun he_raw_lift
        simp only [map_sum, hpw, hebar_coi.complete, map_one]
      have hfull : (∑ p : (Σ l : Fin n, Fin (d l)), e_raw p) • m = m :=
        (hsmul_eq _ 1 i m hπ_eq).trans (one_smul A m)
      rw [Finset.sum_smul] at hfull
      rw [show (∑ x : (Σ l : Fin n, Fin (d l)), e_raw x • m) =
        ∑ l : Fin n, ∑ j : Fin (d l), e_raw ⟨l, j⟩ • m from Fintype.sum_sigma _] at hfull
      have hother : ∀ l : Fin n, l ≠ σ i →
          (∑ j : Fin (d l), e_raw ⟨l, j⟩ • m) = 0 :=
        fun l hl => Finset.sum_eq_zero (fun j _ => hzero_act l j hl m)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (σ i))] at hfull
      have hzero : (∑ x ∈ Finset.univ.erase (σ i), ∑ j : Fin (d x), e_raw ⟨x, j⟩ • m) = 0 :=
        Finset.sum_eq_zero (fun l hl => hother l (Finset.mem_erase.mp hl).1)
      rw [hzero, add_zero] at hfull
      exact hfull

    have hv_span : ∀ m : M i, m ∈ Submodule.span k (Set.range v) := by
      intro m; rw [← hblock_id m]
      apply Submodule.sum_mem; intro j _
      have hmem : e_raw ⟨σ i, j⟩ • m ∈ module_scalar_submodule (k := k) (A := A) (M i) (e_raw ⟨σ i, j⟩) := ⟨m, rfl⟩
      have h1 := hrank ⟨σ i, j⟩ i; simp at h1
      have hle : Submodule.span k {v j} ≤ module_scalar_submodule (k := k) (A := A) (M i) (e_raw ⟨σ i, j⟩) :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hv_mem j))
      haveI : FiniteDimensional k ↥(module_scalar_submodule (k := k) (A := A) (M i) (e_raw ⟨σ i, j⟩)) :=
        Submodule.finiteDimensional_of_le (le_top)
      have heq : module_scalar_submodule (k := k) (A := A) (M i) (e_raw ⟨σ i, j⟩) = Submodule.span k {v j} :=
        le_antisymm (Submodule.eq_of_le_of_finrank_le hle (by
          rw [h1, finrank_span_singleton (hv_ne j)])).symm.le hle
      rw [heq] at hmem; rw [Submodule.mem_span_singleton] at hmem
      obtain ⟨c_val, hc⟩ := hmem; rw [← hc]
      exact Submodule.smul_mem _ c_val (Submodule.subset_span ⟨j, rfl⟩)

    have hv_indep : LinearIndependent k v := by
      rw [linearIndependent_iff']; intro s g hg idx₀ hidx₀
      have key : ∑ x ∈ s, g x • (e_raw ⟨σ i, idx₀⟩ • v x) = 0 := by
        calc ∑ x ∈ s, g x • (e_raw ⟨σ i, idx₀⟩ • v x)
            = ∑ x ∈ s, e_raw ⟨σ i, idx₀⟩ • (g x • v x) := by
              congr 1; ext x; rw [smul_comm]
          _ = e_raw ⟨σ i, idx₀⟩ • ∑ x ∈ s, g x • v x := (Finset.smul_sum.symm)
          _ = e_raw ⟨σ i, idx₀⟩ • 0 := by rw [hg]
          _ = 0 := smul_zero _
      have hif : ∀ x, e_raw ⟨σ i, idx₀⟩ • v x = if x = idx₀ then v idx₀ else 0 := by
        intro x; by_cases hxj : x = idx₀
        · rw [if_pos hxj, hxj]; exact hv_idem idx₀
        · rw [if_neg hxj]; exact hv_ortho x idx₀ hxj
      simp_rw [hif] at key
      simp only [smul_ite, smul_zero, Finset.sum_ite_eq'] at key
      rw [if_pos hidx₀] at key
      exact smul_eq_zero.mp key |>.resolve_right (hv_ne idx₀)

    have htop : ⊤ ≤ Submodule.span k (Set.range v) := fun m _ => hv_span m
    rw [← Fintype.card_fin (d (σ i))]
    exact (Module.finrank_eq_card_basis (Module.Basis.mk hv_indep htop)).symm

  have hσ_surj : Function.Surjective σ := by
    intro l₀
    by_contra h_not
    push Not at h_not

    haveI := hd l₀
    set p : Σ l : Fin n, Fin (d l) := ⟨l₀, 0⟩ with hp_def
    have h_ann : ∀ j : ι, ∀ m : M j, e_raw p • m = 0 := by
      intro j m
      have hfr := hrank p j
      have hne : σ j ≠ l₀ := h_not j
      rw [if_neg hne] at hfr
      haveI := hMi_finite j
      have h_bot : module_scalar_submodule (k := k) (A := A) (M j) (e_raw p) = ⊥ := by
        have : Module.Finite k ↥(module_scalar_submodule (k := k) (A := A) (M j) (e_raw p)) :=
          Submodule.finiteDimensional_of_le le_top
        exact (Submodule.finrank_eq_zero (R := k)).mp hfr
      have : e_raw p • m ∈ module_scalar_submodule (k := k) (A := A) (M j) (e_raw p) := ⟨m, rfl⟩
      rw [h_bot] at this; exact (Submodule.mem_bot k).mp this

    have h_in_J : e_raw p ∈ Ring.jacobson A := by
      rw [Ring.jacobson_eq_sInf_isMaximal]
      apply Submodule.mem_sInf.mpr
      intro I hI
      haveI : IsSimpleModule A (A ⧸ I) :=
        isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hI)
      obtain ⟨j₀, ⟨φ⟩⟩ := hM_exhaustive (A ⧸ I)

      have h_all_zero : ∀ x : A ⧸ I, (e_raw p) • x = 0 :=
        fun x => φ.injective (by rw [φ.map_smul, h_ann j₀, map_zero])

      have h0 := h_all_zero (I.mkQ 1)
      rw [show (e_raw p) • I.mkQ (1 : A) = I.mkQ (e_raw p) by
        simp only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]] at h0
      exact (Submodule.Quotient.mk_eq_zero I).mp h0

    have h_eq_zero : π (e_raw p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h_in_J

    have h_ne_zero : π (e_raw p) ≠ 0 := by
      have he := congr_fun he_raw_lift p
      simp only [Function.comp_apply] at he
      rw [he]; intro h
      have h1 : (Pi.single l₀ (Matrix.single (0 : Fin (d l₀)) 0 (1 : k)) :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) k) = 0 :=
        WA.symm.injective (by rw [map_zero]; exact h)
      have h2 := congr_fun h1 l₀
      rw [Pi.single_eq_same, Pi.zero_apply] at h2

      have h3 := congr_fun (congr_fun h2 (0 : Fin (d l₀))) (0 : Fin (d l₀))
      simp  at h3
    exact h_ne_zero h_eq_zero
  exact ⟨σ, ⟨hσ_inj, hσ_surj⟩, hd_eq, hrank⟩

end CompleteSystem

/-- A family of finite projective modules with Kronecker-delta linear-map dimensions decomposes the regular module as a direct sum with multiplicities given by the dimensions of the simple modules. -/
theorem RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.regularModule_linearEquiv_directSum
    [IsAlgClosed k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (P i))
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0) :
    Nonempty (A ≃ₗ[A] ⨁ (i : ι), Fin (Module.finrank k (M i)) → P i) := by

  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance

  suffices h_coi : ∃ (e : (Σ i : ι, Fin (Module.finrank k (M i))) → A),
      CompleteOrthogonalIdempotents e ∧
      ∀ (p : Σ i : ι, Fin (Module.finrank k (M i))) (j : ι),
        Module.finrank k (RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.module_scalar_submodule (k := k) (A := A) (M j) (e p)) =
          if p.fst = j then 1 else 0 by

    obtain ⟨e, he_coi, he_rank⟩ := h_coi

    set N : (Σ i : ι, Fin (Module.finrank k (M i))) → Submodule A A :=
      fun p => Submodule.span A ({e p} : Set A) with hN_def
    have hdim_hom : ∀ (p : Σ i : ι, Fin (Module.finrank k (M i))) (j : ι),
        Module.finrank k (↥(N p) →ₗ[A] M j) = if p.fst = j then 1 else 0 := by
      intro p j
      rw [RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.finrank_linearMap_span_eq_associated_submodule (k := k) (e p) (he_coi.idem p)]
      exact he_rank p j

    have hproj : ∀ p, Module.Projective A ↥(N p) :=
      fun p => RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.projective_span_singleton (e p) (he_coi.idem p)

    have hindec : ∀ p, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A ↥(N p) :=
      fun p => RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.span_singleton_satisfies_module_property (k := k) M hM hM_exhaustive
        (e p) (he_coi.idem p) p.1 (hdim_hom p)

    have hiso : ∀ p, Nonempty (↥(N p) ≃ₗ[A] P p.fst) := by
      intro p

      have hdim1 : Module.finrank k (↥(N p) →ₗ[A] M p.fst) = 1 := by
        rw [hdim_hom]; simp

      have hdim2 : Module.finrank k (P p.fst →ₗ[A] M p.fst) = 1 := by
        rw [hP]; simp

      haveI : Module.Finite k ↥(N p) :=
        Module.Finite.of_injective ((N p).subtype.restrictScalars k) Subtype.val_injective
      haveI : FiniteDimensional k ↥(N p) := inferInstance
      haveI : FiniteDimensional k (P p.fst) := Module.Finite.trans A (P p.fst)

      haveI : ∀ j, Module.Finite k (M j) := by
        intro j
        haveI : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
        obtain ⟨v, hv⟩ := exists_ne (0 : M j)
        let φ : A →ₗ[k] M j := (LinearMap.toSpanSingleton A (M j) v).restrictScalars k
        have hφ_surj : Function.Surjective φ := by
          intro m
          have hrange : LinearMap.range (LinearMap.toSpanSingleton A (M j) v) = ⊤ := by
            rcases IsSimpleOrder.eq_bot_or_eq_top
              (LinearMap.range (LinearMap.toSpanSingleton A (M j) v)) with h | h
            · exact absurd (show v = 0 from by
                have : v ∈ LinearMap.range
                    (LinearMap.toSpanSingleton A (M j) v) := ⟨1, one_smul A v⟩
                rw [h] at this; exact (Submodule.mem_bot A).mp this) hv
            · exact h
          exact LinearMap.range_eq_top.mp hrange m
        exact Module.Finite.of_surjective φ hφ_surj

      haveI : Module.Finite k (↥(N p) →ₗ[A] M p.fst) :=
        Module.Finite.of_injective
          (LinearMap.restrictScalarsₗ k A (↥(N p)) (M p.fst) k)
          (LinearMap.restrictScalars_injective k)
      haveI : Module.Finite k (P p.fst →ₗ[A] M p.fst) :=
        Module.Finite.of_injective
          (LinearMap.restrictScalarsₗ k A (P p.fst) (M p.fst) k)
          (LinearMap.restrictScalars_injective k)

      have hnt1 : Nontrivial (↥(N p) →ₗ[A] M p.fst) := by
        rw [← Module.finrank_pos_iff (R := k)]; omega
      have hnt2 : Nontrivial (P p.fst →ₗ[A] M p.fst) := by
        rw [← Module.finrank_pos_iff (R := k)]; omega
      obtain ⟨φ, hφ⟩ := exists_ne (0 : ↥(N p) →ₗ[A] M p.fst)
      obtain ⟨ψ, hψ⟩ := exists_ne (0 : P p.fst →ₗ[A] M p.fst)
      exact RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.nonempty_linearEquiv_of_nonzero_maps_to_simple (k := k)
        (hindec p) (hP_indec p.fst) φ hφ ψ hψ

    have hint := RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.isInternal_span_singleton_of_completeOrthogonalIdempotents e he_coi

    let decomp : A ≃ₗ[A] ⨁ p, ↥(N p) :=
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hint).symm

    let δ : (i : ι) → Fin (Module.finrank k (M i)) → Type _ := fun i _ => P i

    let isoP : ∀ (p : Σ i : ι, Fin (Module.finrank k (M i))),
        ↥(N p) ≃ₗ[A] δ p.fst p.snd :=
      fun p => Classical.choice (hiso p)

    let dsIso : (⨁ p, ↥(N p)) ≃ₗ[A] ⨁ (p : Σ i : ι, Fin (Module.finrank k (M i))),
        δ p.fst p.snd :=
      DFinsupp.mapRange.linearEquiv isoP

    let sigCurry :=
      @DirectSum.sigmaLcurryEquiv A _ ι (fun i => Fin (Module.finrank k (M i))) δ _ _ _

    let piEquiv : (⨁ (i : ι), ⨁ (_ : Fin (Module.finrank k (M i))), P i) ≃ₗ[A]
        ⨁ (i : ι), (Fin (Module.finrank k (M i)) → P i) :=
      DFinsupp.mapRange.linearEquiv (fun i =>
        DirectSum.linearEquivFunOnFintype A (Fin (Module.finrank k (M i)))
          (fun _ => P i))

    exact ⟨decomp.trans (dsIso.trans (sigCurry.trans piEquiv))⟩

  exact RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.auxiliary_result M hM hM_exhaustive

/-- Every finite projective module satisfying the designated module property is linearly equivalent to a member of a projective family with Kronecker-delta linear-map dimensions. -/
theorem RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.exists_linearEquiv_projective_family
    [IsAlgClosed k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type uA) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hM_exhaustive : ∀ (S : Type uA) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] M i))
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (P i))
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (Q : Type uA) [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q]
    [SMulCommClass A k Q]
    [Module.Projective A Q] [Module.Finite A Q] (hQ_indec : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A Q) :
    ∃ i, Nonempty (Q ≃ₗ[A] P i) := by

  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  haveI : Nontrivial Q := hQ_indec.1
  haveI : FiniteDimensional k Q := Module.Finite.trans A Q

  obtain ⟨N, hN_coatom⟩ := RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.exists_isCoatom_submodule (R := A) (M := Q)
  haveI : IsSimpleModule A (Q ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN_coatom

  obtain ⟨j₀, ⟨e⟩⟩ := hM_exhaustive (Q ⧸ N)

  let φ : Q →ₗ[A] M j₀ := e.toLinearMap.comp N.mkQ
  have hφ : φ ≠ 0 := by
    intro h
    apply hN_coatom.1
    rw [Submodule.eq_top_iff']
    intro q
    have h1 : (e (N.mkQ q) : M j₀) = 0 := LinearMap.congr_fun h q
    have h2 : N.mkQ q = 0 := e.injective (by rwa [map_zero])
    exact (Submodule.Quotient.mk_eq_zero N).mp h2

  haveI : FiniteDimensional k (P j₀) := Module.Finite.trans A (P j₀)

  haveI : Module.Finite A (M j₀) := Module.Finite.equiv e
  haveI : Module.Finite k (M j₀) := Module.Finite.trans A (M j₀)
  haveI : Module.Finite k (P j₀ →ₗ[A] M j₀) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k A (P j₀) (M j₀) k)
      (LinearMap.restrictScalars_injective k)
  have hPdim : Module.finrank k (P j₀ →ₗ[A] M j₀) = 1 := by
    have := hP j₀ j₀; simp only [ite_true] at this; exact this
  have hP_nt : Nontrivial (P j₀ →ₗ[A] M j₀) := by
    rw [← Module.finrank_pos_iff (R := k)]; omega
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : P j₀ →ₗ[A] M j₀)

  exact ⟨j₀, RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.nonempty_linearEquiv_of_nonzero_maps_to_simple (k := k) hQ_indec
    (hP_indec j₀) φ hφ ψ hψ⟩

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.Auxiliary.statement016667 := _root_.RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.auxiliary_result

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.Auxiliary.statement016753 := _root_.RepresentationTheory.RingTheory.Artinian.ModuleIdempotents.exists_projective_family_with_finrank_hom

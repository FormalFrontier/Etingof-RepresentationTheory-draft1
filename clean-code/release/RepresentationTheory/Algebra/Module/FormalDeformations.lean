/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Module.ExtensionCocycles
import RepresentationTheory.Alignment.Attribute
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.NoncommRing

namespace RepresentationTheory.Algebra.Module.FormalDeformations

open RepresentationTheory.Algebra.Module.ExtensionCocycles (AuxiliaryData)

variable (k : Type*) (A : Type*) (V : Type*)
  [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The original algebra action regarded as a linear map into endomorphisms over the base field. -/
noncomputable def actionLinearMap : A →ₗ[k] (V →ₗ[k] V) :=
  (Algebra.lsmul k k V).toLinearMap

/-- A sequence of linear action coefficients whose zeroth term is the original action and whose product coefficients satisfy the convolution law. -/
@[source_ref "Chapter3/Problem3.9.4" (role := supporting)]
structure FormalRepresentationDeformation where

  /-- The linear action coefficient of a formal representation deformation at a natural-number index. -/
  coeff : ℕ → (A →ₗ[k] (V →ₗ[k] V))

  /-- The zeroth coefficient of a formal representation deformation is the original module action. -/
  coeff_zero : coeff 0 = actionLinearMap k A V

  /-- A deformation coefficient evaluated on a product is the antidiagonal convolution of the coefficients evaluated on its factors. -/
  coeff_mul : ∀ (a b : A) (n : ℕ),
    coeff n (a * b)
      = ∑ p ∈ Finset.antidiagonal n, (coeff p.1 a).comp (coeff p.2 b)

/-- The canonical formal representation deformation associated with the original module action. -/
@[source_ref "Chapter3/Problem3.9.4" (role := primary)]
noncomputable def canonicalDeformation : FormalRepresentationDeformation k A V where
  coeff n := if n = 0 then actionLinearMap k A V else 0
  coeff_zero := by simp
  coeff_mul := by
    intro a b n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn

      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      ext v
      change (a * b) • v = a • b • v
      exact mul_smul a b v
    ·
      rw [if_neg hn.ne', LinearMap.zero_apply]
      symm
      refine Finset.sum_eq_zero ?_
      rintro ⟨i, j⟩ hp
      rw [Finset.mem_antidiagonal] at hp
      rcases Nat.eq_zero_or_pos i with hi | hi
      · have hj : j ≠ 0 := by omega
        simp [hj]
      · simp [hi.ne']

/-- An auxiliary binary relation on formal representation deformations. -/
@[source_ref "Chapter3/Problem3.9.4" (role := supporting)]
def AuxiliaryDeformationRel (D D' : FormalRepresentationDeformation k A V) : Prop :=
  ∃ b : ℕ → (V →ₗ[k] V), b 0 = LinearMap.id ∧
    ∀ (a : A) (n : ℕ),
      ∑ p ∈ Finset.antidiagonal n, (b p.1).comp (D.coeff p.2 a)
        = ∑ p ∈ Finset.antidiagonal n, (D'.coeff p.1 a).comp (b p.2)

/-- An auxiliary predicate on a formal representation deformation. -/
@[source_ref "Chapter3/Problem3.9.4" (role := supporting)]
def AuxiliaryDeformationProperty (D : FormalRepresentationDeformation k A V) : Prop :=
  AuxiliaryDeformationRel k A V D (canonicalDeformation k A V)

/-- The auxiliary relation on formal representation deformations is reflexive. -/
theorem auxiliaryDeformationRel_refl (D : FormalRepresentationDeformation k A V) :
    AuxiliaryDeformationRel k A V D D := by
  let b : ℕ → Module.End k V := fun n => if n = 0 then LinearMap.id else 0
  refine ⟨b, by simp [b], ?_⟩
  intro a n
  have hleft :
      ∑ p ∈ Finset.antidiagonal n, (b p.1).comp (D.coeff p.2 a) = D.coeff n a := by
    rw [Finset.sum_eq_single_of_mem (0, n) (by simp [Finset.mem_antidiagonal])]
    · simp [b]
    · rintro ⟨i, j⟩ hmem hne
      have hi : i ≠ 0 := by
        rintro rfl
        rw [Finset.mem_antidiagonal] at hmem
        apply hne
        simp_all
      simp [b, hi]
  have hright :
      ∑ p ∈ Finset.antidiagonal n, (D.coeff p.1 a).comp (b p.2) = D.coeff n a := by
    rw [Finset.sum_eq_single_of_mem (n, 0) (by simp [Finset.mem_antidiagonal])]
    · simp [b]
    · rintro ⟨i, j⟩ hmem hne
      have hj : j ≠ 0 := by
        rintro rfl
        rw [Finset.mem_antidiagonal] at hmem
        apply hne
        simp_all
      simp [b, hj]
  rw [hleft, hright]

section Construction

open RepresentationTheory.Algebra.Module.ExtensionCocycles

variable {k A V}
variable (D : FormalRepresentationDeformation k A V)

/-- The linearized module action sends algebra products to products of endomorphisms. -/
lemma actionLinearMap_mul (a c : A) :
    actionLinearMap k A V (a * c) = actionLinearMap k A V a * actionLinearMap k A V c := by
  ext v
  change (a * c) • v = a • c • v
  exact mul_smul a c v

/-- Evaluating the coboundary of an endomorphism gives its commutator with the original algebra action. -/
lemma coboundary_apply (X : Module.End k V) (a : A) :
    coboundary k A V V X a = actionLinearMap k A V a * X - X * actionLinearMap k A V a := by
  ext w
  simp only [coboundary, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.llcomp_apply,
    LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe, Module.End.mul_apply,
    actionLinearMap]

/-- The coboundary construction is additive in its endomorphism argument. -/
lemma coboundary_add (X Y : Module.End k V) :
    coboundary k A V V (X + Y) = coboundary k A V V X + coboundary k A V V Y := by
  refine LinearMap.ext fun a => ?_
  simp only [coboundary_apply, LinearMap.add_apply, mul_add, add_mul]
  abel

/-- The coboundary construction commutes with scalar multiplication. -/
lemma coboundary_smul (c : k) (X : Module.End k V) :
    coboundary k A V V (c • X) = c • coboundary k A V V X := by
  refine LinearMap.ext fun a => ?_
  simp only [coboundary_apply, LinearMap.smul_apply, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- The coboundary of the zero endomorphism is zero. -/
lemma coboundary_zero : coboundary k A V V (0 : Module.End k V) = 0 := by
  refine LinearMap.ext fun a => ?_
  simp [coboundary_apply]

/-- Membership in the displayed coboundary submodule yields an endomorphism whose coboundary is the given map. -/
lemma exists_coboundary_of_mem {g : A →ₗ[k] Module.End k V}
    (hg : g ∈ coboundaries k A V V) : ∃ X, coboundary k A V V X = g := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · rintro f ⟨X, rfl⟩; exact ⟨X, rfl⟩
  · exact ⟨0, coboundary_zero⟩
  · rintro f₁ f₂ _ _ ⟨X, rfl⟩ ⟨Y, rfl⟩; exact ⟨X + Y, coboundary_add X Y⟩
  · rintro c f _ ⟨X, rfl⟩; exact ⟨c • X, coboundary_smul c X⟩

/-- If the displayed auxiliary type is a subsingleton, every extension cocycle is the coboundary of an endomorphism. -/
lemma exists_coboundary_of_auxiliaryType_subsingleton (hExt : Subsingleton (AuxiliaryData k A V V))
    (g : A →ₗ[k] Module.End k V) (hg : IsExtensionCocycle k A V V g) :
    ∃ X, coboundary k A V V X = g := by
  have hmem : g ∈ coboundaries k A V V := by
    have h0 : (Submodule.Quotient.mk (⟨g, hg⟩ : auxiliaryMapSubmodule k A V V) : AuxiliaryData k A V V) = 0 :=
      Subsingleton.elim _ _
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.mem_comap).mp h0
  exact exists_coboundary_of_mem hmem

/-- The power series of endomorphisms obtained by evaluating all coefficients of a formal representation deformation on an algebra element. -/
noncomputable def actionPowerSeries (a : A) : PowerSeries (Module.End k V) :=
  PowerSeries.mk fun n => D.coeff n a

/-- The coefficient of the deformation action series is the corresponding deformation coefficient evaluated on the algebra element. -/
@[simp] lemma actionPowerSeries_coeff (a : A) (n : ℕ) :
    PowerSeries.coeff n (actionPowerSeries D a) = D.coeff n a := by
  simp [actionPowerSeries]

/-- The deformation action series sends an algebra product to the product of its action series. -/
lemma actionPowerSeries_mul (a c : A) :
    actionPowerSeries D (a * c) = actionPowerSeries D a * actionPowerSeries D c := by
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [actionPowerSeries_coeff]
  rw [D.coeff_mul a c n]
  simp only [← Module.End.mul_eq_comp]

/-- The linear map obtained by convolving a finite family of endomorphisms with the coefficients of a formal representation deformation. -/
noncomputable def obstructionCocycle {m : ℕ} (prev : Fin m → Module.End k V) :
    A →ₗ[k] Module.End k V :=
  ∑ i : Fin m, (LinearMap.llcomp k V V V (prev i)).comp (D.coeff (m - i))

/-- The obstruction cocycle evaluates as the sum of each preceding endomorphism composed with the complementary deformation coefficient. -/
lemma obstructionCocycle_apply {m : ℕ} (prev : Fin m → Module.End k V) (a : A) :
    obstructionCocycle D prev a = ∑ i : Fin m, prev i * D.coeff (m - i) a := by
  simp only [obstructionCocycle, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.llcomp_apply', ← Module.End.mul_eq_comp]

open Classical in

/-- The next endomorphism coefficient selected from a finite family of preceding coefficients. -/
noncomputable def nextTrivializingCoeff {m : ℕ} (prev : Fin m → Module.End k V) : Module.End k V :=
  if h : ∃ X, coboundary k A V V X = obstructionCocycle D prev then h.choose else 0

/-- The finite family of trivializing coefficients through a given natural-number index. -/
noncomputable def trivializingPrefix : (n : ℕ) → Fin (n + 1) → Module.End k V
  | 0 => fun _ => 1
  | (n + 1) => Fin.snoc (trivializingPrefix n) (nextTrivializingCoeff D (trivializingPrefix n))

/-- The selected endomorphism coefficient used to trivialize a formal representation deformation. -/
noncomputable def trivializingCoeff (n : ℕ) : Module.End k V := trivializingPrefix D n (Fin.last n)

/-- The zeroth trivializing coefficient is the identity endomorphism. -/
lemma trivializingCoeff_zero : trivializingCoeff D 0 = 1 := rfl

/-- The next trivializing coefficient is obtained from the preceding finite family by the displayed recursive construction. -/
lemma trivializingCoeff_succ (n : ℕ) : trivializingCoeff D (n + 1) = nextTrivializingCoeff D (trivializingPrefix D n) := by
  simp only [trivializingCoeff, trivializingPrefix, Fin.snoc_last]

/-- The finite prefix evaluates to the trivializing coefficient at the underlying index. -/
lemma trivializingPrefix_apply (n : ℕ) (i : Fin (n + 1)) : trivializingPrefix D n i = trivializingCoeff D (i : ℕ) := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ i
    · simp only [trivializingPrefix, Fin.snoc_last, Fin.val_last, trivializingCoeff_succ]
    · intro j
      rw [trivializingPrefix, Fin.snoc_castSucc, ih j, Fin.val_castSucc]

/-- If the obstruction determined by the current prefix is a coboundary, then it is the coboundary of the next selected trivializing coefficient. -/
lemma coboundary_trivializingCoeff_succ (n : ℕ)
    (h : ∃ X, coboundary k A V V X = obstructionCocycle D (trivializingPrefix D n)) :
    coboundary k A V V (trivializingCoeff D (n + 1)) = obstructionCocycle D (trivializingPrefix D n) := by
  rw [trivializingCoeff_succ, nextTrivializingCoeff, dif_pos h]
  exact h.choose_spec

/-- The coefficient obtained by multiplying a chosen endomorphism power series with the action series of a formal representation deformation. -/
noncomputable def gaugeActionCoeff (n : ℕ) (a : A) : Module.End k V :=
  ∑ p ∈ Finset.antidiagonal n, trivializingCoeff D p.1 * D.coeff p.2 a

/-- The obstruction coefficient remaining after separating the chosen endomorphism coefficient composed with the original action. -/
noncomputable def obstructionCoeff (n : ℕ) (a : A) : Module.End k V :=
  ∑ i ∈ Finset.range n, trivializingCoeff D i * D.coeff (n - i) a

/-- The gauge-action coefficient is the corresponding coefficient of the product of the endomorphism series and deformation action series. -/
lemma gaugeActionCoeff_eq_coeff_mul (n : ℕ) (a : A) :
    gaugeActionCoeff D n a = PowerSeries.coeff n (PowerSeries.mk (trivializingCoeff D) * actionPowerSeries D a) := by
  rw [PowerSeries.coeff_mul]
  simp only [gaugeActionCoeff, PowerSeries.coeff_mk, actionPowerSeries_coeff]

/-- The gauge-action coefficient of a product is the antidiagonal convolution of gauge-action and deformation coefficients. -/
lemma gaugeActionCoeff_mul (n : ℕ) (a c : A) :
    gaugeActionCoeff D n (a * c) = ∑ p ∈ Finset.antidiagonal n, gaugeActionCoeff D p.1 a * D.coeff p.2 c := by
  rw [gaugeActionCoeff_eq_coeff_mul, actionPowerSeries_mul, ← mul_assoc, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [gaugeActionCoeff_eq_coeff_mul, actionPowerSeries_coeff]

/-- A gauge-action coefficient decomposes as its obstruction coefficient plus the chosen endomorphism coefficient composed with the original action. -/
lemma gaugeActionCoeff_eq_obstructionCoeff_add (n : ℕ) (a : A) :
    gaugeActionCoeff D n a = obstructionCoeff D n a + trivializingCoeff D n * actionLinearMap k A V a := by
  rw [gaugeActionCoeff, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, obstructionCoeff,
    Nat.sub_self, D.coeff_zero]

/-- The obstruction cocycle formed from a trivializing prefix evaluates to the next obstruction coefficient. -/
lemma obstructionCocycle_trivializingPrefix (n : ℕ) (a : A) :
    obstructionCocycle D (trivializingPrefix D n) a = obstructionCoeff D (n + 1) a := by
  rw [obstructionCocycle_apply, obstructionCoeff, ← Fin.sum_univ_eq_sum_range fun i => trivializingCoeff D i * D.coeff (n + 1 - i) a]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trivializingPrefix_apply]

/-- When lower gauge coefficients have the displayed form, the next obstruction coefficient satisfies the derivation rule on products. -/
lemma obstructionCoeff_mul (n : ℕ) (ih : ∀ r < n, ∀ a, gaugeActionCoeff D r a = actionLinearMap k A V a * trivializingCoeff D r)
    (a c : A) :
    obstructionCoeff D n (a * c) = actionLinearMap k A V a * obstructionCoeff D n c + obstructionCoeff D n a * actionLinearMap k A V c := by
  have hCc : gaugeActionCoeff D n (a * c)
      = actionLinearMap k A V a * obstructionCoeff D n c + gaugeActionCoeff D n a * actionLinearMap k A V c := by
    rw [gaugeActionCoeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Nat.sub_self, D.coeff_zero, obstructionCoeff, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [ih r hr a, mul_assoc]
  have hgv : obstructionCoeff D n (a * c) = gaugeActionCoeff D n (a * c) - trivializingCoeff D n * actionLinearMap k A V (a * c) := by
    rw [gaugeActionCoeff_eq_obstructionCoeff_add]; abel
  rw [hgv, hCc, actionLinearMap_mul, gaugeActionCoeff_eq_obstructionCoeff_add]
  noncomm_ring

/-- If the displayed auxiliary type is a subsingleton, every gauge-action coefficient equals the original action composed with the corresponding trivializing coefficient. -/
lemma gaugeActionCoeff_eq_action_mul_of_auxiliaryType_subsingleton (hExt : Subsingleton (AuxiliaryData k A V V)) :
    ∀ n a, gaugeActionCoeff D n a = actionLinearMap k A V a * trivializingCoeff D n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a
    match n, ih with
    | 0, _ =>
      rw [gaugeActionCoeff_eq_obstructionCoeff_add, obstructionCoeff, trivializingCoeff_zero]
      simp
    | (m + 1), ih =>

      have hcoc : IsExtensionCocycle k A V V (obstructionCocycle D (trivializingPrefix D m)) := by
        intro a' c'
        rw [obstructionCocycle_trivializingPrefix, obstructionCocycle_trivializingPrefix, obstructionCocycle_trivializingPrefix,
          ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
        exact obstructionCoeff_mul D (m + 1) (fun r hr => ih r hr) a' c'
      obtain ⟨X, hX⟩ := exists_coboundary_of_auxiliaryType_subsingleton hExt _ hcoc
      have hcob : coboundary k A V V (trivializingCoeff D (m + 1)) = obstructionCocycle D (trivializingPrefix D m) :=
        coboundary_trivializingCoeff_succ D m ⟨X, hX⟩
      have key := congrArg (fun f => f a) hcob
      simp only [coboundary_apply, obstructionCocycle_trivializingPrefix] at key

      rw [gaugeActionCoeff_eq_obstructionCoeff_add, ← key]
      abel

end Construction

/-- If the displayed auxiliary type is a subsingleton, every formal representation deformation satisfies the auxiliary predicate. -/
@[source_ref "Chapter3/Problem3.9.4" (role := primary)]
theorem auxiliaryDeformationProperty_of_auxiliaryType_subsingleton
    (hExt : Subsingleton (AuxiliaryData k A V V)) (D : FormalRepresentationDeformation k A V) :
    AuxiliaryDeformationProperty k A V D := by
  refine ⟨trivializingCoeff D, ?_, ?_⟩
  · rw [trivializingCoeff_zero]; exact Module.End.one_eq_id
  · intro a n
    have hL : ∑ p ∈ Finset.antidiagonal n, (trivializingCoeff D p.1).comp (D.coeff p.2 a)
        = actionLinearMap k A V a * trivializingCoeff D n := by
      rw [← gaugeActionCoeff_eq_action_mul_of_auxiliaryType_subsingleton D hExt n a, gaugeActionCoeff]
      exact Finset.sum_congr rfl fun p _ =>
        (Module.End.mul_eq_comp (trivializingCoeff D p.1) (D.coeff p.2 a)).symm
    have hR : ∑ p ∈ Finset.antidiagonal n,
          ((canonicalDeformation k A V).coeff p.1 a).comp (trivializingCoeff D p.2)
        = actionLinearMap k A V a * trivializingCoeff D n := by
      rw [Finset.sum_eq_single_of_mem (0, n) (by simp [Finset.mem_antidiagonal])]
      · change ((if (0 : ℕ) = 0 then actionLinearMap k A V else 0) a).comp (trivializingCoeff D n) = _
        rw [if_pos rfl, Module.End.mul_eq_comp]
      · rintro ⟨i, j⟩ hmem hne
        rw [Finset.mem_antidiagonal] at hmem
        have hi : i ≠ 0 := by rintro rfl; exact hne (by simp_all)
        change ((if i = 0 then actionLinearMap k A V else 0) a).comp (trivializingCoeff D j) = 0
        rw [if_neg hi, LinearMap.zero_apply, LinearMap.zero_comp]
    rw [hL, hR]

/-- An auxiliary proposition associated with a module over an algebra. -/
def AuxiliaryModuleProperty : Prop :=
  (∀ D : FormalRepresentationDeformation k A V, AuxiliaryDeformationProperty k A V D) → Subsingleton (AuxiliaryData k A V V)

/-- An auxiliary proposition associated with a module over the dual numbers. -/
def AuxiliaryDualNumberModuleProperty (V : Type*)
    [AddCommGroup V] [Module k V] [Module (DualNumber k) V]
    [IsScalarTower k (DualNumber k) V] : Prop :=
  AuxiliaryModuleProperty k (DualNumber k) V

section DualNumberCounterexample

variable (K : Type*) [Field K]

/-- An auxiliary algebra structure of the dual numbers on the base field. -/
@[reducible] noncomputable def auxiliaryDualNumberAlgebra : Algebra (DualNumber K) K :=
  TrivSqZeroExt.algebraBase K K

/-- The algebra structure of the dual numbers on the base field used by the displayed one-dimensional module. -/
local instance dualNumberAlgebra : Algebra (DualNumber K) K :=
  TrivSqZeroExt.algebraBase K K

/-- The algebra homomorphism that identifies an endomorphism of the one-dimensional vector space with its scalar. -/
noncomputable def endomorphismScalarAlgHom : Module.End K K →ₐ[K] K where
  toFun f := f 1
  map_one' := rfl
  map_mul' f g := by
    change f (g 1) = f 1 * g 1
    calc
      f (g 1) = f ((g 1) • (1 : K)) := by simp
      _ = (g 1) • f 1 := by rw [map_smul]
      _ = f 1 * g 1 := by simp [mul_comm]
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by simp

/-- The scalar algebra homomorphism on endomorphisms of the field is injective. -/
lemma endomorphismScalarAlgHom_injective : Function.Injective (endomorphismScalarAlgHom K) := by
  intro f g h
  change f 1 = g 1 at h
  apply LinearMap.ext
  intro x
  calc
    f x = f (x • (1 : K)) := by simp
    _ = x • f 1 := by rw [map_smul]
    _ = x • g 1 := by rw [h]
    _ = g (x • (1 : K)) := by rw [map_smul]
    _ = g x := by simp

/-- The scalar-valued power series obtained from a deformation of the one-dimensional dual-number module. -/
noncomputable def scalarActionPowerSeries (D : FormalRepresentationDeformation K (DualNumber K) K)
    (a : DualNumber K) : PowerSeries K :=
  PowerSeries.map (endomorphismScalarAlgHom K).toRingHom (actionPowerSeries D a)

/-- A coefficient of the scalar action series is obtained by applying the endomorphism-scalar homomorphism to the corresponding deformation coefficient. -/
@[simp] lemma scalarActionPowerSeries_coeff (D : FormalRepresentationDeformation K (DualNumber K) K)
    (a : DualNumber K) (n : ℕ) :
    PowerSeries.coeff n (scalarActionPowerSeries K D a) = endomorphismScalarAlgHom K (D.coeff n a) := by
  simp [scalarActionPowerSeries, actionPowerSeries_coeff]

/-- The scalar action series evaluated at the dual-number infinitesimal element is zero. -/
lemma scalarActionPowerSeries_eps (D : FormalRepresentationDeformation K (DualNumber K) K) :
    scalarActionPowerSeries K D DualNumber.eps = 0 := by
  have hsq : actionPowerSeries D DualNumber.eps * actionPowerSeries D DualNumber.eps = 0 := by
    rw [← actionPowerSeries_mul]
    simp only [DualNumber.eps_mul_eps]
    ext n
    simp [actionPowerSeries]
  have hsq' := congrArg (PowerSeries.map (endomorphismScalarAlgHom K).toRingHom) hsq
  simp only [map_mul, map_zero] at hsq'
  exact eq_zero_of_mul_self_eq_zero hsq'

/-- The constant coefficient of the scalar action series evaluated at one is one. -/
lemma scalarActionPowerSeries_one_coeff_zero (D : FormalRepresentationDeformation K (DualNumber K) K) :
    PowerSeries.coeff 0 (scalarActionPowerSeries K D 1) = 1 := by
  rw [scalarActionPowerSeries_coeff, D.coeff_zero]
  simp [endomorphismScalarAlgHom, actionLinearMap]

/-- The scalar action series evaluated at one is one. -/
lemma scalarActionPowerSeries_one (D : FormalRepresentationDeformation K (DualNumber K) K) :
    scalarActionPowerSeries K D 1 = 1 := by
  let U := scalarActionPowerSeries K D 1
  have hidem : U * U = U := by
    change scalarActionPowerSeries K D 1 * scalarActionPowerSeries K D 1 = scalarActionPowerSeries K D 1
    simp only [scalarActionPowerSeries, ← map_mul, ← actionPowerSeries_mul, one_mul]
  have hfac : U * (U - 1) = 0 := by rw [mul_sub, hidem, mul_one, sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hfac with hU | hU
  · have hcoeff := congrArg (PowerSeries.coeff 0) hU
    rw [scalarActionPowerSeries_one_coeff_zero] at hcoeff
    simp at hcoeff
  · exact sub_eq_zero.mp hU

/-- Every coefficient of a deformation of the one-dimensional dual-number module vanishes on the dual-number infinitesimal element. -/
lemma coeff_eps_eq_zero_dualNumber (D : FormalRepresentationDeformation K (DualNumber K) K) (n : ℕ) :
    D.coeff n DualNumber.eps = 0 := by
  apply endomorphismScalarAlgHom_injective K
  change endomorphismScalarAlgHom K (D.coeff n DualNumber.eps) = endomorphismScalarAlgHom K 0
  rw [← scalarActionPowerSeries_coeff]
  simp [scalarActionPowerSeries_eps]

/-- Every positive-index coefficient of a deformation of the one-dimensional dual-number module vanishes on one. -/
lemma coeff_succ_one_eq_zero_dualNumber (D : FormalRepresentationDeformation K (DualNumber K) K) (n : ℕ) :
    D.coeff (n + 1) 1 = 0 := by
  apply endomorphismScalarAlgHom_injective K
  change endomorphismScalarAlgHom K (D.coeff (n + 1) 1) = endomorphismScalarAlgHom K 0
  rw [← scalarActionPowerSeries_coeff]
  simp [scalarActionPowerSeries_one]

/-- Every positive-index coefficient of a deformation of the one-dimensional dual-number module is zero. -/
theorem coeff_succ_eq_zero_dualNumber
    (D : FormalRepresentationDeformation K (DualNumber K) K) (n : ℕ) :
    D.coeff (n + 1) = 0 := by
  apply LinearMap.ext
  intro a
  rw [← a.inl_fst_add_inr_snd_eq, map_add]
  have hinl : TrivSqZeroExt.inl a.fst = a.fst • (1 : DualNumber K) := by
    ext <;> simp
  rw [hinl, DualNumber.inr_eq_smul_eps, map_smul, map_smul,
    coeff_succ_one_eq_zero_dualNumber, coeff_eps_eq_zero_dualNumber, smul_zero, smul_zero, add_zero]
  simp

/-- Every formal deformation of the one-dimensional dual-number module equals its canonical deformation. -/
theorem eq_canonicalDeformation_dualNumber
    (D : FormalRepresentationDeformation K (DualNumber K) K) :
    D = canonicalDeformation K (DualNumber K) K := by
  cases D with
  | mk coeff coeff_zero coeff_mul =>
      rw [FormalRepresentationDeformation.mk.injEq]
      funext n
      cases n with
      | zero =>
          rw [coeff_zero]
          simp [canonicalDeformation]
      | succ n =>
          exact coeff_succ_eq_zero_dualNumber K
            ({ coeff := coeff, coeff_zero := coeff_zero, coeff_mul := coeff_mul } :
              FormalRepresentationDeformation K (DualNumber K) K) n

/-- Every displayed deformation of the one-dimensional dual-number module satisfies the auxiliary deformation predicate. -/
theorem auxiliaryDeformationProperty_dualNumber :
    ∀ D : FormalRepresentationDeformation K (DualNumber K) K,
      AuxiliaryDeformationProperty K (DualNumber K) K D := by
  intro D
  rw [eq_canonicalDeformation_dualNumber K D]
  exact auxiliaryDeformationRel_refl K (DualNumber K) K _

/-- A linear map from the dual numbers to endomorphisms of the base field used as a nontrivial extension cocycle. -/
noncomputable def dualNumberCocycle :
    DualNumber K →ₗ[K] Module.End K K :=
  (Algebra.lsmul K K K).toLinearMap.comp (TrivSqZeroExt.sndHom K K)

/-- The distinguished linear map on the dual numbers satisfies the displayed extension-cocycle predicate. -/
lemma isExtensionCocycle_dualNumberCocycle :
    RepresentationTheory.Algebra.Module.ExtensionCocycles.IsExtensionCocycle K (DualNumber K) K K (dualNumberCocycle K) := by
  intro a b
  apply LinearMap.ext
  intro x
  simp only [dualNumberCocycle, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply]
  have hlsmul (c y : K) :
      ((Algebra.lsmul K K K).toLinearMap c) y = c * y := rfl
  have hsnd (c : DualNumber K) :
      (TrivSqZeroExt.sndHom K K) c = c.snd := rfl
  have hrho (c : DualNumber K) (y : K) :
      RepresentationTheory.Algebra.Module.ExtensionCocycles.algebraEndomorphismFamily K (DualNumber K) K c y = c.fst * y := rfl
  rw [hlsmul, hsnd, hrho, hlsmul, hsnd, hrho, hlsmul, hsnd, DualNumber.snd_mul]
  ring

/-- Every endomorphism of the one-dimensional dual-number module has zero coboundary. -/
lemma coboundary_eq_zero_dualNumber (X : Module.End K K) :
    RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundary K (DualNumber K) K K X = 0 := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  rw [RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundary_apply_apply]
  change a.fst * X x - X (a.fst * x) = 0
  rw [show a.fst * x = a.fst • x by rfl, map_smul]
  simp

/-- The distinguished dual-number cocycle is nonzero. -/
lemma dualNumberCocycle_ne_zero : dualNumberCocycle K ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun (LinearMap.congr_fun h DualNumber.eps) 1
  simp [dualNumberCocycle] at h'

/-- The distinguished dual-number cocycle does not belong to the displayed coboundary submodule. -/
lemma dualNumberCocycle_not_mem_coboundaries :
    dualNumberCocycle K ∉
      RepresentationTheory.Algebra.Module.ExtensionCocycles.coboundaries K (DualNumber K) K K := by
  intro hmem
  rw [RepresentationTheory.Algebra.Module.ExtensionCocycles.mem_coboundaries_iff] at hmem
  obtain ⟨X, hX⟩ := hmem
  apply dualNumberCocycle_ne_zero K
  exact hX.symm.trans (coboundary_eq_zero_dualNumber K X)

/-- The displayed auxiliary type associated with the one-dimensional dual-number module is not a subsingleton. -/
theorem auxiliaryType_not_subsingleton_dualNumber :
    ¬ Subsingleton (AuxiliaryData K (DualNumber K) K K) := by
  letI : AddCommGroup (RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule K (DualNumber K) K K) :=
    @Submodule.addCommGroup K
      (DualNumber K →ₗ[K] Module.End K K) _ _ _
      (RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule K (DualNumber K) K K)
  intro h
  rw [RepresentationTheory.Algebra.Module.ExtensionCocycles.AuxiliaryData, Submodule.Quotient.subsingleton_iff,
    Submodule.eq_top_iff'] at h
  have hmem := h
    (⟨dualNumberCocycle K, isExtensionCocycle_dualNumberCocycle K⟩ :
      RepresentationTheory.Algebra.Module.ExtensionCocycles.auxiliaryMapSubmodule K (DualNumber K) K K)
  exact dualNumberCocycle_not_mem_coboundaries K ((Submodule.mem_comap).mp hmem)

/-- The base field as a module over the dual numbers does not satisfy the displayed auxiliary module property. -/
theorem not_auxiliaryDualNumberModuleProperty :
    ¬ AuxiliaryDualNumberModuleProperty K K := by
  intro h
  exact auxiliaryType_not_subsingleton_dualNumber K (h (auxiliaryDeformationProperty_dualNumber K))

end DualNumberCounterexample

end RepresentationTheory.Algebra.Module.FormalDeformations

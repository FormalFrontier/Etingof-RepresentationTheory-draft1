import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Problem 9.5.3(i): the primitive central idempotent decomposition

This file establishes the ring-theoretic core of the block ↔ central-idempotent bijection of
Etingof Problem 9.5.3(i): a **finite dimensional algebra** `R` over a field `k` has a finite
complete orthogonal family `{eₖ}` of *indecomposable* central idempotents, unique in the sense
that every indecomposable central idempotent is one of the `eₖ` (so they are exactly the subtype
`{e // IsIndecomposableCentralIdempotent R e}`, and that subtype is finite).

The predicate `Etingof.Problem953.IsIndecomposableCentralIdempotent` (a nonzero central idempotent
that is not a sum of two nonzero orthogonal central idempotents) lives here so it can be shared by
this development and the block statements in `Problem9_5_3.lean`.

## Main results

* `isIndecomposableCentralIdempotent_comm_iff`: in a commutative ring, indecomposability of an
  idempotent `e` says exactly that every idempotent below `e` is `0` or `e`.
* `exists_completeOrthogonal_isIndecomposable_of_commArtinian`: a commutative Artinian ring has a
  finite complete orthogonal family of indecomposable idempotents, unique up to reindexing.
* `exists_completeOrthogonal_isIndecomposableCentral`: the corresponding decomposition for a
  finite dimensional algebra `R`, obtained by transferring the decomposition of the (commutative
  Artinian) center `Z(R)` along the central inclusion `Z(R) ↪ R`.
* `finite_isIndecomposableCentralIdempotent`: the indecomposable central idempotents form a
  finite set.

## Proof strategy

The center `Z(R)` is a finite dimensional commutative `k`-algebra, hence Artinian. A commutative
Artinian ring `A` decomposes as `A ⧸ nil(A) ≅ ∏ᵢ (A ⧸ mᵢ)`, a finite product of fields; the
standard idempotents `Pi.single i 1` there are primitive, and they lift (along the nilpotent
kernel of `A → A ⧸ nil(A)`) to a complete orthogonal family of primitive idempotents of `A`.
Central idempotents of `R` are exactly the idempotents of `Z(R)`, and a splitting on one side is a
splitting on the other, so this transfers to `R`.
-/

universe u

namespace Etingof

namespace Problem953

variable (R : Type u) [Ring R]

/-- An **indecomposable central idempotent** of a ring `R`: a nonzero central idempotent that
cannot be written as a sum `e = e₁ + e₂` of two nonzero orthogonal central idempotents. These
are the primitive idempotents of the center; by Problem 9.5.3(i) they index the blocks. -/
def IsIndecomposableCentralIdempotent (e : R) : Prop :=
  e ≠ 0 ∧ IsIdempotentElem e ∧ (∀ y : R, e * y = y * e) ∧
    ¬ ∃ e₁ e₂ : R, e₁ ≠ 0 ∧ e₂ ≠ 0 ∧ IsIdempotentElem e₁ ∧ IsIdempotentElem e₂ ∧
      (∀ y, e₁ * y = y * e₁) ∧ (∀ y, e₂ * y = y * e₂) ∧ e₁ * e₂ = 0 ∧ e = e₁ + e₂

variable {R}

/-- In a commutative ring, indecomposability of an idempotent `e` is equivalent to: `e` is a
nonzero idempotent, and every idempotent `x` below `e` (i.e. `x * e = x`) is `0` or `e`. -/
theorem isIndecomposableCentralIdempotent_comm_iff {A : Type*} [CommRing A] {e : A} :
    IsIndecomposableCentralIdempotent A e ↔
      e ≠ 0 ∧ IsIdempotentElem e ∧
        ∀ x : A, IsIdempotentElem x → x * e = x → x = 0 ∨ x = e := by
  constructor
  · rintro ⟨he0, hei, _, hns⟩
    refine ⟨he0, hei, fun x hx hxe => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hx0, hxe'⟩ := hcon
    -- witness the forbidden splitting `e = x + (e - x)`
    refine hns ⟨x, e - x, hx0, ?_, hx, ?_, fun y => by ring, fun y => by ring, ?_, by ring⟩
    · exact fun h => hxe' (sub_eq_zero.mp h).symm
    · have hex : e * x = x := by rw [mul_comm]; exact hxe
      change (e - x) * (e - x) = e - x
      have : (e - x) * (e - x) = e * e - e * x - x * e + x * x := by ring
      rw [this, hei.eq, hx.eq, hex, hxe]; ring
    · change x * (e - x) = 0
      have : x * (e - x) = x * e - x * x := by ring
      rw [this, hxe, hx.eq]; ring
  · rintro ⟨he0, hei, hsub⟩
    refine ⟨he0, hei, fun y => by rw [mul_comm], ?_⟩
    rintro ⟨e₁, e₂, h1, h2, hi1, hi2, _, _, hor, hsum⟩
    -- `e₁` is an idempotent below `e`
    have h1e : e₁ * e = e₁ := by
      rw [hsum, mul_add, hor, add_zero]; exact hi1.eq
    rcases hsub e₁ hi1 h1e with h | h
    · exact h1 h
    · -- `e₁ = e` forces `e₂ = 0`
      apply h2
      have : e₂ = e - e₁ := by rw [hsum]; ring
      rw [this, h]; ring

/-- Indecomposability of a (central) idempotent transfers along a ring isomorphism of
commutative rings. -/
theorem IsIndecomposableCentralIdempotent.ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (φ : A ≃+* B) {e : A} (he : IsIndecomposableCentralIdempotent A e) :
    IsIndecomposableCentralIdempotent B (φ e) := by
  rw [isIndecomposableCentralIdempotent_comm_iff] at he ⊢
  obtain ⟨h0, hi, hsub⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · simpa using (map_ne_zero_iff φ φ.injective).mpr h0
  · change φ e * φ e = φ e
    rw [← map_mul, hi.eq]
  · intro x hx hxe
    obtain ⟨y, rfl⟩ := φ.surjective x
    have hy : IsIdempotentElem y := by
      have := hx.eq
      rw [← map_mul] at this
      exact φ.injective this
    have hye : y * e = y := by
      apply φ.injective
      rw [map_mul]; exact hxe
    rcases hsub y hy hye with h | h
    · left; rw [h, map_zero]
    · right; rw [h]

/-- The standard idempotent `Pi.single i 1` is indecomposable in a finite product of fields. -/
theorem isIndecomposable_pi_single {ι : Type*} [Finite ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, Field (K i)] (i : ι) :
    IsIndecomposableCentralIdempotent (∀ j, K j) (Pi.single i 1) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [isIndecomposableCentralIdempotent_comm_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- `Pi.single i 1 ≠ 0`
    intro h
    have : (Pi.single i (1 : K i)) i = (0 : ∀ j, K j) i := by rw [h]
    rw [Pi.single_eq_same] at this
    exact one_ne_zero this
  · exact (CompleteOrthogonalIdempotents.single K).idem i
  · intro x hx hxe
    -- `x j = 0` for `j ≠ i`, and `x i` is idempotent hence `0` or `1`
    have hxidem : ∀ j, x j * x j = x j := fun j => congr_fun hx.eq j
    have hxne : ∀ j, j ≠ i → x j = 0 := by
      intro j hj
      have := congr_fun hxe j
      rw [Pi.mul_apply, Pi.single_eq_of_ne hj, mul_zero] at this
      exact this.symm
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hxidem i) with hi0 | hi1
    · left
      ext j
      by_cases hj : j = i
      · subst hj; rw [hi0]; rfl
      · rw [hxne j hj]; rfl
    · right
      ext j
      by_cases hj : j = i
      · subst hj; rw [hi1, Pi.single_eq_same]
      · rw [hxne j hj, Pi.single_eq_of_ne hj]

/-- **Primitive central idempotent decomposition of a commutative Artinian ring.**
A commutative Artinian ring `A` admits a finite complete orthogonal family `{eᵢ}` of
indecomposable idempotents, and every indecomposable idempotent of `A` is one of the `eᵢ`.

The `eᵢ` are the primitive idempotents of the finite product of fields that `A ⧸ nil(A)`
decomposes into (`IsArtinianRing.quotNilradicalEquivPi`): the standard idempotents
`Pi.single i 1` are indecomposable, and they lift along the nilpotent-kernel quotient
`A → A ⧸ nil(A)` to a complete orthogonal family of indecomposable idempotents of `A`. -/
theorem exists_completeOrthogonal_isIndecomposable_of_commArtinian
    (A : Type u) [CommRing A] [IsArtinianRing A] :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → A),
      CompleteOrthogonalIdempotents e ∧
      (∀ i, IsIndecomposableCentralIdempotent A (e i)) ∧
      (∀ f, IsIndecomposableCentralIdempotent A f → ∃ i, e i = f) := by
  classical
  let ι := MaximalSpectrum A
  haveI : Fintype ι := Fintype.ofFinite ι
  let K : ι → Type _ := fun I => A ⧸ I.asIdeal
  letI hK : ∀ I : ι, Field (K I) := fun I => @Ideal.Quotient.field A _ I.asIdeal I.isMaximal
  -- `A → A ⧸ nil(A) ≅ ∏ᵢ Kᵢ`, a surjection with nilpotent kernel
  let φ : (A ⧸ nilradical A) ≃+* (∀ I : ι, K I) :=
    (IsArtinianRing.quotNilradicalEquivPi A).toRingEquiv
  let ψ : A →+* (∀ I : ι, K I) :=
    φ.toRingHom.comp (Ideal.Quotient.mk (nilradical A))
  have hψ_surj : Function.Surjective ψ :=
    φ.surjective.comp Ideal.Quotient.mk_surjective
  have hker : ∀ x ∈ RingHom.ker ψ, IsNilpotent x := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hφ : φ ((Ideal.Quotient.mk (nilradical A)) x) = 0 := hx
    have hx0 := φ.map_eq_zero_iff.mp hφ
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_nilradical] at hx0
    exact hx0
  -- the standard idempotents downstairs, and their lift
  have hp := CompleteOrthogonalIdempotents.single K
  obtain ⟨e, he, hψe⟩ :=
    hp.lift_of_isNilpotent_ker ψ hker (fun i => RingHom.mem_range.mpr (hψ_surj _))
  have hψei : ∀ i, ψ (e i) = Pi.single i 1 := fun i => congr_fun hψe i
  have hp_indec := fun i => isIndecomposable_pi_single K i
  -- each lifted `e i` is indecomposable
  have he_indec : ∀ i, IsIndecomposableCentralIdempotent A (e i) := by
    intro i
    refine ⟨?_, he.idem i, fun y => by rw [mul_comm], ?_⟩
    · intro h
      have hz : ψ (e i) = 0 := by rw [h, map_zero]
      rw [hψei i] at hz
      exact (hp_indec i).1 hz
    · rintro ⟨e₁, e₂, h1, h2, hi1, hi2, _, _, hor, hsum⟩
      -- `ψ e₁, ψ e₂` are orthogonal idempotents summing to `Pi.single i 1`; not both nonzero
      have key : ψ e₁ = 0 ∨ ψ e₂ = 0 := by
        by_contra hcon
        push Not at hcon
        have hidem1 : IsIdempotentElem (ψ e₁) := by
          change ψ e₁ * ψ e₁ = ψ e₁; rw [← map_mul, hi1.eq]
        have hidem2 : IsIdempotentElem (ψ e₂) := by
          change ψ e₂ * ψ e₂ = ψ e₂; rw [← map_mul, hi2.eq]
        have hortho : ψ e₁ * ψ e₂ = 0 := by rw [← map_mul, hor, map_zero]
        have hsum' : ψ e₁ + ψ e₂ = ψ (e i) := by rw [← map_add, hsum]
        exact (hp_indec i).2.2.2 ⟨ψ e₁, ψ e₂, hcon.1, hcon.2, hidem1, hidem2,
          fun y => by rw [mul_comm], fun y => by rw [mul_comm], hortho,
          (hsum'.trans (hψei i)).symm⟩
      rcases key with h | h
      · exact h1 (IsIdempotentElem.eq_zero_of_isNilpotent hi1
          (hker e₁ (RingHom.mem_ker.mpr h)))
      · exact h2 (IsIdempotentElem.eq_zero_of_isNilpotent hi2
          (hker e₂ (RingHom.mem_ker.mpr h)))
  -- every indecomposable idempotent of `A` is one of the `e i`
  have surj : ∀ f, IsIndecomposableCentralIdempotent A f → ∃ i, e i = f := by
    intro f hf
    rw [isIndecomposableCentralIdempotent_comm_iff] at hf
    obtain ⟨hf0, hfi, hfsub⟩ := hf
    have hsum : ∑ i, f * e i = f := by rw [← Finset.mul_sum, he.complete, mul_one]
    have hidem : ∀ i, IsIdempotentElem (f * e i) := by
      intro i
      change (f * e i) * (f * e i) = f * e i
      have : (f * e i) * (f * e i) = (f * f) * (e i * e i) := by ring
      rw [this, hfi.eq, (he.idem i).eq]
    have hbelow : ∀ i, (f * e i) * f = f * e i := by
      intro i
      have : (f * e i) * f = (f * f) * e i := by ring
      rw [this, hfi.eq]
    have hne : ∃ i, f * e i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hf0 (by rw [← hsum]; exact Finset.sum_eq_zero (fun i _ => hc i))
    obtain ⟨i, hi⟩ := hne
    rcases hfsub (f * e i) (hidem i) (hbelow i) with h | h
    · exact absurd h hi
    · refine ⟨i, ?_⟩
      obtain ⟨_, _, hei_sub⟩ := (isIndecomposableCentralIdempotent_comm_iff).mp (he_indec i)
      rcases hei_sub f hfi h with hh | hh
      · exact absurd hh hf0
      · exact hh.symm
  exact ⟨ι, inferInstance, e, he, he_indec, surj⟩

/-- Indecomposability of a central idempotent of `R` is the same, along the inclusion of the
center, as indecomposability in the (commutative) center `Z(R)`: central idempotents of `R` are
exactly the idempotents of `Z(R)`, and a splitting on one side is a splitting on the other. -/
theorem isIndecomposableCentralIdempotent_center_iff
    {k : Type*} [Field k] [Algebra k R] (z : ↥(Subalgebra.center k R)) :
    IsIndecomposableCentralIdempotent R (z : R) ↔
      IsIndecomposableCentralIdempotent ↥(Subalgebra.center k R) z := by
  set v := Subalgebra.val (Subalgebra.center k R) with hv
  have hcentral : ∀ w : ↥(Subalgebra.center k R), ∀ y : R, (w : R) * y = y * (w : R) :=
    fun w y => (Subalgebra.mem_center_iff.mp w.property y).symm
  constructor
  · -- `R`-indecomposable ⟹ `Z`-indecomposable
    rintro ⟨h0, hi, _, hns⟩
    refine ⟨fun h => h0 (by rw [h]; rfl), Subtype.ext hi.eq, fun y => mul_comm z y, ?_⟩
    rintro ⟨z₁, z₂, hz1, hz2, hzi1, hzi2, _, _, hzor, hzsum⟩
    exact hns ⟨(z₁ : R), (z₂ : R),
      fun h => hz1 (Subtype.ext h), fun h => hz2 (Subtype.ext h),
      congrArg v hzi1.eq, congrArg v hzi2.eq, hcentral z₁, hcentral z₂,
      congrArg v hzor, congrArg v hzsum⟩
  · -- `Z`-indecomposable ⟹ `R`-indecomposable
    rintro ⟨h0, hi, _, hns⟩
    refine ⟨fun h => h0 (Subtype.ext h), congrArg v hi.eq, hcentral z, ?_⟩
    rintro ⟨e₁, e₂, h1, h2, hi1, hi2, hc1, hc2, hor, hsum⟩
    have hm1 : e₁ ∈ Subalgebra.center k R := Subalgebra.mem_center_iff.mpr (fun b => (hc1 b).symm)
    have hm2 : e₂ ∈ Subalgebra.center k R := Subalgebra.mem_center_iff.mpr (fun b => (hc2 b).symm)
    exact hns ⟨⟨e₁, hm1⟩, ⟨e₂, hm2⟩,
      fun h => h1 (congrArg v h), fun h => h2 (congrArg v h),
      Subtype.ext hi1.eq, Subtype.ext hi2.eq, fun y => mul_comm _ y, fun y => mul_comm _ y,
      Subtype.ext hor, Subtype.ext hsum⟩

/-- **Primitive central idempotent decomposition of a finite dimensional algebra.**
A finite dimensional algebra `R` over a field `k` has a finite complete orthogonal family
`{eₖ}` of indecomposable central idempotents (`∑ eₖ = 1`, `eₖ * eₗ = 0` for `k ≠ l`, each central
and idempotent), and every indecomposable central idempotent of `R` is one of the `eₖ`.

These are the images in `R` of the primitive idempotents of the commutative Artinian center
`Z(R)` (`exists_completeOrthogonal_isIndecomposable_of_commArtinian`); central idempotents of `R`
correspond exactly to idempotents of `Z(R)`. -/
theorem exists_completeOrthogonal_isIndecomposableCentral
    {k : Type*} [Field k] [Algebra k R] [FiniteDimensional k R] :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → R),
      (∑ i, e i = 1) ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧
      (∀ i, IsIndecomposableCentralIdempotent R (e i)) ∧
      (∀ f, IsIndecomposableCentralIdempotent R f → ∃ i, e i = f) := by
  classical
  letI : IsArtinianRing ↥(Subalgebra.center k R) :=
    isArtinian_of_tower k (inferInstance : IsArtinian k ↥(Subalgebra.center k R))
  obtain ⟨ι, _, z, hz, hz_indec, hz_surj⟩ :=
    exists_completeOrthogonal_isIndecomposable_of_commArtinian ↥(Subalgebra.center k R)
  refine ⟨ι, ‹Fintype ι›, fun i => (z i : R), ?_, ?_, ?_, ?_⟩
  · change ∑ i, Subalgebra.val (Subalgebra.center k R) (z i) = 1
    rw [← map_sum, hz.complete, map_one]
  · intro i j hij
    change Subalgebra.val (Subalgebra.center k R) (z i)
      * Subalgebra.val (Subalgebra.center k R) (z j) = 0
    rw [← map_mul, hz.ortho hij, map_zero]
  · intro i
    exact (isIndecomposableCentralIdempotent_center_iff (z i)).mpr (hz_indec i)
  · intro f hf
    -- `f` is central, hence lies in `Z`; transfer indecomposability into `Z` and match.
    have hfc : f ∈ Subalgebra.center k R :=
      Subalgebra.mem_center_iff.mpr (fun b => (hf.2.2.1 b).symm)
    have hzf : IsIndecomposableCentralIdempotent ↥(Subalgebra.center k R) ⟨f, hfc⟩ :=
      (isIndecomposableCentralIdempotent_center_iff (⟨f, hfc⟩ : ↥(Subalgebra.center k R))).mp hf
    obtain ⟨i, hi⟩ := hz_surj ⟨f, hfc⟩ hzf
    exact ⟨i, congrArg (Subalgebra.val _) hi⟩

/-- The indecomposable central idempotents of a finite dimensional algebra form a finite set. -/
theorem finite_isIndecomposableCentralIdempotent
    (k : Type*) [Field k] [Algebra k R] [FiniteDimensional k R] :
    Finite {e : R // IsIndecomposableCentralIdempotent R e} := by
  obtain ⟨ι, _, e, _, _, he_indec, he_surj⟩ :=
    exists_completeOrthogonal_isIndecomposableCentral (R := R) (k := k)
  refine Finite.of_surjective (fun i => (⟨e i, he_indec i⟩ : {e : R // _})) ?_
  rintro ⟨f, hf⟩
  obtain ⟨i, hi⟩ := he_surj f hf
  exact ⟨i, Subtype.ext hi⟩

end Problem953

end Etingof

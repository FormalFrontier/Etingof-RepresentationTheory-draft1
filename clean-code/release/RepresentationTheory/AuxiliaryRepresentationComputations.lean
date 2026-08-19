/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.InductionAndCoinduction
import RepresentationTheory.AuxiliaryUnavailableStatement
import RepresentationTheory.Subgroup.HomAdjunction
import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary representation computations

This module develops auxiliary finite-group representations and character computations.
-/

open CategoryTheory

noncomputable section

namespace RepresentationTheory.AuxiliaryRepresentationComputations

/-- An auxiliary type. -/
abbrev AuxiliaryType : Type := Equiv.Perm (Fin 3)

/-! ## The irreducible-representation catalogue of `S₃` -/

/-- The one-dimensional complex representation associated to a homomorphism into the complex units. -/
def representationOfUnitsHom {G : Type*} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- A third auxiliary finite-dimensional complex representation of the acting type. -/
def auxiliaryRepresentationThree : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitsHom (1 : AuxiliaryType →* ℂˣ))

/-- An auxiliary homomorphism from the acting type to the complex units. -/
def auxiliaryUnitsCharacter : AuxiliaryType →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

/-- A first auxiliary finite-dimensional complex representation of the acting type. -/
def auxiliaryRepresentationOne : FDRep ℂ AuxiliaryType := FDRep.of (representationOfUnitsHom auxiliaryUnitsCharacter)

/-- The character of the representation associated to a units-valued homomorphism is the underlying complex-valued function. -/
@[simp] lemma character_representationOfUnitsHom {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (representationOfUnitsHom χ)).character g = (χ g : ℂ) := by
  have hg : representationOfUnitsHom χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (representationOfUnitsHom χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp

/-- A one-dimensional representation obtained from a complex-units-valued homomorphism is simple for a finite group. -/
lemma simple_representationOfUnitsHom {G : Type} [Group G] [Finite G] (χ : G →* ℂˣ) :
    Simple (FDRep.of (representationOfUnitsHom χ)) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [FDRep.simple_iff_char_is_norm_one]
  have : ∀ g : G, (FDRep.of (representationOfUnitsHom χ)).character g * (FDRep.of (representationOfUnitsHom χ)).character g⁻¹
      = 1 := by
    intro g
    rw [character_representationOfUnitsHom, character_representationOfUnitsHom, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card]

/-- The third auxiliary representation is simple. -/
lemma auxiliaryRepresentationThree_simple : Simple auxiliaryRepresentationThree := simple_representationOfUnitsHom _

/-- The first auxiliary representation is simple. -/
lemma auxiliaryRepresentationOne_simple : Simple auxiliaryRepresentationOne := simple_representationOfUnitsHom _

/-! ### The standard representation `ℂ²`

The natural 3-dimensional permutation representation of `S₃` on `Fin 3 → ℂ`
(`σ` acts by `f ↦ f ∘ σ⁻¹`) contains the sum-zero subspace as an invariant
2-dimensional subspace; this subspace is the standard irreducible representation. -/

/-- An auxiliary complex representation on functions of three coordinates. -/
def auxiliaryCoordinateRepresentation : Representation ℂ AuxiliaryType (Fin 3 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑σ⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, Equiv.Perm.coe_mul,
      Function.comp_apply]

/-- The action on a coordinate function is precomposition with the inverse permutation. -/
@[simp] lemma auxiliaryCoordinateRepresentation_apply (σ : AuxiliaryType) (f : Fin 3 → ℂ) (i : Fin 3) :
    auxiliaryCoordinateRepresentation σ f i = f (σ⁻¹ i) := rfl

/-- An auxiliary complex-linear map from three-coordinate functions to the complex numbers. -/
def auxiliaryLinearMap : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

/-- The auxiliary linear map evaluates a function by summing all three coordinates. -/
@[simp] lemma auxiliaryLinearMap_apply_sum (f : Fin 3 → ℂ) : auxiliaryLinearMap f = ∑ i, f i := by
  simp [auxiliaryLinearMap, Finset.sum_apply]

/-- An auxiliary subrepresentation of the auxiliary coordinate representation. -/
def auxiliarySubrepresentation : Subrepresentation auxiliaryCoordinateRepresentation where
  toSubmodule := LinearMap.ker auxiliaryLinearMap
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, auxiliaryLinearMap_apply_sum] at hf ⊢
    calc ∑ i, auxiliaryCoordinateRepresentation σ f i = ∑ i, f (σ⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [auxiliaryCoordinateRepresentation_apply]
      _ = ∑ i, f i := Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin 3)) f
      _ = 0 := hf

/-- A second auxiliary finite-dimensional complex representation of the acting type. -/
def auxiliaryRepresentationTwo : FDRep ℂ AuxiliaryType := FDRep.of auxiliarySubrepresentation.toRepresentation

/-! ### Character and simplicity of `auxiliaryRepresentationTwo`

The character of `auxiliaryRepresentationTwo` is computed by viewing `auxiliaryCoordinateRepresentation` as the internal direct
sum of the sum-zero subspace `auxiliarySubrepresentation` and the line of constant vectors. On constants
`S₃` acts trivially, so `χ_permRep = χ_stdRep + 1`; and `χ_permRep(g)` is the number
of fixed points of `g` (the trace of a permutation matrix). Hence
`χ_stdRep(g) = #fix(g) − 1`, giving the values `(2, 0, −1)`. Norm-one of this
character then yields simplicity. -/

open Module

/-- An auxiliary complex vector on three coordinates. -/
def auxiliaryVector : Fin 3 → ℂ := fun _ => 1

/-- Every coordinate of the auxiliary vector is one. -/
@[simp] lemma auxiliaryVector_apply (i : Fin 3) : auxiliaryVector i = 1 := rfl

/-- The auxiliary vector is nonzero. -/
lemma auxiliaryVector_ne_zero : (auxiliaryVector : Fin 3 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 0; simp [auxiliaryVector] at this

/-- Every acting element fixes the auxiliary vector. -/
@[simp] lemma auxiliaryCoordinateRepresentation_fixed_auxiliaryVector (g : AuxiliaryType) : auxiliaryCoordinateRepresentation g auxiliaryVector = auxiliaryVector := by
  funext i; simp

/-- An auxiliary complex submodule of functions on three coordinates. -/
def auxiliarySubmodule : Submodule ℂ (Fin 3 → ℂ) := Submodule.span ℂ {auxiliaryVector}

/-- A three-coordinate vector belongs to the auxiliary submodule exactly when it is a scalar multiple of the auxiliary vector. -/
lemma mem_auxiliarySubmodule_iff {x : Fin 3 → ℂ} : x ∈ auxiliarySubmodule ↔ ∃ c : ℂ, c • auxiliaryVector = x :=
  Submodule.mem_span_singleton

/-- The linear action is given by the permutation matrix of the inverse element. -/
lemma auxiliaryCoordinateRepresentation_eq_permMatrix (g : AuxiliaryType) :
    (auxiliaryCoordinateRepresentation g) = ((g⁻¹ : AuxiliaryType).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext i
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, auxiliaryCoordinateRepresentation_apply]
  rfl

/-- The trace of the auxiliary coordinate action equals the number of fixed coordinates of the inverse element. -/
lemma trace_auxiliaryCoordinateRepresentation (g : AuxiliaryType) :
    LinearMap.trace ℂ (Fin 3 → ℂ) (auxiliaryCoordinateRepresentation g) = (Function.fixedPoints ⇑g⁻¹).ncard := by
  rw [auxiliaryCoordinateRepresentation_eq_permMatrix, Matrix.trace_toLin'_eq, Matrix.trace_permutation]

/-- An auxiliary natural-number-valued function on the auxiliary type. -/
def auxiliaryNatValue (g : AuxiliaryType) : ℕ := (Finset.univ.filter (fun i : Fin 3 => g i = i)).card

/-- A coordinate is fixed by an inverse permutation exactly when it is fixed by the permutation. -/
lemma inv_fixed_iff_fixed (g : AuxiliaryType) (i : Fin 3) : g⁻¹ i = i ↔ g i = i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

/-- The number of fixed points of the inverse action equals the auxiliary natural-number-valued function. -/
lemma ncard_fixedPoints_inv (g : AuxiliaryType) :
    (Function.fixedPoints ⇑g⁻¹).ncard = auxiliaryNatValue g := by
  rw [auxiliaryNatValue, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  exact inv_fixed_iff_fixed g i

/-- The auxiliary natural-number-valued function is invariant under inversion. -/
@[simp] lemma auxiliaryNatValue_inv (g : AuxiliaryType) : auxiliaryNatValue g⁻¹ = auxiliaryNatValue g := by
  rw [auxiliaryNatValue, auxiliaryNatValue]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact inv_fixed_iff_fixed g i

/-- The character of the second auxiliary representation is the fixed-point count minus one. -/
lemma character_auxiliaryRepresentationTwo (g : AuxiliaryType) :
    auxiliaryRepresentationTwo.character g = (auxiliaryNatValue g : ℂ) - 1 := by
  classical
  -- The two complementary invariant subspaces: sum-zero and constants.
  set N : Fin 2 → Submodule ℂ (Fin 3 → ℂ) := ![auxiliarySubrepresentation.toSubmodule, auxiliarySubmodule] with hN
  -- `auxiliaryLinearMap` is surjective, so its kernel has dimension `2`.
  have hsurj : Function.Surjective auxiliaryLinearMap := by
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    rw [auxiliaryLinearMap_apply_sum, Fin.sum_univ_three]
    simp
  have hkerdim : Module.finrank ℂ (LinearMap.ker auxiliaryLinearMap) = 2 := by
    have h := auxiliaryLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi] at h
    simp only [Fintype.card_fin] at h
    omega
  have hsum1 : auxiliaryLinearMap auxiliaryVector = 3 := by rw [auxiliaryLinearMap_apply_sum]; simp
  -- `IsCompl` of the two summands, hence `IsInternal N`.
  have hcompl : IsCompl auxiliarySubrepresentation.toSubmodule auxiliarySubmodule := by
    have hone : Module.finrank ℂ auxiliarySubmodule = 1 := finrank_span_singleton auxiliaryVector_ne_zero
    have hdim : Module.finrank ℂ (Fin 3 → ℂ) ≤
        Module.finrank ℂ auxiliarySubrepresentation.toSubmodule + Module.finrank ℂ auxiliarySubmodule := by
      have hk : Module.finrank ℂ auxiliarySubrepresentation.toSubmodule = 2 := hkerdim
      rw [hk, hone, Module.finrank_pi]
      simp
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_auxiliarySubmodule_iff] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : auxiliaryLinearMap (c • auxiliaryVector) = 0 := hxk
    rw [map_smul, hsum1, smul_eq_mul] at h0
    have hc : c = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · norm_num at h
    simp [hc]
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (zero_ne_one) huniv).mpr hcompl
  -- `auxiliaryCoordinateRepresentation g` maps each summand into itself.
  have hf0 : Set.MapsTo (auxiliaryCoordinateRepresentation g) (N 0) (N 0) := auxiliarySubrepresentation.apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (auxiliaryCoordinateRepresentation g) (N 1) (N 1) := by
    intro x hx
    change x ∈ auxiliarySubmodule at hx
    change auxiliaryCoordinateRepresentation g x ∈ auxiliarySubmodule
    rw [mem_auxiliarySubmodule_iff] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, auxiliaryCoordinateRepresentation_fixed_auxiliaryVector]⟩
  have hf : ∀ i, Set.MapsTo (auxiliaryCoordinateRepresentation g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  -- Trace splits over the internal direct sum.
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_auxiliaryCoordinateRepresentation, ncard_fixedPoints_inv, Fin.sum_univ_two] at htr
  -- Identify the two restricted traces.
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((auxiliaryCoordinateRepresentation g).restrict (hf 0)) = auxiliaryRepresentationTwo.character g := by
    change LinearMap.trace ℂ ↥(auxiliarySubrepresentation.toSubmodule) (auxiliarySubrepresentation.toRepresentation g)
      = LinearMap.trace ℂ ↥(auxiliarySubrepresentation.toSubmodule) ((FDRep.of auxiliarySubrepresentation.toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((auxiliaryCoordinateRepresentation g).restrict (hf 1)) = 1 := by
    have hid : (auxiliaryCoordinateRepresentation g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : Fin 3 → ℂ) ∈ auxiliarySubmodule := x.2
      rw [mem_auxiliarySubmodule_iff] at hx
      obtain ⟨c, hc⟩ := hx
      change auxiliaryCoordinateRepresentation g (x : Fin 3 → ℂ) = (x : Fin 3 → ℂ)
      rw [← hc, map_smul, auxiliaryCoordinateRepresentation_fixed_auxiliaryVector]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton auxiliaryVector_ne_zero
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  -- `#fix(g) = χ_stdRep(g) + 1`.
  rw [eq_sub_iff_add_eq]
  exact htr.symm

/-- The second auxiliary representation has character value two at the identity. -/
lemma character_auxiliaryRepresentationTwo_one : auxiliaryRepresentationTwo.character 1 = 2 := by
  rw [character_auxiliaryRepresentationTwo]
  have : auxiliaryNatValue 1 = 3 := by decide
  rw [this]; norm_num

/-- The second auxiliary representation has character value zero at the transposition of zero and one. -/
lemma character_auxiliaryRepresentationTwo_swap : auxiliaryRepresentationTwo.character (Equiv.swap (0 : Fin 3) 1) = 0 := by
  rw [character_auxiliaryRepresentationTwo]
  have : auxiliaryNatValue (Equiv.swap (0 : Fin 3) 1) = 1 := by decide
  rw [this]; norm_num

/-- An auxiliary proposition whose displayed formal type is unavailable. -/
lemma auxiliaryStatementThree : auxiliaryRepresentationTwo.character (finRotate 3) = -1 := by
  rw [character_auxiliaryRepresentationTwo]
  have : auxiliaryNatValue (finRotate 3) = 0 := by decide
  rw [this]; norm_num

/-- The second auxiliary representation is simple. -/
lemma auxiliaryRepresentationTwo_simple : Simple auxiliaryRepresentationTwo := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : AuxiliaryType, auxiliaryRepresentationTwo.character g * auxiliaryRepresentationTwo.character g⁻¹
      = (((auxiliaryNatValue g : ℤ) - 1) ^ 2 : ℤ) := by
    intro g
    rw [character_auxiliaryRepresentationTwo, character_auxiliaryRepresentationTwo, auxiliaryNatValue_inv]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Int.cast_sum]
  have hsum : ∑ g : AuxiliaryType, (((auxiliaryNatValue g : ℤ) - 1) ^ 2) = 6 := by decide
  rw [hsum]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num

/-! ## The cyclic subgroups -/

/-- An auxiliary subgroup of the auxiliary type. -/
abbrev auxiliarySubgroupA : Subgroup AuxiliaryType := Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)

/-- Another auxiliary subgroup of the auxiliary type. -/
abbrev auxiliarySubgroupB : Subgroup AuxiliaryType := alternatingGroup (Fin 3)

/-! ### The primitive cube-root character `ℂ_ε`

`Z₃ = A₃` is cyclic of order 3, generated by the 3-cycle `(0 1 2) = finRotate 3`. Its
nontrivial irreducible characters send the generator to a primitive cube root of unity
`ζ = exp(2πi/3)`; we build the one with `ε(gen) = ζ` as `auxiliaryCharacterOne`, and `ℂ_ε := representationOfUnitsHom auxiliaryCharacterOne`. -/

/-- An auxiliary unit of the complex numbers. -/
noncomputable def auxiliaryComplexUnit : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / 3)) (Complex.exp_ne_zero _)

/-- Rotation of three coordinates belongs to the second auxiliary subgroup. -/
lemma finRotate_mem_auxiliarySubgroupB : finRotate 3 ∈ auxiliarySubgroupB := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

/-- An auxiliary element of the second auxiliary subgroup. -/
def auxiliarySubgroupBElement : ↥auxiliarySubgroupB := ⟨finRotate 3, finRotate_mem_auxiliarySubgroupB⟩

/-- The cube of the auxiliary complex unit is one. -/
lemma auxiliaryComplexUnit_cube : auxiliaryComplexUnit ^ 3 = 1 := by
  apply Units.ext
  have hval : ((auxiliaryComplexUnit ^ 3 : ℂˣ) : ℂ) = (Complex.exp (2 * Real.pi * Complex.I / 3)) ^ 3 := by
    simp [auxiliaryComplexUnit]
  rw [hval, ← Complex.exp_nat_mul,
    show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) = 2 * Real.pi * Complex.I by
      push_cast; ring, Complex.exp_two_pi_mul_I, Units.val_one]

/-- The auxiliary element of the second subgroup has order three. -/
lemma orderOf_auxiliarySubgroupBElement : orderOf auxiliarySubgroupBElement = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Subtype.ext; decide
  · intro h; exact absurd (congrArg Subtype.val h) (by decide)

/-- Every element of the second auxiliary subgroup is a power of its auxiliary element. -/
lemma mem_zpowers_auxiliarySubgroupBElement (x : ↥auxiliarySubgroupB) : x ∈ Subgroup.zpowers auxiliarySubgroupBElement := by
  have htop : Subgroup.zpowers auxiliarySubgroupBElement = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, orderOf_auxiliarySubgroupBElement, Nat.card_eq_fintype_card]
    decide
  rw [htop]; exact Subgroup.mem_top x

/-- An auxiliary homomorphism from the second auxiliary subgroup to the complex units. -/
noncomputable def auxiliaryCharacterOne : ↥auxiliarySubgroupB →* ℂˣ :=
  monoidHomOfForallMemZpowers mem_zpowers_auxiliarySubgroupBElement (g' := auxiliaryComplexUnit)
    (by rw [orderOf_auxiliarySubgroupBElement]; exact orderOf_dvd_of_pow_eq_one auxiliaryComplexUnit_cube)

/-- An auxiliary finite-dimensional complex representation of the second auxiliary subgroup. -/
noncomputable def auxiliarySubgroupRepresentationOne : FDRep ℂ ↥auxiliarySubgroupB := FDRep.of (representationOfUnitsHom auxiliaryCharacterOne)

/-- The first auxiliary subgroup representation is simple. -/
lemma simple_auxiliarySubgroupRepresentationOne : Simple auxiliarySubgroupRepresentationOne := simple_representationOfUnitsHom _

/-! ### The conjugate primitive character `ℂ_{ε²}`

The other nontrivial character of `Z₃ = A₃` sends the generator to `ζ² = ζ⁻¹`, the
complex-conjugate primitive cube root of unity; it is `ε²` in that its value on the
generator is the square of `ε`'s. -/

/-- The cube of the square of the auxiliary complex unit is one. -/
lemma auxiliaryComplexUnit_sq_cube : (auxiliaryComplexUnit ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, auxiliaryComplexUnit_cube, one_pow]

/-- Another auxiliary homomorphism from the second auxiliary subgroup to the complex units. -/
noncomputable def auxiliaryCharacterTwo : ↥auxiliarySubgroupB →* ℂˣ :=
  monoidHomOfForallMemZpowers mem_zpowers_auxiliarySubgroupBElement (g' := auxiliaryComplexUnit ^ 2)
    (by rw [orderOf_auxiliarySubgroupBElement]; exact orderOf_dvd_of_pow_eq_one auxiliaryComplexUnit_sq_cube)

/-- Another auxiliary finite-dimensional complex representation of the second auxiliary subgroup. -/
noncomputable def auxiliarySubgroupRepresentationTwo : FDRep ℂ ↥auxiliarySubgroupB := FDRep.of (representationOfUnitsHom auxiliaryCharacterTwo)

/-- The second auxiliary subgroup representation is simple. -/
lemma simple_auxiliarySubgroupRepresentationTwo : Simple auxiliarySubgroupRepresentationTwo := simple_representationOfUnitsHom _

/-- The second auxiliary character takes the displayed subgroup element to the square of the specified complex unit. -/
lemma auxiliaryCharacterTwo_apply_auxiliaryElement : auxiliaryCharacterTwo auxiliarySubgroupBElement = auxiliaryComplexUnit ^ 2 :=
  monoidHomOfForallMemZpowers_apply_gen _ _

/-! ## Multiplicity machinery: characters, dimensions, completeness

The four decompositions are proved via Frobenius reciprocity, which computes the
multiplicity of each irreducible in the induced representation. This section collects
the reusable inputs: symmetry of hom-space dimensions, the dimensions and pairwise
non-isomorphism of the three irreducibles, and completeness of the catalogue
`{auxiliaryRepresentationThree, auxiliaryRepresentationOne, auxiliaryRepresentationTwo}` (every simple `S₃`-representation is isomorphic to one of
them). -/

open Module

/-- For finite-group complex representations, the spaces of morphisms in the two directions have equal dimension. -/
theorem finrank_hom_comm {G : Type} [Group G] [Finite G] (V W : FDRep ℂ G) :
    finrank ℂ (V ⟶ W) = finrank ℂ (W ⟶ V) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hVW := FDRep.scalar_product_char_eq_finrank_equivariant V W
  have hWV := FDRep.scalar_product_char_eq_finrank_equivariant W V
  have hcast : (finrank ℂ (V ⟶ W) : ℂ) = (finrank ℂ (W ⟶ V) : ℂ) := by
    rw [← hVW, ← hWV]
    congr 1
    rw [← Equiv.sum_comp (Equiv.inv G) (fun g => V.character g * W.character g⁻¹)]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    change W.character g * V.character g⁻¹ = V.character g⁻¹ * W.character g⁻¹⁻¹
    rw [inv_inv, mul_comm]
  exact_mod_cast hcast

/-! ### Characters and dimensions of the three irreducibles -/

/-- The third auxiliary representation has constant character value one. -/
@[simp] lemma character_auxiliaryRepresentationThree (g : AuxiliaryType) : auxiliaryRepresentationThree.character g = 1 := by
  rw [auxiliaryRepresentationThree, character_representationOfUnitsHom]; simp

/-- The character of the first auxiliary representation is the underlying value of the auxiliary units-valued character. -/
@[simp] lemma character_auxiliaryRepresentationOne (g : AuxiliaryType) : auxiliaryRepresentationOne.character g = (auxiliaryUnitsCharacter g : ℂ) := by
  rw [auxiliaryRepresentationOne, character_representationOfUnitsHom]

/-- An auxiliary proposition whose displayed formal type is unavailable. -/
lemma auxiliaryStatementTwo : auxiliaryRepresentationOne.character (Equiv.swap (0 : Fin 3) 1) = -1 := by
  rw [character_auxiliaryRepresentationOne, auxiliaryUnitsCharacter]
  simp [Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)]

/-- The third auxiliary representation has complex dimension one. -/
lemma finrank_auxiliaryRepresentationThree : finrank ℂ (auxiliaryRepresentationThree : Type) = 1 := by
  have h := FDRep.char_one auxiliaryRepresentationThree
  rw [character_auxiliaryRepresentationThree] at h
  exact_mod_cast h.symm

/-- The first auxiliary representation has complex dimension one. -/
lemma finrank_auxiliaryRepresentationOne : finrank ℂ (auxiliaryRepresentationOne : Type) = 1 := by
  have h := FDRep.char_one auxiliaryRepresentationOne
  rw [character_auxiliaryRepresentationOne, auxiliaryUnitsCharacter] at h
  simp only [map_one, Units.val_one] at h
  exact_mod_cast h.symm

/-- The second auxiliary representation has complex dimension two. -/
lemma finrank_auxiliaryRepresentationTwo : finrank ℂ (auxiliaryRepresentationTwo : Type) = 2 := by
  have h := FDRep.char_one auxiliaryRepresentationTwo
  rw [character_auxiliaryRepresentationTwo_one] at h
  exact_mod_cast h.symm

/-! ### Pairwise non-isomorphism -/

/-- The third and first auxiliary representations are not isomorphic. -/
lemma auxiliaryRepresentationThree_not_iso_one : ¬ Nonempty (auxiliaryRepresentationThree ≅ auxiliaryRepresentationOne) := by
  rintro ⟨e⟩
  have h := congrFun (FDRep.char_iso e) (Equiv.swap (0 : Fin 3) 1)
  rw [character_auxiliaryRepresentationThree, auxiliaryStatementTwo] at h
  norm_num at h

/-- The third and second auxiliary representations are not isomorphic. -/
lemma auxiliaryRepresentationThree_not_iso_two : ¬ Nonempty (auxiliaryRepresentationThree ≅ auxiliaryRepresentationTwo) := by
  rintro ⟨e⟩
  have h := (FDRep.isoToLinearEquiv e).finrank_eq
  rw [finrank_auxiliaryRepresentationThree, finrank_auxiliaryRepresentationTwo] at h
  norm_num at h

/-- The first and second auxiliary representations are not isomorphic. -/
lemma auxiliaryRepresentationOne_not_iso_two : ¬ Nonempty (auxiliaryRepresentationOne ≅ auxiliaryRepresentationTwo) := by
  rintro ⟨e⟩
  have h := (FDRep.isoToLinearEquiv e).finrank_eq
  rw [finrank_auxiliaryRepresentationOne, finrank_auxiliaryRepresentationTwo] at h
  norm_num at h

/-! ### Completeness of the catalogue -/

/-- The displayed cast of the cardinality of the auxiliary type is nonzero. -/
instance neZero_natCardAuxiliaryType : NeZero (Nat.card AuxiliaryType : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- Every simple finite-dimensional complex representation of the auxiliary type is isomorphic to one of three specified representations. -/
@[source_ref "Chapter4/Example4.3_S3" (role := supporting),
  source_ref "Chapter4/Introduction_4.8/Derived2" (role := supporting)]
theorem simple_iso_one_of_three_auxiliary_representations (S : FDRep ℂ AuxiliaryType) [Simple S] :
    Nonempty (S ≅ auxiliaryRepresentationThree) ∨ Nonempty (S ≅ auxiliaryRepresentationOne) ∨ Nonempty (S ≅ auxiliaryRepresentationTwo) := by
  classical
  obtain ⟨n, V, hsimple, hinj, hsurj, hsum⟩ := RepresentationTheory.FDRep.GroupAlgebraDecomposition.exists_completeSimpleFamily_sum_finrank_sq_eq_card ℂ AuxiliaryType
  obtain ⟨a, ⟨ea⟩⟩ := hsurj auxiliaryRepresentationThree auxiliaryRepresentationThree_simple
  obtain ⟨b, ⟨eb⟩⟩ := hsurj auxiliaryRepresentationOne auxiliaryRepresentationOne_simple
  obtain ⟨c, ⟨ec⟩⟩ := hsurj auxiliaryRepresentationTwo auxiliaryRepresentationTwo_simple
  obtain ⟨s, ⟨es⟩⟩ := hsurj S inferInstance
  -- dimensions of the three indices
  have hda : finrank ℂ (V a : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv ea).finrank_eq, finrank_auxiliaryRepresentationThree]
  have hdb : finrank ℂ (V b : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv eb).finrank_eq, finrank_auxiliaryRepresentationOne]
  have hdc : finrank ℂ (V c : Type) = 2 := by
    rw [← (FDRep.isoToLinearEquiv ec).finrank_eq, finrank_auxiliaryRepresentationTwo]
  -- a, b, c are distinct
  have hab : a ≠ b := by
    rintro rfl; exact auxiliaryRepresentationThree_not_iso_one ⟨ea ≪≫ eb.symm⟩
  have hac : a ≠ c := by
    rintro rfl; exact auxiliaryRepresentationThree_not_iso_two ⟨ea ≪≫ ec.symm⟩
  have hbc : b ≠ c := by
    rintro rfl; exact auxiliaryRepresentationOne_not_iso_two ⟨eb ≪≫ ec.symm⟩
  -- s is one of a, b, c
  have hs : s = a ∨ s = b ∨ s = c := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hsa, hsb, hsc⟩ := hcon
    -- {a,b,c,s} are four distinct indices; their squared dims sum to ≥ 7 > 6
    have hsub : ({a, b, c, s} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hpos : 0 < finrank ℂ (V s : Type) := by
      haveI := hsimple s
      exact RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_pos_of_not_isZero (Simple.not_isZero (V s))
    have hle : ∑ i ∈ ({a, b, c, s} : Finset (Fin n)), finrank ℂ (V i : Type) ^ 2 ≤
        ∑ i, finrank ℂ (V i : Type) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
    have hcard : ∑ i ∈ ({a, b, c, s} : Finset (Fin n)), finrank ℂ (V i : Type) ^ 2 =
        finrank ℂ (V a : Type) ^ 2 + finrank ℂ (V b : Type) ^ 2 +
          finrank ℂ (V c : Type) ^ 2 + finrank ℂ (V s : Type) ^ 2 := by
      rw [Finset.sum_insert (by simp [hab, hac, hsa.symm]),
        Finset.sum_insert (by simp [hbc, hsb.symm]),
        Finset.sum_insert (by simp [hsc.symm]), Finset.sum_singleton]
      ring
    have hcard6 : Fintype.card AuxiliaryType = 6 := by decide
    rw [hsum, hcard6] at hle
    rw [hcard, hda, hdb, hdc] at hle
    -- 1 + 1 + 4 + (≥1) ≤ 6 is impossible
    have hsq : 1 ≤ finrank ℂ (V s : Type) ^ 2 := Nat.one_le_pow 2 _ hpos
    omega
  rcases hs with rfl | rfl | rfl
  · exact Or.inl ⟨es ≪≫ ea.symm⟩
  · exact Or.inr (Or.inl ⟨es ≪≫ eb.symm⟩)
  · exact Or.inr (Or.inr ⟨es ≪≫ ec.symm⟩)

/-! ### Cyclic-subgroup enumeration -/

/-- An auxiliary element of the first auxiliary subgroup. -/
def auxiliarySubgroupAElement : ↥auxiliarySubgroupA := ⟨Equiv.swap (0 : Fin 3) 1, Subgroup.mem_zpowers _⟩

/-- The underlying permutation of the auxiliary element is the transposition of zero and one. -/
@[simp] lemma auxiliarySubgroupAElement_val : (auxiliarySubgroupAElement : AuxiliaryType) = Equiv.swap 0 1 := rfl

/-- The auxiliary element of the first subgroup has order two. -/
lemma orderOf_auxiliarySubgroupAElement : orderOf auxiliarySubgroupAElement = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Subtype.ext; decide
  · intro h; exact absurd (congrArg Subtype.val h) (by decide)

/-- The transposition of zero and one has order two. -/
lemma orderOf_swap_zero_one : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · decide
  · decide

/-- The auxiliary element generates the first auxiliary subgroup. -/
lemma zpowers_auxiliarySubgroupAElement : Subgroup.zpowers auxiliarySubgroupAElement = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, orderOf_auxiliarySubgroupAElement, Nat.card_zpowers, orderOf_swap_zero_one]

/-- The auxiliary element generates the second auxiliary subgroup. -/
lemma zpowers_auxiliarySubgroupBElement : Subgroup.zpowers auxiliarySubgroupBElement = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, orderOf_auxiliarySubgroupBElement, Nat.card_eq_fintype_card]
  decide

/-- A sum over a finite group generated by an element of order n equals the sum indexed by its successive powers. -/
lemma sum_eq_sum_powers_of_generator {H : Type} [Group H] [Fintype H] {g : H} {n : ℕ}
    (hord : orderOf g = n) (hgtop : Subgroup.zpowers g = ⊤) (f : H → ℂ) :
    ∑ h : H, f h = ∑ i : Fin n, f (g ^ (i : ℕ)) := by
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hsurj : Function.Surjective (Subgroup.zpowers g).subtype := fun x =>
    ⟨⟨x, hgtop ▸ Subgroup.mem_top x⟩, rfl⟩
  let φ : ↥(Subgroup.zpowers g) ≃* H :=
    MulEquiv.ofBijective (Subgroup.zpowers g).subtype ⟨Subtype.val_injective, hsurj⟩
  let e : Fin n ≃ H := (finCongr hord.symm).trans ((finEquivZPowers hfin).trans φ.toEquiv)
  have he : ∀ i : Fin n, e i = g ^ (i : ℕ) := fun i => rfl
  rw [← Equiv.sum_comp e f]
  exact Finset.sum_congr rfl fun i _ => by rw [he i]

/-! ### Frobenius reciprocity at the dimension level -/

/-- The character of a restricted representation at a subgroup element equals the original character at its underlying element. -/
lemma character_restriction_apply (H : Subgroup AuxiliaryType) (S : FDRep ℂ AuxiliaryType) (h : ↥H) :
    FDRep.character ((Action.res (FGModuleCat ℂ) H.subtype).obj S) h = S.character (h : AuxiliaryType) := rfl

/-- The morphism-space dimension from an induced representation equals that from the original representation to the restriction. -/
theorem finrank_hom_induced_eq_restricted (H : Subgroup AuxiliaryType) {V : Type}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ ↥H V) (S : FDRep ℂ AuxiliaryType) :
    finrank ℂ (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ) ⟶ S)
      = finrank ℂ (FDRep.of ρ ⟶ (Action.res (FGModuleCat ℂ) H.subtype).obj S) := by
  -- G-side: pass to `Rep ℂ S₃`.
  rw [← (FDRep.forget₂HomLinearEquiv (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ)) S).finrank_eq]
  have hG : (forget₂ (FDRep ℂ AuxiliaryType) (Rep ℂ AuxiliaryType)).obj (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ))
      = Rep.ind H.subtype (Rep.of ρ) := rfl
  rw [hG, (Rep.indResHomEquiv H.subtype (Rep.of ρ)
      ((forget₂ (FDRep ℂ AuxiliaryType) (Rep ℂ AuxiliaryType)).obj S)).finrank_eq]
  -- H-side: identify both objects with forgetful images of `FDRep`s, then return to `FDRep`.
  have hWρ : Rep.of ρ = (forget₂ (FDRep ℂ ↥H) (Rep ℂ ↥H)).obj (FDRep.of ρ) := rfl
  have hRes : (Rep.resFunctor H.subtype).obj ((forget₂ (FDRep ℂ AuxiliaryType) (Rep ℂ AuxiliaryType)).obj S)
      = (forget₂ (FDRep ℂ ↥H) (Rep ℂ ↥H)).obj
          ((Action.res (FGModuleCat ℂ) H.subtype).obj S) := rfl
  have key : finrank ℂ (FDRep.of ρ ⟶ (Action.res (FGModuleCat ℂ) H.subtype).obj S)
      = finrank ℂ (Rep.of ρ ⟶ (Rep.resFunctor H.subtype).obj
          ((forget₂ (FDRep ℂ AuxiliaryType) (Rep ℂ AuxiliaryType)).obj S)) := by
    rw [← (FDRep.forget₂HomLinearEquiv (FDRep.of ρ)
      ((Action.res (FGModuleCat ℂ) H.subtype).obj S)).finrank_eq, ← hWρ, ← hRes]
  rw [key]

/-- The dimension of morphisms into an induced representation equals the normalized sum of the two characters over the subgroup. -/
lemma finrank_hom_induced_eq_character_sum (H : Subgroup AuxiliaryType) [Fintype ↥H] [Invertible (Fintype.card ↥H : ℂ)]
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ ↥H V) (S : FDRep ℂ AuxiliaryType) :
    (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ)) : ℂ)
      = ⅟(Fintype.card ↥H : ℂ) • ∑ h : ↥H, S.character (h : AuxiliaryType) * (FDRep.of ρ).character h⁻¹ := by
  rw [finrank_hom_comm, finrank_hom_induced_eq_restricted,
    ← FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of ρ)
      ((Action.res (FGModuleCat ℂ) H.subtype).obj S)]
  simp only [character_restriction_apply]
  simp [Nat.card_eq_fintype_card, invOf_eq_inv, smul_eq_mul]

/-! ### Subgroup cardinalities and remaining character values -/

/-- The first auxiliary subgroup has exactly two elements. -/
lemma card_auxiliarySubgroupA : Fintype.card ↥auxiliarySubgroupA = 2 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, orderOf_swap_zero_one]

/-- The second auxiliary subgroup has exactly three elements. -/
lemma card_auxiliarySubgroupB : Fintype.card ↥auxiliarySubgroupB = 3 := by decide

/-- The auxiliary units-valued character takes rotation of three coordinates to one. -/
lemma auxiliaryUnitsCharacter_finRotate : (auxiliaryUnitsCharacter (finRotate 3) : ℂ) = 1 := by
  rw [auxiliaryUnitsCharacter]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map]
  rw [show Equiv.Perm.sign (finRotate 3) = 1 from by decide]
  simp

/-- An auxiliary proposition whose displayed formal type is unavailable. -/
lemma auxiliaryStatementFour : auxiliaryRepresentationTwo.character ((finRotate 3) ^ 2) = -1 := by
  rw [character_auxiliaryRepresentationTwo]
  rw [show auxiliaryNatValue ((finRotate 3) ^ 2) = 0 from by decide]
  norm_num

/-- The first auxiliary representation has character value one at the identity. -/
lemma character_auxiliaryRepresentationOne_one : auxiliaryRepresentationOne.character 1 = 1 := by
  rw [character_auxiliaryRepresentationOne]; simp

/-- The first auxiliary representation has character value one at rotation of three coordinates. -/
lemma character_auxiliaryRepresentationOne_finRotate : auxiliaryRepresentationOne.character (finRotate 3) = 1 := by
  rw [character_auxiliaryRepresentationOne, auxiliaryUnitsCharacter_finRotate]

/-- The first auxiliary representation has character value one at the square of rotation. -/
lemma character_auxiliaryRepresentationOne_finRotate_sq : auxiliaryRepresentationOne.character ((finRotate 3) ^ 2) = 1 := by
  rw [character_auxiliaryRepresentationOne, auxiliaryUnitsCharacter]
  simp only [MonoidHom.coe_comp, Function.comp_apply, map_pow]
  rw [show Equiv.Perm.sign (finRotate 3) = 1 from by decide]
  simp

/-- The third auxiliary representation is simple. -/
instance simple_auxiliaryRepresentationThree : Simple auxiliaryRepresentationThree := auxiliaryRepresentationThree_simple
/-- The first auxiliary representation is simple. -/
instance simple_auxiliaryRepresentationOne : Simple auxiliaryRepresentationOne := auxiliaryRepresentationOne_simple
/-- The second auxiliary representation is simple. -/
instance simple_auxiliaryRepresentationTwo : Simple auxiliaryRepresentationTwo := auxiliaryRepresentationTwo_simple

/-- The displayed cast of the cardinality of the first auxiliary subgroup is invertible. -/
noncomputable instance invertibleCardAuxiliarySubgroupA : Invertible (Fintype.card ↥auxiliarySubgroupA : ℂ) :=
  invertibleOfNonzero (by rw [card_auxiliarySubgroupA]; norm_num)
/-- The displayed cast of the cardinality of the second auxiliary subgroup is invertible. -/
noncomputable instance invertibleCardAuxiliarySubgroupB : Invertible (Fintype.card ↥auxiliarySubgroupB : ℂ) :=
  invertibleOfNonzero (by rw [card_auxiliarySubgroupB]; norm_num)

/-- The underlying permutation of the auxiliary element is rotation of three coordinates. -/
@[simp] lemma auxiliarySubgroupBElement_val : (auxiliarySubgroupBElement : AuxiliaryType) = finRotate 3 := rfl

/-- An auxiliary proposition whose displayed formal type is unavailable. -/
lemma auxiliaryStatementOne : (auxiliaryUnitsCharacter (Equiv.swap (0 : Fin 3) 1) : ℂ) = -1 := by
  rw [auxiliaryUnitsCharacter]; simp [Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)]

/-- The morphism-space dimension into an induced character from the first auxiliary subgroup is the stated normalized character sum. -/
lemma finrank_hom_induced_auxiliarySubgroupA (χ : ↥auxiliarySubgroupA →* ℂˣ) (S : FDRep ℂ AuxiliaryType) :
    (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA (representationOfUnitsHom χ))) : ℂ)
      = ⅟(Fintype.card ↥auxiliarySubgroupA : ℂ) •
          (S.character 1 * (χ 1 : ℂ) + S.character (Equiv.swap 0 1) * ((χ auxiliarySubgroupAElement)⁻¹ : ℂ)) := by
  rw [finrank_hom_induced_eq_character_sum, sum_eq_sum_powers_of_generator orderOf_auxiliarySubgroupAElement zpowers_auxiliarySubgroupAElement, Fin.sum_univ_two]
  congr 1
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, OneMemClass.coe_one, inv_one,
    auxiliarySubgroupAElement_val, character_representationOfUnitsHom, map_one, map_inv, Units.val_one, Units.val_inv_eq_inv_val]

/-- The morphism-space dimension into an induced character from the second auxiliary subgroup is the stated normalized three-term character sum. -/
lemma finrank_hom_induced_auxiliarySubgroupB (χ : ↥auxiliarySubgroupB →* ℂˣ) (S : FDRep ℂ AuxiliaryType) :
    (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom χ))) : ℂ)
      = ⅟(Fintype.card ↥auxiliarySubgroupB : ℂ) •
          (S.character 1 * (χ 1 : ℂ)
            + S.character (finRotate 3) * ((χ auxiliarySubgroupBElement)⁻¹ : ℂ)
            + S.character ((finRotate 3) ^ 2) * ((χ (auxiliarySubgroupBElement ^ 2))⁻¹ : ℂ)) := by
  rw [finrank_hom_induced_eq_character_sum, sum_eq_sum_powers_of_generator orderOf_auxiliarySubgroupBElement zpowers_auxiliarySubgroupBElement, Fin.sum_univ_three]
  congr 1
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, OneMemClass.coe_one,
    inv_one, auxiliarySubgroupBElement_val, Subgroup.coe_pow, character_representationOfUnitsHom, map_one, map_inv, Units.val_one,
    Units.val_inv_eq_inv_val]

/-! ### Cube-root-of-unity arithmetic for `ℂ_ε` -/

/-- The first auxiliary character takes the displayed subgroup element to the specified complex unit. -/
lemma auxiliaryCharacterOne_apply_auxiliaryElement : auxiliaryCharacterOne auxiliarySubgroupBElement = auxiliaryComplexUnit :=
  monoidHomOfForallMemZpowers_apply_gen _ _

/-- The cube of the underlying complex value of the auxiliary unit is one. -/
lemma auxiliaryComplexUnit_val_cube : (auxiliaryComplexUnit : ℂ) ^ 3 = 1 := by
  rw [← Units.val_pow_eq_pow_val, auxiliaryComplexUnit_cube, Units.val_one]

/-- The inverse of the underlying complex value is its square. -/
lemma auxiliaryComplexUnit_val_inv : (auxiliaryComplexUnit : ℂ)⁻¹ = (auxiliaryComplexUnit : ℂ) ^ 2 :=
  inv_eq_of_mul_eq_one_right (by
    rw [show (auxiliaryComplexUnit : ℂ) * (auxiliaryComplexUnit : ℂ) ^ 2 = (auxiliaryComplexUnit : ℂ) ^ 3 by ring, auxiliaryComplexUnit_val_cube])

/-- The inverse of the square of the underlying complex value equals that value. -/
lemma auxiliaryComplexUnit_val_sq_inv : ((auxiliaryComplexUnit : ℂ) ^ 2)⁻¹ = (auxiliaryComplexUnit : ℂ) :=
  inv_eq_of_mul_eq_one_right (by
    rw [show (auxiliaryComplexUnit : ℂ) ^ 2 * (auxiliaryComplexUnit : ℂ) = (auxiliaryComplexUnit : ℂ) ^ 3 by ring, auxiliaryComplexUnit_val_cube])

/-- The underlying complex value of the auxiliary unit is a primitive cube root of unity. -/
lemma isPrimitiveRoot_auxiliaryComplexUnit : IsPrimitiveRoot (auxiliaryComplexUnit : ℂ) 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  rw [show (auxiliaryComplexUnit : ℂ) = Complex.exp (2 * ↑Real.pi * Complex.I / 3) from rfl,
    show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num]
  exact h

/-- The square of the underlying complex value, the value itself, and one sum to zero. -/
lemma auxiliaryComplexUnit_sum_sq_self_one : (auxiliaryComplexUnit : ℂ) ^ 2 + (auxiliaryComplexUnit : ℂ) + 1 = 0 := by
  have h := isPrimitiveRoot_auxiliaryComplexUnit.geom_sum_eq_zero (by norm_num : 1 < 3)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
  linear_combination h

/-! ## Auxiliary decomposition statements

The following isomorphisms are obtained by computing multiplicities through Frobenius
reciprocity and explicit character values on the two auxiliary subgroups. -/

/-- The representation induced from the trivial character of the first auxiliary subgroup is isomorphic to the indicated binary direct sum. -/
@[source_ref "Chapter5/Introduction_5.11" (role := supporting),
  source_ref "Chapter5/Discussion_5.11_examples" (role := primary)]
theorem induced_trivial_auxiliarySubgroupA_iso_biprod :
    Nonempty
      (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA (representationOfUnitsHom (1 : ↥auxiliarySubgroupA →* ℂˣ))) ≅ auxiliaryRepresentationTwo ⊞ auxiliaryRepresentationThree) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  have hLsum : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA (representationOfUnitsHom (1 : ↥auxiliarySubgroupA →* ℂˣ)))) : ℂ)
      = ⅟(Fintype.card ↥auxiliarySubgroupA : ℂ) • (S.character 1 + S.character (Equiv.swap 0 1)) := by
    rw [finrank_hom_induced_eq_character_sum, sum_eq_sum_powers_of_generator orderOf_auxiliarySubgroupAElement zpowers_auxiliarySubgroupAElement, Fin.sum_univ_two]
    congr 1
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, auxiliarySubgroupAElement_val,
      character_representationOfUnitsHom, MonoidHom.one_apply, Units.val_one, mul_one, inv_one, OneMemClass.coe_one]
  rcases simple_iso_one_of_three_auxiliary_representations S with h | h | h
  · -- S ≅ auxiliaryRepresentationThree : multiplicity 1 = 0 + 1
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA (representationOfUnitsHom (1 : ↥auxiliarySubgroupA →* ℂˣ)))) : ℂ)
        = 1 := by
      rw [hLsum]; simp only [hc, character_auxiliaryRepresentationThree]
      rw [invOf_smul_eq_iff, card_auxiliarySubgroupA, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo ⊞ auxiliaryRepresentationThree) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S auxiliaryRepresentationThree,
        if_neg (fun h => auxiliaryRepresentationThree_not_iso_two ⟨e.symm ≪≫ h.some⟩), if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationOne : multiplicity 0 = 0 + 0
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA (representationOfUnitsHom (1 : ↥auxiliarySubgroupA →* ℂˣ)))) : ℂ)
        = 0 := by
      rw [hLsum]; simp only [hc, character_auxiliaryRepresentationOne_one, auxiliaryStatementTwo]
      rw [invOf_smul_eq_iff, card_auxiliarySubgroupA, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo ⊞ auxiliaryRepresentationThree) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S auxiliaryRepresentationThree,
        if_neg (fun h => auxiliaryRepresentationOne_not_iso_two ⟨e.symm ≪≫ h.some⟩),
        if_neg (fun h => auxiliaryRepresentationThree_not_iso_one ⟨(e.symm ≪≫ h.some).symm⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationTwo : multiplicity 1 = 1 + 0
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA (representationOfUnitsHom (1 : ↥auxiliarySubgroupA →* ℂˣ)))) : ℂ)
        = 1 := by
      rw [hLsum]; simp only [hc, character_auxiliaryRepresentationTwo_one, character_auxiliaryRepresentationTwo_swap]
      rw [invOf_smul_eq_iff, card_auxiliarySubgroupA, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo ⊞ auxiliaryRepresentationThree) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S auxiliaryRepresentationThree, if_pos ⟨e⟩,
        if_neg (fun h => auxiliaryRepresentationThree_not_iso_two ⟨(e.symm ≪≫ h.some).symm⟩)]
    rw [hR]; exact_mod_cast hL

/-- The representation induced from the restricted auxiliary character is isomorphic to the indicated binary direct sum. -/
@[source_ref "Chapter5/Discussion_5.11_examples" (role := primary)]
theorem induced_restrictedCharacter_iso_biprod :
    Nonempty
      (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA (representationOfUnitsHom (auxiliaryUnitsCharacter.comp auxiliarySubgroupA.subtype))) ≅
        auxiliaryRepresentationTwo ⊞ auxiliaryRepresentationOne) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases simple_iso_one_of_three_auxiliary_representations S with h | h | h
  · -- S ≅ auxiliaryRepresentationThree : multiplicity 0 = 0 + 0
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA
        (representationOfUnitsHom (auxiliaryUnitsCharacter.comp auxiliarySubgroupA.subtype)))) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliarySubgroupA]
      simp only [hc, character_auxiliaryRepresentationThree, MonoidHom.comp_apply, map_one, Subgroup.coe_subtype,
        auxiliarySubgroupAElement_val, Units.val_one, auxiliaryStatementOne]
      rw [invOf_smul_eq_iff, card_auxiliarySubgroupA, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo ⊞ auxiliaryRepresentationOne) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S auxiliaryRepresentationOne,
        if_neg (fun hh => auxiliaryRepresentationThree_not_iso_two ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => auxiliaryRepresentationThree_not_iso_one ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationOne : multiplicity 1 = 0 + 1
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA
        (representationOfUnitsHom (auxiliaryUnitsCharacter.comp auxiliarySubgroupA.subtype)))) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliarySubgroupA]
      simp only [hc, character_auxiliaryRepresentationOne_one, auxiliaryStatementTwo, MonoidHom.comp_apply, map_one,
        Subgroup.coe_subtype, auxiliarySubgroupAElement_val, Units.val_one, auxiliaryStatementOne]
      rw [invOf_smul_eq_iff, card_auxiliarySubgroupA, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo ⊞ auxiliaryRepresentationOne) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S auxiliaryRepresentationOne,
        if_neg (fun hh => auxiliaryRepresentationOne_not_iso_two ⟨e.symm ≪≫ hh.some⟩), if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationTwo : multiplicity 1 = 1 + 0
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupA
        (representationOfUnitsHom (auxiliaryUnitsCharacter.comp auxiliarySubgroupA.subtype)))) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliarySubgroupA]
      simp only [hc, character_auxiliaryRepresentationTwo_one, character_auxiliaryRepresentationTwo_swap, MonoidHom.comp_apply, map_one,
        Subgroup.coe_subtype, auxiliarySubgroupAElement_val, Units.val_one, auxiliaryStatementOne]
      rw [invOf_smul_eq_iff, card_auxiliarySubgroupA, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo ⊞ auxiliaryRepresentationOne) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        FDRep.finrank_hom_simple_simple S auxiliaryRepresentationOne, if_pos ⟨e⟩,
        if_neg (fun hh => auxiliaryRepresentationOne_not_iso_two ⟨(e.symm ≪≫ hh.some).symm⟩)]
    rw [hR]; exact_mod_cast hL

/-- The representation induced from the trivial character of the second auxiliary subgroup is isomorphic to the indicated binary direct sum. -/
@[source_ref "Chapter5/Introduction_5.11" (role := supporting),
  source_ref "Chapter5/Discussion_5.11_examples" (role := supporting)]
theorem induced_trivial_auxiliarySubgroupB_iso_biprod :
    Nonempty
      (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom (1 : ↥auxiliarySubgroupB →* ℂˣ))) ≅ auxiliaryRepresentationThree ⊞ auxiliaryRepresentationOne) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases simple_iso_one_of_three_auxiliary_representations S with h | h | h
  · -- S ≅ auxiliaryRepresentationThree : multiplicity 1 = 1 + 0
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB
        (representationOfUnitsHom (1 : ↥auxiliarySubgroupB →* ℂˣ)))) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliarySubgroupB]
      simp only [hc, character_auxiliaryRepresentationThree, MonoidHom.one_apply, inv_one, Units.val_one]
      rw [invOf_smul_eq_iff, card_auxiliarySubgroupB, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationThree ⊞ auxiliaryRepresentationOne) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S auxiliaryRepresentationThree,
        FDRep.finrank_hom_simple_simple S auxiliaryRepresentationOne, if_pos ⟨e⟩,
        if_neg (fun hh => auxiliaryRepresentationThree_not_iso_one ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationOne : multiplicity 1 = 0 + 1
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB
        (representationOfUnitsHom (1 : ↥auxiliarySubgroupB →* ℂˣ)))) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliarySubgroupB]
      simp only [hc, character_auxiliaryRepresentationOne_one, character_auxiliaryRepresentationOne_finRotate, character_auxiliaryRepresentationOne_finRotate_sq,
        MonoidHom.one_apply, inv_one, Units.val_one]
      rw [invOf_smul_eq_iff, card_auxiliarySubgroupB, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationThree ⊞ auxiliaryRepresentationOne) = 1 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S auxiliaryRepresentationThree,
        FDRep.finrank_hom_simple_simple S auxiliaryRepresentationOne,
        if_neg (fun hh => auxiliaryRepresentationThree_not_iso_one ⟨(e.symm ≪≫ hh.some).symm⟩), if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationTwo : multiplicity 0 = 0 + 0
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB
        (representationOfUnitsHom (1 : ↥auxiliarySubgroupB →* ℂˣ)))) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliarySubgroupB]
      simp only [hc, character_auxiliaryRepresentationTwo_one, auxiliaryStatementThree, auxiliaryStatementFour,
        MonoidHom.one_apply, inv_one, Units.val_one]
      rw [invOf_smul_eq_iff, card_auxiliarySubgroupB, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationThree ⊞ auxiliaryRepresentationOne) = 0 := by
      rw [RepresentationTheory.FiniteGroups.CharacterRigidity.finrank_hom_biprod, FDRep.finrank_hom_simple_simple S auxiliaryRepresentationThree,
        FDRep.finrank_hom_simple_simple S auxiliaryRepresentationOne,
        if_neg (fun hh => auxiliaryRepresentationThree_not_iso_two ⟨(e.symm ≪≫ hh.some).symm⟩),
        if_neg (fun hh => auxiliaryRepresentationOne_not_iso_two ⟨(e.symm ≪≫ hh.some).symm⟩)]
    rw [hR]; exact_mod_cast hL

/-- The representation induced from the first character of the second auxiliary subgroup is isomorphic to the indicated auxiliary representation. -/
@[source_ref "Chapter5/Discussion_5.11_examples" (role := supporting)]
theorem induced_auxiliaryCharacterOne_iso_auxiliaryRepresentation :
    Nonempty (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom auxiliaryCharacterOne)) ≅ auxiliaryRepresentationTwo) := by
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases simple_iso_one_of_three_auxiliary_representations S with h | h | h
  · -- S ≅ auxiliaryRepresentationThree : multiplicity 0 (ε ⊥ triv)
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom auxiliaryCharacterOne))) : ℂ)
        = 0 := by
      rw [finrank_hom_induced_auxiliarySubgroupB]
      simp only [hc, character_auxiliaryRepresentationThree, auxiliaryCharacterOne_apply_auxiliaryElement, map_one, map_pow,
        Units.val_pow_eq_pow_val, Units.val_one]
      rw [auxiliaryComplexUnit_val_inv, auxiliaryComplexUnit_val_sq_inv, invOf_smul_eq_iff, card_auxiliarySubgroupB, smul_eq_mul]
      push_cast; linear_combination auxiliaryComplexUnit_sum_sq_self_one
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo) = 0 := by
      rw [FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        if_neg (fun hh => auxiliaryRepresentationThree_not_iso_two ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationOne : multiplicity 0 (ε ⊥ sign)
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom auxiliaryCharacterOne))) : ℂ)
        = 0 := by
      rw [finrank_hom_induced_auxiliarySubgroupB]
      simp only [hc, character_auxiliaryRepresentationOne_one, character_auxiliaryRepresentationOne_finRotate, character_auxiliaryRepresentationOne_finRotate_sq, auxiliaryCharacterOne_apply_auxiliaryElement,
        map_one, map_pow, Units.val_pow_eq_pow_val, Units.val_one]
      rw [auxiliaryComplexUnit_val_inv, auxiliaryComplexUnit_val_sq_inv, invOf_smul_eq_iff, card_auxiliarySubgroupB, smul_eq_mul]
      push_cast; linear_combination auxiliaryComplexUnit_sum_sq_self_one
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo) = 0 := by
      rw [FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        if_neg (fun hh => auxiliaryRepresentationOne_not_iso_two ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationTwo : multiplicity 1 (ε appears once in Res_{Z₃} std)
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom auxiliaryCharacterOne))) : ℂ)
        = 1 := by
      rw [finrank_hom_induced_auxiliarySubgroupB]
      simp only [hc, character_auxiliaryRepresentationTwo_one, auxiliaryStatementThree, auxiliaryStatementFour, auxiliaryCharacterOne_apply_auxiliaryElement,
        map_one, map_pow, Units.val_pow_eq_pow_val, Units.val_one]
      rw [auxiliaryComplexUnit_val_inv, auxiliaryComplexUnit_val_sq_inv, invOf_smul_eq_iff, card_auxiliarySubgroupB, smul_eq_mul]
      push_cast; linear_combination -auxiliaryComplexUnit_sum_sq_self_one
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo) = 1 := by
      rw [FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo, if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL

/-- A character whose value at the displayed auxiliary element is a primitive third root induces to the indicated auxiliary representation. -/
theorem induced_character_of_isPrimitiveRoot_iso_auxiliaryRepresentation (χ : ↥auxiliarySubgroupB →* ℂˣ)
    (hχ : IsPrimitiveRoot ((χ auxiliarySubgroupBElement : ℂˣ) : ℂ) 3) :
    Nonempty (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom χ)) ≅ auxiliaryRepresentationTwo) := by
  set ω : ℂ := ((χ auxiliarySubgroupBElement : ℂˣ) : ℂ) with hω
  have hcube : ω ^ 3 = 1 := hχ.pow_eq_one
  have hne1 : ω ≠ 1 := hχ.ne_one (by norm_num)
  have hsum : ω ^ 2 + ω + 1 = 0 := by
    have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hcube
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hne1
    · exact h
  have hinv1 : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by linear_combination hcube)
  have hinv2 : (ω ^ 2)⁻¹ = ω := inv_eq_of_mul_eq_one_right (by linear_combination hcube)
  refine RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_finrank_eq_of_finrank_hom_simple_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases simple_iso_one_of_three_auxiliary_representations S with h | h | h
  · -- S ≅ auxiliaryRepresentationThree : multiplicity 0
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom χ))) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliarySubgroupB]
      simp only [hc, character_auxiliaryRepresentationThree, map_one, map_pow,
        Units.val_pow_eq_pow_val, Units.val_one]
      rw [← hω, hinv1, hinv2, invOf_smul_eq_iff, card_auxiliarySubgroupB, smul_eq_mul]
      push_cast; linear_combination hsum
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo) = 0 := by
      rw [FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        if_neg (fun hh => auxiliaryRepresentationThree_not_iso_two ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationOne : multiplicity 0
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom χ))) : ℂ) = 0 := by
      rw [finrank_hom_induced_auxiliarySubgroupB]
      simp only [hc, character_auxiliaryRepresentationOne_one, character_auxiliaryRepresentationOne_finRotate, character_auxiliaryRepresentationOne_finRotate_sq, map_one,
        map_pow, Units.val_pow_eq_pow_val, Units.val_one]
      rw [← hω, hinv1, hinv2, invOf_smul_eq_iff, card_auxiliarySubgroupB, smul_eq_mul]
      push_cast; linear_combination hsum
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo) = 0 := by
      rw [FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo,
        if_neg (fun hh => auxiliaryRepresentationOne_not_iso_two ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ auxiliaryRepresentationTwo : multiplicity 1
    obtain ⟨e⟩ := h
    have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom χ))) : ℂ) = 1 := by
      rw [finrank_hom_induced_auxiliarySubgroupB]
      simp only [hc, character_auxiliaryRepresentationTwo_one, auxiliaryStatementThree, auxiliaryStatementFour, map_one,
        map_pow, Units.val_pow_eq_pow_val, Units.val_one]
      rw [← hω, hinv1, hinv2, invOf_smul_eq_iff, card_auxiliarySubgroupB, smul_eq_mul]
      push_cast; linear_combination -hsum
    have hR : finrank ℂ (S ⟶ auxiliaryRepresentationTwo) = 1 := by
      rw [FDRep.finrank_hom_simple_simple S auxiliaryRepresentationTwo, if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL

/-- The representation induced from the second character of the second auxiliary subgroup is isomorphic to the indicated auxiliary representation. -/
@[source_ref "Chapter5/Discussion_5.11_examples" (role := supporting)]
theorem induced_auxiliaryCharacterTwo_iso_auxiliaryRepresentation :
    Nonempty (FDRep.of (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced auxiliarySubgroupB (representationOfUnitsHom auxiliaryCharacterTwo)) ≅ auxiliaryRepresentationTwo) :=
  induced_character_of_isPrimitiveRoot_iso_auxiliaryRepresentation auxiliaryCharacterTwo (by
    rw [auxiliaryCharacterTwo_apply_auxiliaryElement, Units.val_pow_eq_pow_val]
    exact isPrimitiveRoot_auxiliaryComplexUnit.pow_of_coprime 2 (by decide))

end RepresentationTheory.AuxiliaryRepresentationComputations

end

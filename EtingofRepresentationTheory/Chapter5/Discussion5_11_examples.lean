import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter5.Theorem5_9_1

/-!
# Discussion 5.11: Worked examples of induced representations for `S₃`

Etingof's §5.11 computes, via Frobenius reciprocity, the decomposition into
irreducibles of representations of `S₃ = Sym(Fin 3)` induced from one-dimensional
representations of the cyclic subgroups `Z₂` and `Z₃`:

* `Ind_{Z₂}^{S₃} ℂ₊ ≅ ℂ² ⊕ ℂ₊` and `Ind_{Z₂}^{S₃} ℂ₋ ≅ ℂ² ⊕ ℂ₋`;
* `Ind_{Z₃}^{S₃} ℂ₊ ≅ ℂ₊ ⊕ ℂ₋` and `Ind_{Z₃}^{S₃} ℂ_ε ≅ ℂ²`,

where `ℂ₊` is the trivial representation, `ℂ₋` the sign representation, and `ℂ²`
the two-dimensional standard (irreducible) representation of `S₃`.

This file builds the **S₃ irreducible-representation catalogue** used by those
statements — the trivial, sign, and standard representations as objects of
`FDRep ℂ S₃` — and states the four decompositions. The catalogue is the reusable
piece the issue asks for; the decomposition proofs go through Frobenius-reciprocity
multiplicities (`Etingof.Theorem5_10_1` / `Etingof.Theorem5_9_1`) together with the
fact that over `ℂ` a finite group's representation is determined up to isomorphism by
its character.

## Mathlib correspondence

* `Equiv.Perm (Fin 3)` — the group `S₃`.
* `Equiv.Perm.sign` — the sign homomorphism, used for `ℂ₋`.
* `Representation.ofMulAction` / a hand-rolled permutation action — the natural
  3-dimensional representation, whose sum-zero subspace is the standard
  representation `ℂ²`.
* `Etingof.Definition5_8_1` — the induced representation `Ind_H^G`.
-/

open CategoryTheory

noncomputable section

namespace Etingof.Discussion5_11

/-- `S₃`, realized as the symmetric group on `Fin 3`. -/
abbrev S3 : Type := Equiv.Perm (Fin 3)

/-! ## The irreducible-representation catalogue of `S₃` -/

/-- A one-dimensional representation of a group `G` attached to a multiplicative
character `χ : G →* ℂˣ`: `g` acts on `ℂ` by multiplication by `χ g`. -/
def charRep {G : Type*} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The trivial representation `ℂ₊` of `S₃`. -/
def trivRep : FDRep ℂ S3 := FDRep.of (charRep (1 : S3 →* ℂˣ))

/-- The sign character `S₃ →* ℂˣ`, sending a permutation to `±1 ∈ ℂˣ`. -/
def signHom : S3 →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

/-- The sign representation `ℂ₋` of `S₃`. -/
def signRep : FDRep ℂ S3 := FDRep.of (charRep signHom)

/-- The character of a one-dimensional `charRep χ` is `g ↦ χ g`. -/
@[simp] lemma charRep_character {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (charRep χ)).character g = (χ g : ℂ) := by
  have hg : charRep χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (charRep χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp

/-- Any one-dimensional `charRep χ` is simple as an object of `FDRep ℂ G`: its
character has norm one, `∑ g, χ(g)·χ(g⁻¹) = |G|`. -/
lemma charRep_simple {G : Type} [Group G] [Finite G] (χ : G →* ℂˣ) :
    Simple (FDRep.of (charRep χ)) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [FDRep.simple_iff_char_is_norm_one]
  have : ∀ g : G, (FDRep.of (charRep χ)).character g * (FDRep.of (charRep χ)).character g⁻¹
      = 1 := by
    intro g
    rw [charRep_character, charRep_character, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card]

/-- `ℂ₊` is simple. -/
lemma trivRep_simple : Simple trivRep := charRep_simple _

/-- `ℂ₋` is simple. -/
lemma signRep_simple : Simple signRep := charRep_simple _

/-! ### The standard representation `ℂ²`

The natural 3-dimensional permutation representation of `S₃` on `Fin 3 → ℂ`
(`σ` acts by `f ↦ f ∘ σ⁻¹`) contains the sum-zero subspace as an invariant
2-dimensional subspace; this subspace is the standard irreducible representation. -/

/-- The permutation representation of `S₃` on `Fin 3 → ℂ`: `σ` acts by `f ↦ f ∘ σ⁻¹`. -/
def permRep : Representation ℂ S3 (Fin 3 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑σ⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, Equiv.Perm.coe_mul,
      Function.comp_apply]

@[simp] lemma permRep_apply (σ : S3) (f : Fin 3 → ℂ) (i : Fin 3) :
    permRep σ f i = f (σ⁻¹ i) := rfl

/-- The sum map `(Fin 3 → ℂ) →ₗ[ℂ] ℂ`, `f ↦ ∑ i, f i`. -/
def sumLM : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

@[simp] lemma sumLM_apply (f : Fin 3 → ℂ) : sumLM f = ∑ i, f i := by
  simp [sumLM, Finset.sum_apply]

/-- The standard representation `ℂ²` as the sum-zero subrepresentation of `permRep`. -/
def stdSub : Subrepresentation permRep where
  toSubmodule := LinearMap.ker sumLM
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, sumLM_apply] at hf ⊢
    calc ∑ i, permRep σ f i = ∑ i, f (σ⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [permRep_apply]
      _ = ∑ i, f i := Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin 3)) f
      _ = 0 := hf

/-- The standard (2-dimensional) irreducible representation `ℂ²` of `S₃`. -/
def stdRep : FDRep ℂ S3 := FDRep.of stdSub.toRepresentation

/-! ### Character and simplicity of `stdRep`

The character of `stdRep` is computed by viewing `permRep` as the internal direct
sum of the sum-zero subspace `stdSub` and the line of constant vectors. On constants
`S₃` acts trivially, so `χ_permRep = χ_stdRep + 1`; and `χ_permRep(g)` is the number
of fixed points of `g` (the trace of a permutation matrix). Hence
`χ_stdRep(g) = #fix(g) − 1`, giving the values `(2, 0, −1)`. Norm-one of this
character then yields simplicity. -/

open Module

/-- The all-ones vector `(1, 1, 1) ∈ Fin 3 → ℂ`, spanning the trivial line in `permRep`. -/
def onesVec : Fin 3 → ℂ := fun _ => 1

@[simp] lemma onesVec_apply (i : Fin 3) : onesVec i = 1 := rfl

lemma onesVec_ne_zero : (onesVec : Fin 3 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 0; simp [onesVec] at this

/-- `permRep` fixes the all-ones vector: it is a constant, hence permutation-invariant. -/
@[simp] lemma permRep_onesVec (g : S3) : permRep g onesVec = onesVec := by
  funext i; simp

/-- The line of constant vectors, the trivial subrepresentation of `permRep`. -/
def constLine : Submodule ℂ (Fin 3 → ℂ) := Submodule.span ℂ {onesVec}

lemma mem_constLine {x : Fin 3 → ℂ} : x ∈ constLine ↔ ∃ c : ℂ, c • onesVec = x :=
  Submodule.mem_span_singleton

/-- `permRep g` is the linear map of the permutation matrix of `g⁻¹`; this lets us read
its trace off as a count of fixed points. -/
lemma permRep_eq_toLin' (g : S3) :
    (permRep g) = ((g⁻¹ : S3).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext i
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, permRep_apply]
  rfl

/-- The trace of `permRep g` is the number of fixed points of `g⁻¹` (equivalently of `g`). -/
lemma trace_permRep (g : S3) :
    LinearMap.trace ℂ (Fin 3 → ℂ) (permRep g) = (Function.fixedPoints ⇑g⁻¹).ncard := by
  rw [permRep_eq_toLin', Matrix.trace_toLin'_eq, Matrix.trace_permutation]

/-- The number of fixed points of `g`, as a `Finset` cardinality (decidable, hence
computable for concrete permutations). -/
def fixCard (g : S3) : ℕ := (Finset.univ.filter (fun i : Fin 3 => g i = i)).card

/-- A point is fixed by `g⁻¹` iff it is fixed by `g`. -/
lemma perm_inv_fixed_iff (g : S3) (i : Fin 3) : g⁻¹ i = i ↔ g i = i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

lemma fixedPoints_inv_ncard (g : S3) :
    (Function.fixedPoints ⇑g⁻¹).ncard = fixCard g := by
  rw [fixCard, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  exact perm_inv_fixed_iff g i

@[simp] lemma fixCard_inv (g : S3) : fixCard g⁻¹ = fixCard g := by
  rw [fixCard, fixCard]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact perm_inv_fixed_iff g i

/-- **Character of `stdRep`.** For every `g : S₃`, `χ_stdRep(g) = #fix(g) − 1`. -/
lemma stdRep_character (g : S3) :
    stdRep.character g = (fixCard g : ℂ) - 1 := by
  classical
  -- The two complementary invariant subspaces: sum-zero and constants.
  set N : Fin 2 → Submodule ℂ (Fin 3 → ℂ) := ![stdSub.toSubmodule, constLine] with hN
  -- `sumLM` is surjective, so its kernel has dimension `2`.
  have hsurj : Function.Surjective sumLM := by
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    rw [sumLM_apply, Fin.sum_univ_three]
    simp
  have hkerdim : Module.finrank ℂ (LinearMap.ker sumLM) = 2 := by
    have h := sumLM.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi] at h
    simp only [Fintype.card_fin] at h
    omega
  have hsum1 : sumLM onesVec = 3 := by rw [sumLM_apply]; simp
  -- `IsCompl` of the two summands, hence `IsInternal N`.
  have hcompl : IsCompl stdSub.toSubmodule constLine := by
    have hone : Module.finrank ℂ constLine = 1 := finrank_span_singleton onesVec_ne_zero
    have hdim : Module.finrank ℂ (Fin 3 → ℂ) ≤
        Module.finrank ℂ stdSub.toSubmodule + Module.finrank ℂ constLine := by
      have hk : Module.finrank ℂ stdSub.toSubmodule = 2 := hkerdim
      rw [hk, hone, Module.finrank_pi]
      simp
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_constLine] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : sumLM (c • onesVec) = 0 := hxk
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
  -- `permRep g` maps each summand into itself.
  have hf0 : Set.MapsTo (permRep g) (N 0) (N 0) := stdSub.apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (permRep g) (N 1) (N 1) := by
    intro x hx
    change x ∈ constLine at hx
    change permRep g x ∈ constLine
    rw [mem_constLine] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, permRep_onesVec]⟩
  have hf : ∀ i, Set.MapsTo (permRep g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  -- Trace splits over the internal direct sum.
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_permRep, fixedPoints_inv_ncard, Fin.sum_univ_two] at htr
  -- Identify the two restricted traces.
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((permRep g).restrict (hf 0)) = stdRep.character g := by
    change LinearMap.trace ℂ ↥(stdSub.toSubmodule) (stdSub.toRepresentation g)
      = LinearMap.trace ℂ ↥(stdSub.toSubmodule) ((FDRep.of stdSub.toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((permRep g).restrict (hf 1)) = 1 := by
    have hid : (permRep g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : Fin 3 → ℂ) ∈ constLine := x.2
      rw [mem_constLine] at hx
      obtain ⟨c, hc⟩ := hx
      change permRep g (x : Fin 3 → ℂ) = (x : Fin 3 → ℂ)
      rw [← hc, map_smul, permRep_onesVec]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton onesVec_ne_zero
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  -- `#fix(g) = χ_stdRep(g) + 1`.
  rw [eq_sub_iff_add_eq]
  exact htr.symm

/-- `χ_stdRep(1) = 2` (the dimension). -/
lemma stdRep_char_one : stdRep.character 1 = 2 := by
  rw [stdRep_character]
  have : fixCard 1 = 3 := by decide
  rw [this]; norm_num

/-- `χ_stdRep` on a transposition is `0`. -/
lemma stdRep_char_swap : stdRep.character (Equiv.swap (0 : Fin 3) 1) = 0 := by
  rw [stdRep_character]
  have : fixCard (Equiv.swap (0 : Fin 3) 1) = 1 := by decide
  rw [this]; norm_num

/-- `χ_stdRep` on a 3-cycle is `−1`. -/
lemma stdRep_char_cycle : stdRep.character (finRotate 3) = -1 := by
  rw [stdRep_character]
  have : fixCard (finRotate 3) = 0 := by decide
  rw [this]; norm_num

/-- **`stdRep` is simple.** Its character has norm one:
`∑_g χ(g)·χ(g⁻¹) = 1·2² + 3·0² + 2·(−1)² = 6 = |S₃|`. -/
lemma stdRep_simple : Simple stdRep := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : S3, stdRep.character g * stdRep.character g⁻¹
      = (((fixCard g : ℤ) - 1) ^ 2 : ℤ) := by
    intro g
    rw [stdRep_character, stdRep_character, fixCard_inv]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Int.cast_sum]
  have hsum : ∑ g : S3, (((fixCard g : ℤ) - 1) ^ 2) = 6 := by decide
  rw [hsum]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num

/-! ## The cyclic subgroups -/

/-- `Z₂ ≤ S₃`, generated by the transposition `(0 1)`. -/
def Z2 : Subgroup S3 := Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)

/-- `Z₃ ≤ S₃`, the alternating group `A₃ = ⟨(0 1 2)⟩`. -/
def Z3 : Subgroup S3 := alternatingGroup (Fin 3)

/-! ### The primitive cube-root character `ℂ_ε`

`Z₃ = A₃` is cyclic of order 3, generated by the 3-cycle `(0 1 2) = finRotate 3`. Its
nontrivial irreducible characters send the generator to a primitive cube root of unity
`ζ = exp(2πi/3)`; we build the one with `ε(gen) = ζ` as `epsHom`, and `ℂ_ε := charRep epsHom`. -/

/-- A primitive cube root of unity, as a unit of `ℂ`: `ζ = exp(2πi/3)`. -/
noncomputable def zeta3 : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / 3)) (Complex.exp_ne_zero _)

/-- `(0 1 2) = finRotate 3` is an even permutation, hence lies in `Z₃ = A₃`. -/
lemma finRotate_three_mem_Z3 : finRotate 3 ∈ Z3 := by
  rw [Z3, Equiv.Perm.mem_alternatingGroup]; decide

/-- The generator `(0 1 2)` of `Z₃ = A₃`, as an element of the subgroup. -/
def gen3 : ↥Z3 := ⟨finRotate 3, finRotate_three_mem_Z3⟩

/-- `ζ³ = 1`. -/
lemma zeta3_pow_three : zeta3 ^ 3 = 1 := by
  apply Units.ext
  have hval : ((zeta3 ^ 3 : ℂˣ) : ℂ) = (Complex.exp (2 * Real.pi * Complex.I / 3)) ^ 3 := by
    simp [zeta3]
  rw [hval, ← Complex.exp_nat_mul,
    show ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) = 2 * Real.pi * Complex.I by
      push_cast; ring, Complex.exp_two_pi_mul_I, Units.val_one]

/-- `gen3` has order 3. -/
lemma gen3_orderOf : orderOf gen3 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Subtype.ext; decide
  · intro h; exact absurd (congrArg Subtype.val h) (by decide)

/-- `gen3` generates `Z₃`: its powers are all of `Z₃`. -/
lemma gen3_zpowers (x : ↥Z3) : x ∈ Subgroup.zpowers gen3 := by
  have htop : Subgroup.zpowers gen3 = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, gen3_orderOf, Z3, Nat.card_eq_fintype_card]
    decide
  rw [htop]; exact Subgroup.mem_top x

/-- The primitive cube-root character `ε : Z₃ →* ℂˣ`, sending the 3-cycle generator to
`ζ = exp(2πi/3)`. -/
noncomputable def epsHom : ↥Z3 →* ℂˣ :=
  monoidHomOfForallMemZpowers gen3_zpowers (g' := zeta3)
    (by rw [gen3_orderOf]; exact orderOf_dvd_of_pow_eq_one zeta3_pow_three)

/-- The representation `ℂ_ε` of `S₃`'s subgroup `Z₃`: the primitive cube-root character. -/
noncomputable def epsRep : FDRep ℂ ↥Z3 := FDRep.of (charRep epsHom)

/-- `ℂ_ε` is simple (it is one-dimensional). -/
lemma epsRep_simple : Simple epsRep := charRep_simple _

/-! ## The induced representations and their decompositions

Each statement asserts an isomorphism of `S₃`-representations. The intended proof
route (Etingof §5.11), which deliberately avoids the still-`sorry` induced-character
formula `Etingof.Theorem5_9_1`, computes the multiplicity of each irreducible
constituent by Frobenius reciprocity `Etingof.Theorem5_10_1`,
`⟨Ind_H^G W, V_i⟩ = ⟨W, Res_H V_i⟩`, reducing each to a restriction over the 2- or
3-element subgroup, then assembles the isomorphism via `Etingof.iso_of_forall_finrank_hom_eq`
together with completeness of the `S₃` irreducible catalogue `{trivRep, signRep, stdRep}`
(provable from `exists_simples_sum_finrank_sq_eq_card`, since `1² + 1² + 2² = 6 = |S₃|`).

The four statements below are all formalized; their proofs remain to be filled in along
this route. -/

/-- `Ind_{Z₂}^{S₃} ℂ₊ ≅ ℂ² ⊕ ℂ₊`. (Etingof Discussion 5.11(1)) -/
theorem indZ2_trivPlus_decomp :
    Nonempty
      (FDRep.of (Etingof.Definition5_8_1 Z2 (charRep (1 : ↥Z2 →* ℂˣ))) ≅ stdRep ⊞ trivRep) := by
  sorry

/-- `Ind_{Z₂}^{S₃} ℂ₋ ≅ ℂ² ⊕ ℂ₋`. (Etingof Discussion 5.11(1)) -/
theorem indZ2_signMinus_decomp :
    Nonempty
      (FDRep.of (Etingof.Definition5_8_1 Z2 (charRep (signHom.comp Z2.subtype))) ≅
        stdRep ⊞ signRep) := by
  sorry

/-- `Ind_{Z₃}^{S₃} ℂ₊ ≅ ℂ₊ ⊕ ℂ₋`. (Etingof Discussion 5.11(2)) -/
theorem indZ3_trivPlus_decomp :
    Nonempty
      (FDRep.of (Etingof.Definition5_8_1 Z3 (charRep (1 : ↥Z3 →* ℂˣ))) ≅ trivRep ⊞ signRep) := by
  sorry

/-- `Ind_{Z₃}^{S₃} ℂ_ε ≅ ℂ²`. (Etingof Discussion 5.11(2)) -/
theorem indZ3_eps_decomp :
    Nonempty (FDRep.of (Etingof.Definition5_8_1 Z3 (charRep epsHom)) ≅ stdRep) := by
  sorry

end Etingof.Discussion5_11

end

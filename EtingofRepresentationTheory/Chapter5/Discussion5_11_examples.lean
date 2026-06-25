import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter5.Theorem5_9_1
import EtingofRepresentationTheory.Chapter5.Theorem5_10_1
import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

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

/-! ## Multiplicity machinery: characters, dimensions, completeness

The four decompositions are proved via Frobenius reciprocity, which computes the
multiplicity of each irreducible in the induced representation. This section assembles
the reusable inputs: symmetry of hom-space dimensions, the dimensions and pairwise
non-isomorphism of the three irreducibles, and completeness of the catalogue
`{trivRep, signRep, stdRep}` (every simple `S₃`-representation is isomorphic to one of
them). -/

open Module

/-- Hom-space dimensions in `FDRep ℂ G` are symmetric: `dim Hom(V,W) = dim Hom(W,V)`.
Both equal the (symmetric) scalar product of the two characters. -/
theorem finrank_hom_symm {G : Type} [Group G] [Finite G] (V W : FDRep ℂ G) :
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
    show W.character g * V.character g⁻¹ = V.character g⁻¹ * W.character g⁻¹⁻¹
    rw [inv_inv, mul_comm]
  exact_mod_cast hcast

/-! ### Characters and dimensions of the three irreducibles -/

@[simp] lemma trivRep_character (g : S3) : trivRep.character g = 1 := by
  rw [trivRep, charRep_character]; simp

@[simp] lemma signRep_character (g : S3) : signRep.character g = (signHom g : ℂ) := by
  rw [signRep, charRep_character]

lemma signRep_char_swap : signRep.character (Equiv.swap (0 : Fin 3) 1) = -1 := by
  rw [signRep_character, signHom]
  simp [Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)]

lemma trivRep_finrank : finrank ℂ (trivRep : Type) = 1 := by
  have h := FDRep.char_one trivRep
  rw [trivRep_character] at h
  exact_mod_cast h.symm

lemma signRep_finrank : finrank ℂ (signRep : Type) = 1 := by
  have h := FDRep.char_one signRep
  rw [signRep_character, signHom] at h
  simp only [MonoidHom.coe_comp, Function.comp_apply, map_one, Units.val_one] at h
  exact_mod_cast h.symm

lemma stdRep_finrank : finrank ℂ (stdRep : Type) = 2 := by
  have h := FDRep.char_one stdRep
  rw [stdRep_char_one] at h
  exact_mod_cast h.symm

/-! ### Pairwise non-isomorphism -/

lemma trivRep_not_iso_signRep : ¬ Nonempty (trivRep ≅ signRep) := by
  rintro ⟨e⟩
  have h := congrFun (FDRep.char_iso e) (Equiv.swap (0 : Fin 3) 1)
  rw [trivRep_character, signRep_char_swap] at h
  norm_num at h

lemma trivRep_not_iso_stdRep : ¬ Nonempty (trivRep ≅ stdRep) := by
  rintro ⟨e⟩
  have h := (FDRep.isoToLinearEquiv e).finrank_eq
  rw [trivRep_finrank, stdRep_finrank] at h
  norm_num at h

lemma signRep_not_iso_stdRep : ¬ Nonempty (signRep ≅ stdRep) := by
  rintro ⟨e⟩
  have h := (FDRep.isoToLinearEquiv e).finrank_eq
  rw [signRep_finrank, stdRep_finrank] at h
  norm_num at h

/-! ### Completeness of the catalogue -/

instance : NeZero (Nat.card S3 : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- Every simple representation of `S₃` is isomorphic to `trivRep`, `signRep`, or `stdRep`.
This follows from the Artin-Wedderburn dimension count `1² + 1² + 2² = 6 = |S₃|`: the three
listed irreducibles are simple, pairwise non-isomorphic, and exhaust the squared-dimension
budget, so no fourth simple can exist. -/
theorem S3_simple_iso (S : FDRep ℂ S3) [Simple S] :
    Nonempty (S ≅ trivRep) ∨ Nonempty (S ≅ signRep) ∨ Nonempty (S ≅ stdRep) := by
  classical
  obtain ⟨n, V, hsimple, hinj, hsurj, hsum⟩ := exists_simples_sum_finrank_sq_eq_card ℂ S3
  obtain ⟨a, ⟨ea⟩⟩ := hsurj trivRep trivRep_simple
  obtain ⟨b, ⟨eb⟩⟩ := hsurj signRep signRep_simple
  obtain ⟨c, ⟨ec⟩⟩ := hsurj stdRep stdRep_simple
  obtain ⟨s, ⟨es⟩⟩ := hsurj S inferInstance
  -- dimensions of the three indices
  have hda : finrank ℂ (V a : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv ea).finrank_eq, trivRep_finrank]
  have hdb : finrank ℂ (V b : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv eb).finrank_eq, signRep_finrank]
  have hdc : finrank ℂ (V c : Type) = 2 := by
    rw [← (FDRep.isoToLinearEquiv ec).finrank_eq, stdRep_finrank]
  -- a, b, c are distinct
  have hab : a ≠ b := by
    rintro rfl; exact trivRep_not_iso_signRep ⟨ea ≪≫ eb.symm⟩
  have hac : a ≠ c := by
    rintro rfl; exact trivRep_not_iso_stdRep ⟨ea ≪≫ ec.symm⟩
  have hbc : b ≠ c := by
    rintro rfl; exact signRep_not_iso_stdRep ⟨eb ≪≫ ec.symm⟩
  -- s is one of a, b, c
  have hs : s = a ∨ s = b ∨ s = c := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hsa, hsb, hsc⟩ := hcon
    -- {a,b,c,s} are four distinct indices; their squared dims sum to ≥ 7 > 6
    have hsub : ({a, b, c, s} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hpos : 0 < finrank ℂ (V s : Type) := by
      haveI := hsimple s
      exact Etingof.finrank_pos_of_not_isZero (Simple.not_isZero (V s))
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
    have hcard6 : Fintype.card S3 = 6 := by decide
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

/-- The transposition generator `(0 1)` of `Z₂`, as an element of the subgroup. -/
def gen2 : ↥Z2 := ⟨Equiv.swap (0 : Fin 3) 1, Subgroup.mem_zpowers _⟩

@[simp] lemma gen2_val : (gen2 : S3) = Equiv.swap 0 1 := rfl

lemma gen2_orderOf : orderOf gen2 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Subtype.ext; decide
  · intro h; exact absurd (congrArg Subtype.val h) (by decide)

lemma swap01_orderOf : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · decide
  · decide

lemma gen2_zpowers : Subgroup.zpowers gen2 = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, gen2_orderOf, Z2, Nat.card_zpowers, swap01_orderOf]

lemma gen3_zpowers_top : Subgroup.zpowers gen3 = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, gen3_orderOf, Z3, Nat.card_eq_fintype_card]
  decide

/-- A sum over a finite cyclic group `H = ⟨g⟩` (with `orderOf g = n`) enumerates as a sum of
`f (gⁱ)` for `i : Fin n`. -/
lemma sum_cyclic {H : Type} [Group H] [Fintype H] {g : H} {n : ℕ}
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

/-- The character of the restriction `Res_H S` of `S` to a subgroup `H` is `S`'s character
read at the underlying `S₃`-element. -/
lemma resObj_character (H : Subgroup S3) (S : FDRep ℂ S3) (h : ↥H) :
    FDRep.character ((Action.res (FGModuleCat ℂ) H.subtype).obj S) h = S.character (h : S3) := rfl

/-- **Frobenius reciprocity (dimension form).** For a subgroup `H ≤ S₃`, a finite-dimensional
`H`-representation `ρ`, and any `S₃`-representation `S`, the multiplicity of `S` in the induced
representation equals the multiplicity of `ρ` in the restriction of `S` to `H`:
`dim Hom_{S₃}(Ind_H ρ, S) = dim Hom_H(ρ, Res_H S)`.

This passes to `Rep ℂ S₃` (where `Mathlib`'s induction lives), applies the adjunction
`Rep.indResHomEquiv` (`Etingof.Theorem5_10_1`), and returns to `FDRep`. The induced object
`FDRep.of (Definition5_8_1 H ρ)` is definitionally `Rep.ind H.subtype (Rep.of ρ)` after the
forgetful functor, since `Definition5_8_1 H ρ = Representation.ind H.subtype ρ`. -/
theorem frobenius_finrank (H : Subgroup S3) {V : Type}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ ↥H V) (S : FDRep ℂ S3) :
    finrank ℂ (FDRep.of (Etingof.Definition5_8_1 H ρ) ⟶ S)
      = finrank ℂ (FDRep.of ρ ⟶ (Action.res (FGModuleCat ℂ) H.subtype).obj S) := by
  -- G-side: pass to `Rep ℂ S₃`.
  rw [← (FDRep.forget₂HomLinearEquiv (FDRep.of (Etingof.Definition5_8_1 H ρ)) S).finrank_eq]
  have hG : (forget₂ (FDRep ℂ S3) (Rep ℂ S3)).obj (FDRep.of (Etingof.Definition5_8_1 H ρ))
      = Rep.ind H.subtype (Rep.of ρ) := rfl
  rw [hG, (Rep.indResHomEquiv H.subtype (Rep.of ρ)
      ((forget₂ (FDRep ℂ S3) (Rep ℂ S3)).obj S)).finrank_eq]
  -- H-side: identify both objects with forgetful images of `FDRep`s, then return to `FDRep`.
  have hWρ : Rep.of ρ = (forget₂ (FDRep ℂ ↥H) (Rep ℂ ↥H)).obj (FDRep.of ρ) := rfl
  have hRes : (Rep.resFunctor H.subtype).obj ((forget₂ (FDRep ℂ S3) (Rep ℂ S3)).obj S)
      = (forget₂ (FDRep ℂ ↥H) (Rep ℂ ↥H)).obj
          ((Action.res (FGModuleCat ℂ) H.subtype).obj S) := rfl
  have key : finrank ℂ (FDRep.of ρ ⟶ (Action.res (FGModuleCat ℂ) H.subtype).obj S)
      = finrank ℂ (Rep.of ρ ⟶ (Rep.resFunctor H.subtype).obj
          ((forget₂ (FDRep ℂ S3) (Rep ℂ S3)).obj S)) := by
    rw [← (FDRep.forget₂HomLinearEquiv (FDRep.of ρ)
      ((Action.res (FGModuleCat ℂ) H.subtype).obj S)).finrank_eq, ← hWρ, ← hRes]
  rw [key]

/-- The multiplicity of a simple `S` in the induced representation, as a scalar product over
`H` of the restricted character of `S` against the inducing character. Combines hom-symmetry,
Frobenius reciprocity, and the character/scalar-product bridge. -/
lemma ind_finrank_eq_scalar (H : Subgroup S3) [Fintype ↥H] [Invertible (Fintype.card ↥H : ℂ)]
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ ↥H V) (S : FDRep ℂ S3) :
    (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H ρ)) : ℂ)
      = ⅟(Fintype.card ↥H : ℂ) • ∑ h : ↥H, S.character (h : S3) * (FDRep.of ρ).character h⁻¹ := by
  rw [finrank_hom_symm, frobenius_finrank,
    ← FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of ρ)
      ((Action.res (FGModuleCat ℂ) H.subtype).obj S)]
  simp only [resObj_character]

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

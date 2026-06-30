import Mathlib

/-!
# Example 4.3: Irreducible Representations of S₄

S₄ has order 24 with 5 conjugacy classes:
{e}, {(12),...}, {(123),...}, {(1234),...}, {(12)(34),...}

By the sum-of-squares formula: d₁² + d₂² + d₃² + d₄² + d₅² = 24,
the unique solution is dimensions 1, 1, 2, 3, 3.

The five irreducible representations (Etingof Example 4.3):
- Trivial representation `ℂ₊`
- Sign representation `ℂ₋`
- 2-dimensional `ℂ²`: pulled back from `S₃ ≅ S₄/V₄` (`V₄` = Klein four group), realised
  here as the sum-zero subrepresentation of the permutation representation of `S₄` on the
  three partitions of `{0,1,2,3}` into two pairs
- 3-dimensional `ℂ³₋`: the *standard* representation, the functions on `{0,1,2,3}` with zero
  sum of values (book: "the space of functions on the set of four elements with zero sum of
  values"); equivalently the symmetries of the regular tetrahedron
- 3-dimensional `ℂ³₊` = `ℂ₋ ⊗ ℂ³₋`: the rotation group of the cube permuting interior
  diagonals.  `ℂ³₊` and `ℂ³₋` are distinct: on a transposition `g`,
  `det g|_{ℂ³₊} = 1` while `det g|_{ℂ³₋} = (−1)³ = −1`, which here shows up as differing
  character values.

## Genuine formalization

The numerical facts (5 conjugacy classes, `1² + 1² + 2² + 3² + 3² = 24`) are recorded as the
two `decide` theorems below.  Those checks alone are vacuous as a formalization of the
example: they construct no representations and prove nothing irreducible.  This file
therefore builds the **five genuine irreducible representations of `S₄`** as objects of
`FDRep ℂ S₄` and proves each is simple (irreducible) via the character norm-one criterion
`FDRep.simple_iff_char_is_norm_one`, `∑_g χ(g)·χ(g⁻¹) = |S₄| = 24`.

The construction mirrors `Example4_3_S3` (this chapter).

## Mathlib correspondence

Uses `Equiv.Perm (Fin 4)` for S₄ and `Equiv.Perm.sign` for the sign character.
The standard and partition permutation representations and their characters are built here
from scratch; `FDRep.simple_iff_char_is_norm_one` supplies the character criterion.
-/

-- `maxRecDepth` is raised because the kernel quotient enumeration
-- (24 permutations of `Fin 4`, quotiented by conjugacy) recurses past
-- the default limit.
set_option maxRecDepth 10000 in
/-- S₄ has exactly 5 conjugacy classes. (Etingof Example 4.3)

The five conjugacy classes correspond to the five cycle types of `Fin 4`
(equivalently, the five partitions of 4). The count is a finite kernel
computation: enumerate the 24 permutations, quotient by conjugacy, and
count the classes. -/
theorem Etingof.Example4_3_S4_conj_classes :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 4))) = 5 := by
  decide

/-- The sum-of-squares formula for S₄: 1² + 1² + 2² + 3² + 3² = 24 = |S₄|. -/
theorem Etingof.Example4_3_S4_sum_of_squares :
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 + 3 ^ 2 + 3 ^ 2 = Fintype.card (Equiv.Perm (Fin 4)) := by
  decide

open CategoryTheory MonoidalCategory Module

noncomputable section

namespace Etingof.Example4_3_S4

/-- `S₄`, realised as the symmetric group on `Fin 4`. -/
abbrev S4 : Type := Equiv.Perm (Fin 4)

/-! ## The one-dimensional representations `ℂ₊` and `ℂ₋` -/

/-- A one-dimensional representation attached to a multiplicative character `χ : G →* ℂˣ`:
`g` acts on `ℂ` by multiplication by `χ g`. -/
def charRep {G : Type*} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The character of a one-dimensional `charRep χ` is `g ↦ χ g`. -/
@[simp] lemma charRep_character {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (charRep χ)).character g = (χ g : ℂ) := by
  have hg : charRep χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (charRep χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp

/-- Any one-dimensional `charRep χ` is simple as an object of `FDRep ℂ G`: its character
has norm one, `∑ g, χ(g)·χ(g⁻¹) = |G|`. -/
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

/-- The trivial representation `ℂ₊`. -/
def trivRep : FDRep ℂ S4 := FDRep.of (charRep (1 : S4 →* ℂˣ))

/-- The sign character `S₄ →* ℂˣ`, sending a permutation to `±1 ∈ ℂˣ`. -/
def signHom : S4 →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

/-- The sign representation `ℂ₋`. -/
def signRep : FDRep ℂ S4 := FDRep.of (charRep signHom)

/-- The value of the sign character as a complex number is the integer sign. -/
lemma signHom_coe (g : S4) : ((signHom g : ℂˣ) : ℂ) = ((Equiv.Perm.sign g : ℤ) : ℂ) := by
  simp [signHom]

/-- `ℂ₊` is simple (it is one-dimensional). -/
lemma trivRep_simple : Simple trivRep := charRep_simple _

/-- `ℂ₋` is simple (it is one-dimensional). -/
lemma signRep_simple : Simple signRep := charRep_simple _

/-! ## The permutation representation on `Fin 4 → ℂ` and the standard representation `ℂ³₋` -/

/-- The permutation representation of `S₄` on `Fin 4 → ℂ`: `σ` acts by `f ↦ f ∘ σ⁻¹`. -/
def permRep : Representation ℂ S4 (Fin 4 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑σ⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, Equiv.Perm.coe_mul,
      Function.comp_apply]

@[simp] lemma permRep_apply (σ : S4) (f : Fin 4 → ℂ) (i : Fin 4) :
    permRep σ f i = f (σ⁻¹ i) := rfl

/-- The sum map `(Fin 4 → ℂ) →ₗ[ℂ] ℂ`, `f ↦ ∑ i, f i`. -/
def sumLM : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

@[simp] lemma sumLM_apply (f : Fin 4 → ℂ) : sumLM f = ∑ i, f i := by
  simp [sumLM, Finset.sum_apply]

/-- The standard representation `ℂ³₋` as the sum-zero subrepresentation of `permRep`. -/
def stdSub : Subrepresentation permRep where
  toSubmodule := LinearMap.ker sumLM
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, sumLM_apply] at hf ⊢
    calc ∑ i, permRep σ f i = ∑ i, f (σ⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [permRep_apply]
      _ = ∑ i, f i := Equiv.sum_comp (σ⁻¹ : Equiv.Perm (Fin 4)) f
      _ = 0 := hf

/-- The standard (3-dimensional) irreducible representation `ℂ³₋` of `S₄`. -/
def stdRep : FDRep ℂ S4 := FDRep.of stdSub.toRepresentation

/-! ### Character of the permutation and standard representations -/

/-- The all-ones vector `(1,1,1,1) ∈ Fin 4 → ℂ`, spanning the trivial line in `permRep`. -/
def onesVec : Fin 4 → ℂ := fun _ => 1

@[simp] lemma onesVec_apply (i : Fin 4) : onesVec i = 1 := rfl

lemma onesVec_ne_zero : (onesVec : Fin 4 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 0; simp [onesVec] at this

@[simp] lemma permRep_onesVec (g : S4) : permRep g onesVec = onesVec := by
  funext i; simp

/-- The line of constant vectors, the trivial subrepresentation of `permRep`. -/
def constLine : Submodule ℂ (Fin 4 → ℂ) := Submodule.span ℂ {onesVec}

lemma mem_constLine {x : Fin 4 → ℂ} : x ∈ constLine ↔ ∃ c : ℂ, c • onesVec = x :=
  Submodule.mem_span_singleton

/-- `permRep g` is the linear map of the permutation matrix of `g⁻¹`. -/
lemma permRep_eq_toLin' (g : S4) :
    (permRep g) = ((g⁻¹ : S4).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext i
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, permRep_apply]
  rfl

/-- The trace of `permRep g` is the number of fixed points of `g⁻¹` (equivalently of `g`). -/
lemma trace_permRep (g : S4) :
    LinearMap.trace ℂ (Fin 4 → ℂ) (permRep g) = (Function.fixedPoints ⇑g⁻¹).ncard := by
  rw [permRep_eq_toLin', Matrix.trace_toLin'_eq, Matrix.trace_permutation]

/-- The number of fixed points of `g`, as a `Finset` cardinality (decidable). -/
def fixCard (g : S4) : ℕ := (Finset.univ.filter (fun i : Fin 4 => g i = i)).card

lemma perm_inv_fixed_iff (g : S4) (i : Fin 4) : g⁻¹ i = i ↔ g i = i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

lemma fixedPoints_inv_ncard (g : S4) :
    (Function.fixedPoints ⇑g⁻¹).ncard = fixCard g := by
  rw [fixCard, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  exact perm_inv_fixed_iff g i

@[simp] lemma fixCard_inv (g : S4) : fixCard g⁻¹ = fixCard g := by
  rw [fixCard, fixCard]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact perm_inv_fixed_iff g i

/-- **Character of `stdRep`.** For every `g : S₄`, `χ_stdRep(g) = #fix(g) − 1`. -/
lemma stdRep_character (g : S4) :
    stdRep.character g = (fixCard g : ℂ) - 1 := by
  classical
  set N : Fin 2 → Submodule ℂ (Fin 4 → ℂ) := ![stdSub.toSubmodule, constLine] with hN
  have hsurj : Function.Surjective sumLM := by
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    rw [sumLM_apply, Fin.sum_univ_four]
    simp
  have hkerdim : Module.finrank ℂ (LinearMap.ker sumLM) = 3 := by
    have h := sumLM.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi] at h
    simp only [Fintype.card_fin] at h
    omega
  have hsum1 : sumLM onesVec = 4 := by rw [sumLM_apply]; simp
  have hcompl : IsCompl stdSub.toSubmodule constLine := by
    have hone : Module.finrank ℂ constLine = 1 := finrank_span_singleton onesVec_ne_zero
    have hdim : Module.finrank ℂ (Fin 4 → ℂ) ≤
        Module.finrank ℂ stdSub.toSubmodule + Module.finrank ℂ constLine := by
      have hk : Module.finrank ℂ stdSub.toSubmodule = 3 := hkerdim
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
  have hf0 : Set.MapsTo (permRep g) (N 0) (N 0) := stdSub.apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (permRep g) (N 1) (N 1) := by
    intro x hx
    change x ∈ constLine at hx
    change permRep g x ∈ constLine
    rw [mem_constLine] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, permRep_onesVec]⟩
  have hf : ∀ i, Set.MapsTo (permRep g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_permRep, fixedPoints_inv_ncard, Fin.sum_univ_two] at htr
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((permRep g).restrict (hf 0)) = stdRep.character g := by
    change LinearMap.trace ℂ ↥(stdSub.toSubmodule) (stdSub.toRepresentation g)
      = LinearMap.trace ℂ ↥(stdSub.toSubmodule) ((FDRep.of stdSub.toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((permRep g).restrict (hf 1)) = 1 := by
    have hid : (permRep g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : Fin 4 → ℂ) ∈ constLine := x.2
      rw [mem_constLine] at hx
      obtain ⟨c, hc⟩ := hx
      change permRep g (x : Fin 4 → ℂ) = (x : Fin 4 → ℂ)
      rw [← hc, map_smul, permRep_onesVec]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton onesVec_ne_zero
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]
  exact htr.symm

/-- **The standard representation `ℂ³₋` is irreducible** (Etingof Example 4.3).  Proved from
its character: the norm-one identity
`∑_g χ(g)·χ(g⁻¹) = 1·3² + 6·1² + 3·1² + 8·0² + 6·1² = 24 = |S₄|`. -/
lemma stdRep_simple : Simple stdRep := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : S4, stdRep.character g * stdRep.character g⁻¹
      = (((fixCard g : ℤ) - 1) ^ 2 : ℤ) := by
    intro g
    rw [stdRep_character, stdRep_character, fixCard_inv]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Int.cast_sum]
  have hsum : ∑ g : S4, (((fixCard g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num

/-! ## The sign-twisted standard representation `ℂ³₊` -/

/-- Twist a representation `ρ` by a multiplicative character `χ : G →* ℂˣ`: `g` acts by
`(χ g) • ρ g`.  Used to build `ℂ³₊ = ℂ₋ ⊗ ℂ³₋` without invoking the monoidal tensor
product. -/
def twistRep {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (χ : G →* ℂˣ) (ρ : Representation ℂ G V) : Representation ℂ G V where
  toFun g := ((χ g : ℂˣ) : ℂ) • ρ g
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, Units.val_mul, Module.End.mul_eq_comp]
    ext x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul]
    ring_nf

@[simp] lemma twistRep_apply {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (χ : G →* ℂˣ) (ρ : Representation ℂ G V) (g : G) :
    twistRep χ ρ g = ((χ g : ℂˣ) : ℂ) • ρ g := rfl

/-- The character of `twistRep χ ρ` is `χ` times the character of `ρ`. -/
lemma twistRep_character {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (χ : G →* ℂˣ) (ρ : Representation ℂ G V) (g : G) :
    (FDRep.of (twistRep χ ρ)).character g = (χ g : ℂ) * (FDRep.of ρ).character g := by
  change LinearMap.trace ℂ V ((FDRep.of (twistRep χ ρ)).ρ g)
    = (χ g : ℂ) * LinearMap.trace ℂ V ((FDRep.of ρ).ρ g)
  rw [FDRep.of_ρ', FDRep.of_ρ', twistRep_apply, map_smul, smul_eq_mul]

/-- The rotation representation `ℂ³₊ = ℂ₋ ⊗ ℂ³₋`, the sign twist of the standard
representation. -/
def rotRep : FDRep ℂ S4 := FDRep.of (twistRep signHom stdSub.toRepresentation)

/-- **Character of `rotRep`.** `χ_rotRep(g) = sign(g)·(#fix(g) − 1)`. -/
lemma rotRep_character (g : S4) :
    rotRep.character g = ((Equiv.Perm.sign g : ℤ) : ℂ) * ((fixCard g : ℂ) - 1) := by
  rw [rotRep, twistRep_character, signHom_coe]
  congr 1
  exact stdRep_character g

/-- **The rotation representation `ℂ³₊` is irreducible** (Etingof Example 4.3).  Its character
is `sign·χ_stdRep`, so `χ(g)·χ(g⁻¹) = χ_stdRep(g)·χ_stdRep(g⁻¹)` (the signs cancel) and the
norm-one sum is again `24 = |S₄|`. -/
lemma rotRep_simple : Simple rotRep := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : S4, rotRep.character g * rotRep.character g⁻¹
      = (((fixCard g : ℤ) - 1) ^ 2 : ℤ) := by
    intro g
    rw [rotRep_character, rotRep_character, fixCard_inv, Equiv.Perm.sign_inv]
    have hsign : ((Equiv.Perm.sign g : ℤ) : ℂ) ^ 2 = 1 := by
      rw [sq, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have key : ((Equiv.Perm.sign g : ℤ) : ℂ) * ((fixCard g : ℂ) - 1)
        * (((Equiv.Perm.sign g : ℤ) : ℂ) * ((fixCard g : ℂ) - 1))
        = ((Equiv.Perm.sign g : ℤ) : ℂ) ^ 2 * ((fixCard g : ℂ) - 1) ^ 2 := by ring
    rw [key, hsign, one_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Int.cast_sum]
  have hsum : ∑ g : S4, (((fixCard g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num

/-! ## The 2-dimensional representation `ℂ²`

`S₄` acts on the three partitions of `{0,1,2,3}` into two pairs; the kernel of this action
is the Klein four group `V₄ = {e, (01)(23), (02)(13), (03)(12)}`, so the action factors
through `S₄/V₄ ≅ S₃`.  The 2-dimensional representation `ℂ²` is the sum-zero subrepresentation
of the associated 3-dimensional permutation representation — exactly the pullback of the
standard representation of `S₃`.

The three partitions are indexed by `Fin 3`: `0 = {01|23}`, `1 = {02|13}`, `2 = {03|12}`.
A partition is determined by the unordered pair containing `0`, so partition `i` is `{0, i+1}`
together with its complement, and `σ` sends partition `i` to the partition whose pair-type is
that of `{σ 0, σ (i+1)}`. -/

/-- Index of the pair-partition containing the unordered pair `{a, b}` (for `a ≠ b`).
`0 = {01|23}`, `1 = {02|13}`, `2 = {03|12}`. -/
def pairIdx (a b : Fin 4) : Fin 3 :=
  if (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) ∨
     (a.val = 2 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 2) then 0
  else if (a.val = 0 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 0) ∨
          (a.val = 1 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 1) then 1
  else 2

/-- The action of `σ ∈ S₄` on the three partitions: `σ` sends partition `i` (the pair
`{0, i+1}`) to the partition containing `{σ 0, σ (i+1)}`. -/
def actFun (σ : S4) (i : Fin 3) : Fin 3 := pairIdx (σ 0) (σ i.succ)

lemma actFun_one (i : Fin 3) : actFun 1 i = i := by revert i; decide

set_option maxRecDepth 10000 in
lemma actFun_mul (σ τ : S4) (i : Fin 3) :
    actFun (σ * τ) i = actFun σ (actFun τ i) := by revert σ τ i; decide

/-- The action of `σ` on the three partitions, packaged as a permutation of `Fin 3`. -/
def actEquiv (σ : S4) : Equiv.Perm (Fin 3) where
  toFun := actFun σ
  invFun := actFun σ⁻¹
  left_inv i := by rw [actFun_mul (σ⁻¹) σ i |>.symm, inv_mul_cancel, actFun_one]
  right_inv i := by rw [actFun_mul σ (σ⁻¹) i |>.symm, mul_inv_cancel, actFun_one]

@[simp] lemma actEquiv_apply (σ : S4) (i : Fin 3) : actEquiv σ i = actFun σ i := rfl

/-- The permutation action of `S₄` on the three partitions, as a group homomorphism
`S₄ →* Perm (Fin 3)`.  Its kernel is the Klein four group `V₄`. -/
def actHom : S4 →* Equiv.Perm (Fin 3) where
  toFun := actEquiv
  map_one' := by ext i; simp [actFun_one]
  map_mul' a b := by ext i; simp [Equiv.Perm.mul_apply, actFun_mul]

@[simp] lemma actHom_apply (σ : S4) (i : Fin 3) : actHom σ i = actFun σ i := rfl

/-- The permutation representation of `S₄` on `Fin 3 → ℂ` (functions on the three
partitions): `σ` acts by `f ↦ f ∘ (actHom σ)⁻¹`. -/
def permRep3 : Representation ℂ S4 (Fin 3 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑(actHom σ)⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext i
    simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [map_mul, Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev,
      Equiv.Perm.coe_mul, Function.comp_apply]

@[simp] lemma permRep3_apply (σ : S4) (f : Fin 3 → ℂ) (i : Fin 3) :
    permRep3 σ f i = f ((actHom σ)⁻¹ i) := rfl

/-- The sum map `(Fin 3 → ℂ) →ₗ[ℂ] ℂ`. -/
def sumLM3 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

@[simp] lemma sumLM3_apply (f : Fin 3 → ℂ) : sumLM3 f = ∑ i, f i := by
  simp [sumLM3, Finset.sum_apply]

/-- The 2-dimensional representation `ℂ²` as the sum-zero subrepresentation of `permRep3`. -/
def twoDimSub : Subrepresentation permRep3 where
  toSubmodule := LinearMap.ker sumLM3
  apply_mem_toSubmodule σ f hf := by
    simp only [LinearMap.mem_ker, sumLM3_apply] at hf ⊢
    calc ∑ i, permRep3 σ f i = ∑ i, f ((actHom σ)⁻¹ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [permRep3_apply]
      _ = ∑ i, f i := Equiv.sum_comp ((actHom σ)⁻¹) f
      _ = 0 := hf

/-- The 2-dimensional irreducible representation `ℂ²` of `S₄`. -/
def twoDimRep : FDRep ℂ S4 := FDRep.of twoDimSub.toRepresentation

/-! ### Character of the 2-dimensional representation -/

/-- The all-ones vector on the three partitions. -/
def onesVec3 : Fin 3 → ℂ := fun _ => 1

@[simp] lemma onesVec3_apply (i : Fin 3) : onesVec3 i = 1 := rfl

lemma onesVec3_ne_zero : (onesVec3 : Fin 3 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 0; simp [onesVec3] at this

@[simp] lemma permRep3_onesVec3 (g : S4) : permRep3 g onesVec3 = onesVec3 := by
  funext i; simp

/-- The line of constant vectors in `Fin 3 → ℂ`. -/
def constLine3 : Submodule ℂ (Fin 3 → ℂ) := Submodule.span ℂ {onesVec3}

lemma mem_constLine3 {x : Fin 3 → ℂ} : x ∈ constLine3 ↔ ∃ c : ℂ, c • onesVec3 = x :=
  Submodule.mem_span_singleton

lemma permRep3_eq_toLin' (g : S4) :
    (permRep3 g) = (((actHom g)⁻¹).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext i
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, permRep3_apply]
  rfl

lemma trace_permRep3 (g : S4) :
    LinearMap.trace ℂ (Fin 3 → ℂ) (permRep3 g)
      = (Function.fixedPoints ⇑(actHom g)⁻¹).ncard := by
  rw [permRep3_eq_toLin', Matrix.trace_toLin'_eq, Matrix.trace_permutation]

/-- The number of partitions fixed by `g` (decidable). -/
def fix3Card (g : S4) : ℕ := (Finset.univ.filter (fun i : Fin 3 => actFun g i = i)).card

lemma actHom_inv_fixed_iff (g : S4) (i : Fin 3) : (actHom g)⁻¹ i = i ↔ actFun g i = i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm, actHom_apply]

lemma fixedPoints_actHom_inv_ncard (g : S4) :
    (Function.fixedPoints ⇑(actHom g)⁻¹).ncard = fix3Card g := by
  rw [fix3Card, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  exact actHom_inv_fixed_iff g i

/-- **Character of `twoDimRep`.** `χ(g) = #{partitions fixed by g} − 1`. -/
lemma twoDimRep_character (g : S4) :
    twoDimRep.character g = (fix3Card g : ℂ) - 1 := by
  classical
  set N : Fin 2 → Submodule ℂ (Fin 3 → ℂ) := ![twoDimSub.toSubmodule, constLine3] with hN
  have hsurj : Function.Surjective sumLM3 := by
    intro c
    refine ⟨Pi.single 0 c, ?_⟩
    rw [sumLM3_apply, Fin.sum_univ_three]
    simp
  have hkerdim : Module.finrank ℂ (LinearMap.ker sumLM3) = 2 := by
    have h := sumLM3.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_pi] at h
    simp only [Fintype.card_fin] at h
    omega
  have hsum1 : sumLM3 onesVec3 = 3 := by rw [sumLM3_apply]; simp
  have hcompl : IsCompl twoDimSub.toSubmodule constLine3 := by
    have hone : Module.finrank ℂ constLine3 = 1 := finrank_span_singleton onesVec3_ne_zero
    have hdim : Module.finrank ℂ (Fin 3 → ℂ) ≤
        Module.finrank ℂ twoDimSub.toSubmodule + Module.finrank ℂ constLine3 := by
      have hk : Module.finrank ℂ twoDimSub.toSubmodule = 2 := hkerdim
      rw [hk, hone, Module.finrank_pi]
      simp
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_constLine3] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : sumLM3 (c • onesVec3) = 0 := hxk
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
  have hf0 : Set.MapsTo (permRep3 g) (N 0) (N 0) := twoDimSub.apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (permRep3 g) (N 1) (N 1) := by
    intro x hx
    change x ∈ constLine3 at hx
    change permRep3 g x ∈ constLine3
    rw [mem_constLine3] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, permRep3_onesVec3]⟩
  have hf : ∀ i, Set.MapsTo (permRep3 g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_permRep3, fixedPoints_actHom_inv_ncard, Fin.sum_univ_two] at htr
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((permRep3 g).restrict (hf 0)) = twoDimRep.character g := by
    change LinearMap.trace ℂ ↥(twoDimSub.toSubmodule) (twoDimSub.toRepresentation g)
      = LinearMap.trace ℂ ↥(twoDimSub.toSubmodule) ((FDRep.of twoDimSub.toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((permRep3 g).restrict (hf 1)) = 1 := by
    have hid : (permRep3 g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : Fin 3 → ℂ) ∈ constLine3 := x.2
      rw [mem_constLine3] at hx
      obtain ⟨c, hc⟩ := hx
      change permRep3 g (x : Fin 3 → ℂ) = (x : Fin 3 → ℂ)
      rw [← hc, map_smul, permRep3_onesVec3]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton onesVec3_ne_zero
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]
  exact htr.symm

/-- **The 2-dimensional representation `ℂ²` is irreducible** (Etingof Example 4.3).  Proved
from its character: `∑_g χ(g)·χ(g⁻¹) = 1·2² + 3·2² + 8·1² = 24 = |S₄|` (with `χ = fix₃ − 1`,
the fixed-partition count minus one). -/
lemma twoDimRep_simple : Simple twoDimRep := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : S4, twoDimRep.character g * twoDimRep.character g⁻¹
      = (((fix3Card g : ℤ) - 1) * ((fix3Card g⁻¹ : ℤ) - 1) : ℤ) := by
    intro g
    rw [twoDimRep_character, twoDimRep_character]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Int.cast_sum]
  have hsum : ∑ g : S4, (((fix3Card g : ℤ) - 1) * ((fix3Card g⁻¹ : ℤ) - 1)) = 24 := by decide
  rw [hsum]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num

/-! ## `ℂ³₊` and `ℂ³₋` are distinct -/

/-- **`ℂ³₊` and `ℂ³₋` are not isomorphic** (Etingof Example 4.3): on a transposition `g`,
`det g|_{ℂ³₊} = 1` while `det g|_{ℂ³₋} = (−1)³ = −1`, which shows up here as differing
character values, `χ_{ℂ³₋}((01)) = 1 ≠ −1 = χ_{ℂ³₊}((01))`. -/
lemma stdRep_character_ne_rotRep_character :
    stdRep.character (Equiv.swap 0 1) ≠ rotRep.character (Equiv.swap 0 1) := by
  rw [stdRep_character, rotRep_character, show fixCard (Equiv.swap (0 : Fin 4) 1) = 2 from by decide,
    show Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 from by decide]
  norm_num

/-! ## Dimensions: the sum-of-squares decomposition `1² + 1² + 2² + 3² + 3² = 24` -/

/-- `dim ℂ₊ = 1`. -/
lemma trivRep_finrank : finrank ℂ (trivRep : Type) = 1 := by
  have h := FDRep.char_one trivRep
  rw [show trivRep = FDRep.of (charRep (1 : S4 →* ℂˣ)) from rfl, charRep_character] at h
  simp only [map_one, Units.val_one] at h
  exact_mod_cast h.symm

/-- `dim ℂ₋ = 1`. -/
lemma signRep_finrank : finrank ℂ (signRep : Type) = 1 := by
  have h := FDRep.char_one signRep
  rw [show signRep = FDRep.of (charRep signHom) from rfl, charRep_character] at h
  simp only [map_one, Units.val_one] at h
  exact_mod_cast h.symm

/-- `χ_{ℂ²}(1) = 2`. -/
lemma twoDimRep_char_one : twoDimRep.character 1 = 2 := by
  rw [twoDimRep_character, show fix3Card (1 : S4) = 3 from by decide]; norm_num

/-- `χ_{ℂ³₋}(1) = 3`. -/
lemma stdRep_char_one : stdRep.character 1 = 3 := by
  rw [stdRep_character, show fixCard (1 : S4) = 4 from by decide]; norm_num

/-- `χ_{ℂ³₊}(1) = 3`. -/
lemma rotRep_char_one : rotRep.character 1 = 3 := by
  rw [rotRep_character, show fixCard (1 : S4) = 4 from by decide, map_one, Units.val_one]
  norm_num

/-- `dim ℂ² = 2`. -/
lemma twoDimRep_finrank : finrank ℂ (twoDimRep : Type) = 2 := by
  have h := FDRep.char_one twoDimRep
  rw [twoDimRep_char_one] at h
  exact_mod_cast h.symm

/-- `dim ℂ³₋ = 3`. -/
lemma stdRep_finrank : finrank ℂ (stdRep : Type) = 3 := by
  have h := FDRep.char_one stdRep
  rw [stdRep_char_one] at h
  exact_mod_cast h.symm

/-- `dim ℂ³₊ = 3`. -/
lemma rotRep_finrank : finrank ℂ (rotRep : Type) = 3 := by
  have h := FDRep.char_one rotRep
  rw [rotRep_char_one] at h
  exact_mod_cast h.symm

/-- The dimensions `1, 1, 2, 3, 3` of the five irreducible representations realise the
sum-of-squares decomposition `1² + 1² + 2² + 3² + 3² = 24 = |S₄|`. (Etingof Example 4.3) -/
theorem irreps_dim_sum_of_squares :
    finrank ℂ (trivRep : Type) ^ 2 + finrank ℂ (signRep : Type) ^ 2
      + finrank ℂ (twoDimRep : Type) ^ 2 + finrank ℂ (stdRep : Type) ^ 2
      + finrank ℂ (rotRep : Type) ^ 2 = Fintype.card S4 := by
  rw [trivRep_finrank, signRep_finrank, twoDimRep_finrank, stdRep_finrank, rotRep_finrank]
  decide

end Etingof.Example4_3_S4

end

import Mathlib

/-!
# Example 4.3: Irreducible Representations of S₃

The symmetric group S₃ has 3 conjugacy classes: {e}, {(12),(13),(23)}, {(123),(132)}.
By the sum-of-squares formula d₁² + d₂² + d₃² = 6, the dimensions are 1, 1, 2.

The three irreducible representations are:
- The trivial representation `ℂ₊` given by `ρ(σ) = 1`
- The sign representation `ℂ₋` given by `ρ(σ) = (−1)^σ`
- The 2-dimensional standard representation `ℂ²`, realized as the symmetries of an
  equilateral triangle.

Etingof proves that the standard representation is irreducible: any subrepresentation must
be spanned by a subset of the eigenvectors of `ρ((12))` and simultaneously by a subset of
the eigenvectors of `ρ((123))`, and since these eigenvectors differ, the only invariant
subspaces are `0` and `ℂ²`.

## Genuine formalization

The numerical facts (3 conjugacy classes, `1² + 1² + 2² = 6`) are recorded as the two
`decide` theorems below.  But those checks alone are vacuous as a formalization of the
example: they construct no representations and prove nothing irreducible.  This file
therefore builds the **three genuine irreducible representations of `S₃`** as objects of
`FDRep ℂ S₃` and proves each is simple (irreducible):

* `trivRep`, `signRep`, `stdRep` — the trivial, sign, and standard (2-dimensional)
  representations, the last realised as the sum-zero subrepresentation of the permutation
  representation on `Fin 3 → ℂ`.
* `trivRep_simple`, `signRep_simple` — the one-dimensional representations are simple.
* `stdRep_simple` — **the standard representation is irreducible**, the book's main claim
  for this example.  It is proved from the actual character of `stdRep` (a trace of a real
  representation) via the norm-one criterion
  `∑_g χ(g)·χ(g⁻¹) = 1·2² + 3·0² + 2·(−1)² = 6 = |S₃|`.
* `trivRep_finrank`, `signRep_finrank`, `stdRep_finrank` — the dimensions `1, 1, 2`
  realising the sum-of-squares decomposition `1² + 1² + 2² = 6`.

The construction mirrors the sorry-free `S₃` catalogue rebuilt in `Example4_9_1` (this
chapter) and `Discussion5_11_examples` (Chapter 5).

## Mathlib correspondence

Mathlib has `Equiv.Perm` for symmetric groups and `Equiv.Perm.sign` for the sign character.
The standard representation and its character are built here from scratch;
`FDRep.simple_iff_char_is_norm_one` supplies the character criterion for simplicity.
-/

/-- S₃ has exactly 3 irreducible representations (over ℂ or any algebraically closed
field of characteristic ≠ 2, 3). (Etingof Example 4.3) -/
theorem Etingof.Example4_3_S3_irreps_count :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 3))) = 3 := by
  decide

/-- The sum-of-squares formula for S₃: 1² + 1² + 2² = 6 = |S₃|. -/
theorem Etingof.Example4_3_S3_sum_of_squares :
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 = Fintype.card (Equiv.Perm (Fin 3)) := by
  decide

open CategoryTheory MonoidalCategory Module

noncomputable section

namespace Etingof.Example4_3_S3

/-- `S₃`, realised as the symmetric group on `Fin 3`. -/
abbrev S3 : Type := Equiv.Perm (Fin 3)

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
def trivRep : FDRep ℂ S3 := FDRep.of (charRep (1 : S3 →* ℂˣ))

/-- The sign character `S₃ →* ℂˣ`, sending a permutation to `±1 ∈ ℂˣ`. -/
def signHom : S3 →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

/-- The sign representation `ℂ₋`. -/
def signRep : FDRep ℂ S3 := FDRep.of (charRep signHom)

/-- The value of the sign character as a complex number is the integer sign. -/
lemma signHom_coe (g : S3) : ((signHom g : ℂˣ) : ℂ) = ((Equiv.Perm.sign g : ℤ) : ℂ) := by
  simp [signHom]

/-- `ℂ₊` is simple (it is one-dimensional). -/
lemma trivRep_simple : Simple trivRep := charRep_simple _

/-- `ℂ₋` is simple (it is one-dimensional). -/
lemma signRep_simple : Simple signRep := charRep_simple _

/-! ## The standard representation `ℂ²` -/

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

/-! ### Character of `stdRep`

Computed by viewing `permRep` as the internal direct sum of the sum-zero subspace and the
line of constant vectors: `χ_permRep = χ_stdRep + 1`, and `χ_permRep(g) = #fix(g)`. -/

/-- The all-ones vector `(1, 1, 1) ∈ Fin 3 → ℂ`, spanning the trivial line in `permRep`. -/
def onesVec : Fin 3 → ℂ := fun _ => 1

@[simp] lemma onesVec_apply (i : Fin 3) : onesVec i = 1 := rfl

lemma onesVec_ne_zero : (onesVec : Fin 3 → ℂ) ≠ 0 := by
  intro h; have := congrFun h 0; simp [onesVec] at this

@[simp] lemma permRep_onesVec (g : S3) : permRep g onesVec = onesVec := by
  funext i; simp

/-- The line of constant vectors, the trivial subrepresentation of `permRep`. -/
def constLine : Submodule ℂ (Fin 3 → ℂ) := Submodule.span ℂ {onesVec}

lemma mem_constLine {x : Fin 3 → ℂ} : x ∈ constLine ↔ ∃ c : ℂ, c • onesVec = x :=
  Submodule.mem_span_singleton

/-- `permRep g` is the linear map of the permutation matrix of `g⁻¹`. -/
lemma permRep_eq_toLin' (g : S3) :
    (permRep g) = ((g⁻¹ : S3).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext i
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, permRep_apply]
  rfl

/-- The trace of `permRep g` is the number of fixed points of `g⁻¹` (equivalently of `g`). -/
lemma trace_permRep (g : S3) :
    LinearMap.trace ℂ (Fin 3 → ℂ) (permRep g) = (Function.fixedPoints ⇑g⁻¹).ncard := by
  rw [permRep_eq_toLin', Matrix.trace_toLin'_eq, Matrix.trace_permutation]

/-- The number of fixed points of `g`, as a `Finset` cardinality (decidable). -/
def fixCard (g : S3) : ℕ := (Finset.univ.filter (fun i : Fin 3 => g i = i)).card

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
  set N : Fin 2 → Submodule ℂ (Fin 3 → ℂ) := ![stdSub.toSubmodule, constLine] with hN
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
      have hx : (x : Fin 3 → ℂ) ∈ constLine := x.2
      rw [mem_constLine] at hx
      obtain ⟨c, hc⟩ := hx
      change permRep g (x : Fin 3 → ℂ) = (x : Fin 3 → ℂ)
      rw [← hc, map_smul, permRep_onesVec]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton onesVec_ne_zero
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]
  exact htr.symm

/-- **The standard representation `ℂ²` is irreducible** (Etingof Example 4.3).  Proved from
its character: the norm-one identity `∑_g χ(g)·χ(g⁻¹) = 1·2² + 3·0² + 2·(−1)² = 6 = |S₃|`. -/
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

/-! ## Dimensions: the sum-of-squares decomposition `1² + 1² + 2² = 6` -/

/-- `χ_stdRep(1) = 2`, the dimension of `stdRep`. -/
lemma stdRep_char_one : stdRep.character 1 = 2 := by
  rw [stdRep_character]
  have : fixCard (1 : S3) = 3 := by decide
  rw [this]; norm_num

/-- `dim ℂ₊ = 1`. -/
lemma trivRep_finrank : finrank ℂ (trivRep : Type) = 1 := by
  have h := FDRep.char_one trivRep
  rw [show trivRep = FDRep.of (charRep (1 : S3 →* ℂˣ)) from rfl, charRep_character] at h
  simp only [map_one, Units.val_one] at h
  exact_mod_cast h.symm

/-- `dim ℂ₋ = 1`. -/
lemma signRep_finrank : finrank ℂ (signRep : Type) = 1 := by
  have h := FDRep.char_one signRep
  rw [show signRep = FDRep.of (charRep signHom) from rfl, charRep_character] at h
  simp only [map_one, Units.val_one] at h
  exact_mod_cast h.symm

/-- `dim ℂ² = 2`. -/
lemma stdRep_finrank : finrank ℂ (stdRep : Type) = 2 := by
  have h := FDRep.char_one stdRep
  rw [stdRep_char_one] at h
  exact_mod_cast h.symm

/-- The dimensions `1, 1, 2` of the three irreducible representations realise the
sum-of-squares decomposition `1² + 1² + 2² = 6 = |S₃|`. (Etingof Example 4.3) -/
theorem irreps_dim_sum_of_squares :
    finrank ℂ (trivRep : Type) ^ 2 + finrank ℂ (signRep : Type) ^ 2
      + finrank ℂ (stdRep : Type) ^ 2 = Fintype.card S3 := by
  rw [trivRep_finrank, signRep_finrank, stdRep_finrank]
  decide

end Etingof.Example4_3_S3

end

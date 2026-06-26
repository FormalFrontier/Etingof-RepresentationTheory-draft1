import Mathlib

/-!
# Example 4.9.1: Tensor Product Multiplicities

Etingof's Example 4.9.1 records the full Clebsch-Gordan (tensor-product) multiplicity
tables of the irreducible representations of `S₃`, `S₄`, and `A₅`.  For `S₃` the table is

| `S₃` | `ℂ₊` | `ℂ₋` | `ℂ²` |
|---|---|---|---|
| `ℂ₊` | `ℂ₊` | `ℂ₋` | `ℂ²` |
| `ℂ₋` |  | `ℂ₊` | `ℂ²` |
| `ℂ²` |  |  | `ℂ₊ ⊕ ℂ₋ ⊕ ℂ²` |

so for instance `ℂ² ⊗ ℂ² = ℂ₊ ⊕ ℂ₋ ⊕ ℂ²`.  The book computes each entry from the
character formula `n_{ij}^k = (χ_i · χ_j, χ_k)`; equivalently, the product of two
irreducible characters decomposes as the integer combination `χ_i · χ_j = Σ_k n_{ij}^k χ_k`
of irreducible characters, which is exactly the statement `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k`.

## Genuine formalization (S₃)

The earlier version of this file encoded the three character tables as hand-typed matrices
over a formal ring `ℚ[√5]` and proved an *orthonormality certificate* by `native_decide`.
That is a vacuous statement: orthonormality of an arbitrary square of numbers pins down
neither *the* character table nor any actual representation, and `native_decide` is a
forbidden trust hole.  It was rejected in the review of issue #5377.

This file instead builds the **genuine irreducible representations of `S₃`** as objects of
`FDRep ℂ S₃` and proves the tensor-product multiplicity identity from their *actual
characters* (traces of real representations), with no `native_decide`:

* `trivRep`, `signRep`, `stdRep` — the trivial, sign, and standard (2-dimensional)
  irreducibles, the last realised as the sum-zero subrepresentation of the permutation
  representation on `Fin 3 → ℂ`.
* `irrep_char` — each character is computed as a trace: `χ_{ℂ₊} = 1`, `χ_{ℂ₋} = sign`,
  `χ_{ℂ²}(g) = #fix(g) − 1`.
* `S3_tensor_character` — the book's multiplicity identity
  `χ_i(g) · χ_j(g) = Σ_k n_{ij}^k · χ_k(g)`, proved for *every* group element from the real
  characters.
* `S3_tensor_product_character` — the same identity phrased on the genuine tensor product
  `V_i ⊗ V_j` of `FDRep`s, via `FDRep.char_tensor`.  This is the character form of
  `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k`.

The `S₄` and `A₅` tables require their full irreducible catalogues (for `A₅`, the two
3-dimensional icosahedral representations with golden-ratio character values over `ℚ(√5)`);
those genuine constructions are tracked as follow-up work and are deliberately **not**
shipped here as orthonormality certificates.

## Mathlib correspondence

Tensor-product decomposition multiplicities for these groups are not in Mathlib; the
standard representation and its character are built here from scratch.  `FDRep.char_tensor`
supplies `(V ⊗ W).character = V.character · W.character`.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Etingof.Example4_9_1

/-- `S₃`, realised as the symmetric group on `Fin 3`. -/
abbrev S3 : Type := Equiv.Perm (Fin 3)

/-! ## The three irreducible representations of `S₃` (genuine, trace-based)

The construction mirrors the sorry-free `S₃` catalogue used in Chapter 5
(`Discussion5_11_examples`); it is rebuilt here because Chapter 5 imports Chapter 4. -/

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

/-! ### The standard representation `ℂ²` -/

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

open Module

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

/-! ## The irreducible catalogue and character values -/

/-- The three irreducible representations of `S₃`, indexed `0, 1, 2` as `ℂ₊, ℂ₋, ℂ²`. -/
def irrep : Fin 3 → FDRep ℂ S3 := ![trivRep, signRep, stdRep]

/-- The three character values as a function: `1`, `sign`, `#fix − 1`. -/
def charVal (g : S3) : Fin 3 → ℂ := ![1, ((signHom g : ℂˣ) : ℂ), (fixCard g : ℂ) - 1]

lemma char_triv (g : S3) : (irrep 0).character g = 1 := by
  change (FDRep.of (charRep (1 : S3 →* ℂˣ))).character g = 1
  rw [charRep_character]; simp

lemma char_sign (g : S3) : (irrep 1).character g = ((signHom g : ℂˣ) : ℂ) := by
  change (FDRep.of (charRep signHom)).character g = _
  rw [charRep_character]

lemma char_std (g : S3) : (irrep 2).character g = (fixCard g : ℂ) - 1 := by
  change stdRep.character g = _
  exact stdRep_character g

/-- Each irreducible character is the trace of the corresponding real representation. -/
lemma irrep_char (i : Fin 3) (g : S3) : (irrep i).character g = charVal g i := by
  fin_cases i
  · exact char_triv g
  · exact char_sign g
  · exact char_std g

/-! ## The tensor-product multiplicity table of `S₃`

`nS3 i j k` is the multiplicity of the `k`-th irreducible in `V_i ⊗ V_j`. -/

/-- Tensor-product multiplicity table of `S₃`. -/
def nS3 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![1,0,0], ![0,1,0], ![0,0,1]],
    ![![0,1,0], ![1,0,0], ![0,0,1]],
    ![![0,0,1], ![0,0,1], ![1,1,1]]]

/-- The pair `(sign g, #fix g)` takes exactly one of three values over `S₃`: `(1, 3)` for the
identity, `(−1, 1)` for the three transpositions, `(1, 0)` for the two 3-cycles.  This is the
only group-specific input to the multiplicity identity. -/
lemma sign_fix_cases (g : S3) :
    (Equiv.Perm.sign g = 1 ∧ fixCard g = 3) ∨
    (Equiv.Perm.sign g = -1 ∧ fixCard g = 1) ∨
    (Equiv.Perm.sign g = 1 ∧ fixCard g = 0) := by
  revert g; decide

/-- **Tensor-product multiplicity identity for `S₃`** (Etingof Example 4.9.1).  For every group
element `g` and all `i, j`, the product of the two irreducible characters decomposes as the
tabulated integer combination of irreducible characters:
`χ_i(g) · χ_j(g) = Σ_k n_{ij}^k · χ_k(g)`.  Proved from the actual characters (traces) of the
three real representations — no `native_decide`. -/
theorem S3_tensor_character (i j : Fin 3) (g : S3) :
    (irrep i).character g * (irrep j).character g
      = ∑ k, (nS3 i j k : ℂ) * (irrep k).character g := by
  have hsign := signHom_coe g
  simp only [irrep_char, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp only [charVal, nS3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue] <;>
    rcases sign_fix_cases g with ⟨hs, hf⟩ | ⟨hs, hf⟩ | ⟨hs, hf⟩ <;>
    · rw [hsign, hs, hf]; push_cast; ring

/-- **Tensor-product decomposition for `S₃`** phrased on genuine `FDRep` tensor products:
`(V_i ⊗ V_j).character g = Σ_k n_{ij}^k · χ_k(g)`, i.e. the character form of
`V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k`.  (Etingof Example 4.9.1) -/
theorem S3_tensor_product_character (i j : Fin 3) (g : S3) :
    (irrep i ⊗ irrep j).character g = ∑ k, (nS3 i j k : ℂ) * (irrep k).character g := by
  rw [FDRep.char_tensor, Pi.mul_apply]
  exact S3_tensor_character i j g

/-! ## Underlying combinatorial data -/

/-- `S₃` has exactly 3 conjugacy classes, hence 3 irreducible representations
(the trivial, sign, and standard representations above). (Etingof Example 4.9.1) -/
theorem S3_conj_classes :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 3))) = 3 := by
  decide

/-- `S₃` has order 6.  Combined with 3 conjugacy classes, the sum-of-squares formula
`∑ dᵢ² = |G|` forces dimensions 1, 1, 2. (Etingof Example 4.9.1) -/
theorem S3_card :
    Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  decide

end Etingof.Example4_9_1

end

import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_8_1
import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Infrastructure.FDRepDirectSum

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

The book asserts decompositions of *representations*, so for each of the three groups the
table is formalized twice: first as the character identity it is computed from, and then as
the isomorphism of representations it asserts.  The right-hand side `⊕_k n_{ij}^k V_k` is the
object `multSum` built below, and the upgrade is `Etingof.charEq_iso` (Chapter 5: over `ℂ`,
equal characters imply isomorphism).  The isomorphisms are `S3_tensor_iso`, `S4_tensor_iso`,
`A5_tensor_iso` — one statement quantified over `i, j`, hence covering *every* entry of all
three tables, including the multiplicity-2 constituents of `ℂ⁴ ⊗ ℂ⁵` and `ℂ⁵ ⊗ ℂ⁵` for `A₅` —
with `*_biproduct` variants stated using the categorical `⨁`.

## The representations of `S₃`

The three irreducible representations of `S₃` are built as objects of `FDRep ℂ S₃`, and the
tensor-product multiplicity identity is proved from their characters (traces of the
representations):

* `trivRep`, `signRep`, `stdRep`: the trivial, sign, and standard (2-dimensional)
  irreducibles, the last realised as the sum-zero subrepresentation of the permutation
  representation on `Fin 3 → ℂ`.
* `irrep_char`: each character is computed as a trace: `χ_{ℂ₊} = 1`, `χ_{ℂ₋} = sign`,
  `χ_{ℂ²}(g) = #fix(g) − 1`.
* `S3_tensor_character`: the book's multiplicity identity
  `χ_i(g) · χ_j(g) = Σ_k n_{ij}^k · χ_k(g)`, proved for every group element from the
  characters.
* `S3_tensor_product_character`: the same identity phrased on the tensor product
  `V_i ⊗ V_j` of `FDRep`s, via `FDRep.char_tensor`.  This is the character form of
  `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k`.
* `S3_tensor_iso` / `S3_tensor_iso_biproduct`: the decomposition itself,
  `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` in `FDRep ℂ S₃`, for every entry of the table;
  `stdRep_tensor_stdRep_iso` spells out the one nontrivial entry `ℂ² ⊗ ℂ² ≅ ℂ₊ ⊕ ℂ₋ ⊕ ℂ²`.

## The representations of `A₅`

The `A₅` table is formalized the same way, reusing the irreducible catalogue built in
`Example4_8_1` (`Etingof.Example4_8_1.A5`): the trivial `ℂ`, the two 3-dimensional icosahedral
representations `ℂ³₊`, `ℂ³₋` (whose characters take the golden-ratio values `(1 ± √5)/2` on the
two classes of 5-cycles, hence live over `ℚ(√5)`), the 4-dimensional `ℂ⁴` (deleted permutation
representation on `Fin 5`), and the 5-dimensional `ℂ⁵`.  Because the characters are class
functions, the multiplicity identity for every `g` reduces to the five conjugacy classes via
`Etingof.Example4_8_1.A5.classIdxA5_spec` and `FDRep.char_conj`, and there it is the tabulated
`ℚ(√5)` arithmetic (`nA5_char`), with the `√5` terms handled by `√5² = 5`.

* `A5_tensor_character`: `χ_i(g) · χ_j(g) = Σ_k n_{ij}^k · χ_k(g)` for every `g`, from the
  characters (traces) of the five representations.
* `A5_tensor_product_character`: the same identity on the tensor product
  `V_i ⊗ V_j` of `FDRep`s, via `FDRep.char_tensor`.
* `A5_tensor_iso` / `A5_tensor_iso_biproduct`: the decomposition itself,
  `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` in `FDRep ℂ A₅`, for every entry of the table.

## The representations of `S₄`

The `S₄` table is formalized the same way, reusing the irreducible catalogue built in
`Example4_8_1` (`Etingof.Example4_8_1.S4.irrepS4`): the trivial `ℂ₊`, the sign `ℂ₋`, the
2-dimensional `ℂ²` (deleted conjugation-on-partitions representation), and the two 3-dimensionals
`ℂ³₋` (deleted permutation representation on `Fin 4`) and `ℂ³₊ = ℂ³₋ ⊗ sign`.  Every `S₄`
character value is a rational integer (the table `Etingof.Example4_8_1.S4.tbl`), so the
multiplicity identity for every `g` reduces, via `Etingof.Example4_8_1.S4.classRepS4` and
`FDRep.char_conj`, to a pure integer `5·5·5` case split (`nS4_char_int`), with no `√5`.

* `S4_tensor_character`: `χ_i(g) · χ_j(g) = Σ_k n_{ij}^k · χ_k(g)` for every `g`, from the
  characters (traces) of the five representations.
* `S4_tensor_product_character`: the same identity on the tensor product
  `V_i ⊗ V_j` of `FDRep`s, via `FDRep.char_tensor`.
* `S4_tensor_iso` / `S4_tensor_iso_biproduct`: the decomposition itself,
  `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` in `FDRep ℂ S₄`, for every entry of the table.

## Mathlib correspondence

Tensor-product decomposition multiplicities for these groups are not in Mathlib; the
standard representation and its character are built here from scratch.  `FDRep.char_tensor`
supplies `(V ⊗ W).character = V.character · W.character`.  Mathlib has no `⨁`-indexed
biproduct for `FDRep`, so the right-hand sides are built with `Etingof.FDRep.pi`
(`Infrastructure/FDRepDirectSum`), and the converse of `FDRep.char_iso` needed to go from
characters to isomorphisms is `Etingof.charEq_iso` (`Chapter5/CharEqIso`).
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Etingof.Example4_9_1

/-! ## The right-hand sides of the tables, and the character-to-isomorphism bridge

Every entry of Etingof's three tables is a direct sum `⊕_k n_{ij}^k V_k` of irreducibles with
multiplicities, so the right-hand side needs to exist as an object of `FDRep ℂ G` before the
table entry can be stated as an isomorphism.  `multSum V n` is that object: the direct sum
`Etingof.FDRep.pi` (`Infrastructure/FDRepDirectSum`) of the family indexed by the sigma type
`(k : ι) × Fin (n k)`, i.e. `n k` copies of `V k` for each `k`.  Its character is
`Σ_k n k · χ_{V k}` (`character_multSum`), which is exactly the shape of the multiplicity
identities proved below, so `Etingof.charEq_iso` (Chapter 5, equal characters imply isomorphism
over `ℂ`) turns each of them into an isomorphism of representations (`iso_multSum_of_character`).

The isomorphisms are non-canonical — `charEq_iso` produces one from a character computation
without singling one out — so they are stated as `Nonempty (· ≅ ·)`, as elsewhere in the project
(`Etingof.Problem4_12_9.tensor_iso_Rz_mul`). -/

section MultSum

variable {G : Type} [Group G] [Finite G] {ι : Type} [Fintype ι]

/-- **The right-hand side of a multiplicity table entry**: the direct sum `⊕_k n k · V k`,
containing `n k` copies of `V k` for each `k`, realised as `Etingof.FDRep.pi` over the sigma
type `(k : ι) × Fin (n k)`. -/
def multSum (V : ι → FDRep ℂ G) (n : ι → ℕ) : FDRep ℂ G :=
  Etingof.FDRep.pi fun p : (k : ι) × Fin (n k) => V p.1

/-- **Character of `multSum`**: `χ_{⊕_k n k · V k} = Σ_k n k · χ_{V k}`.  Character additivity
over the direct sum (`Etingof.FDRep.character_pi`), with the sum over the sigma type unfolded
to a double sum. -/
theorem character_multSum (V : ι → FDRep ℂ G) (n : ι → ℕ) (g : G) :
    (multSum V n).character g = ∑ k, (n k : ℂ) * (V k).character g := by
  classical
  rw [multSum, Etingof.FDRep.character_pi, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- the summand `(V ⟨k, s⟩.1).character g` is `(V k).character g` by iota reduction, but not
  -- syntactically constant in `s`, so `Finset.sum_const` needs the reduced form first
  change ∑ _s : Fin (n k), (V k).character g = (n k : ℂ) * (V k).character g
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The bridge from a multiplicity identity to a decomposition of representations.**  If the
character of `W` is the tabulated combination `Σ_k n k · χ_{V k}`, then `W ≅ ⊕_k n k · V k`.
This is `Etingof.charEq_iso` ("equal characters imply isomorphism", Chapter 5) applied to
`character_multSum`. -/
theorem iso_multSum_of_character (V : ι → FDRep ℂ G) (n : ι → ℕ) (W : FDRep ℂ G)
    (h : ∀ g, W.character g = ∑ k, (n k : ℂ) * (V k).character g) :
    Nonempty (W ≅ multSum V n) :=
  Etingof.charEq_iso _ _ (funext fun g => by rw [character_multSum]; exact h g)

/-- `multSum V n` is the categorical biproduct of the family `(k, _) ↦ V k`
(`Etingof.FDRep.piIsoBiproduct`). -/
def multSumIsoBiproduct (V : ι → FDRep ℂ G) (n : ι → ℕ) :
    multSum V n ≅ ⨁ fun p : (k : ι) × Fin (n k) => V p.1 := by
  classical
  exact Etingof.FDRep.piIsoBiproduct _

end MultSum

/-- `S₃`, realised as the symmetric group on `Fin 3`. -/
abbrev S3 : Type := Equiv.Perm (Fin 3)

/-! ## The three irreducible representations of `S₃` (trace-based)

The construction mirrors the `S₃` catalogue used in Chapter 5
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
`χ_i(g) · χ_j(g) = Σ_k n_{ij}^k · χ_k(g)`.  Proved from the characters (traces) of the
three representations. -/
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

/-- **Tensor-product decomposition for `S₃`** phrased on `FDRep` tensor products:
`(V_i ⊗ V_j).character g = Σ_k n_{ij}^k · χ_k(g)`, i.e. the character form of
`V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k`.  (Etingof Example 4.9.1) -/
theorem S3_tensor_product_character (i j : Fin 3) (g : S3) :
    (irrep i ⊗ irrep j).character g = ∑ k, (nS3 i j k : ℂ) * (irrep k).character g := by
  rw [FDRep.char_tensor, Pi.mul_apply]
  exact S3_tensor_character i j g

/-- **Tensor-product decomposition for `S₃`, as an isomorphism of representations**
(Etingof Example 4.9.1).  Every entry of the book's `S₃` table holds at the level of
representations, not merely characters: `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` in `FDRep ℂ S₃`.
The character identity `S3_tensor_product_character` is the computation this rests on. -/
theorem S3_tensor_iso (i j : Fin 3) :
    Nonempty ((irrep i ⊗ irrep j : FDRep ℂ S3) ≅ multSum irrep (nS3 i j)) :=
  iso_multSum_of_character irrep (nS3 i j) _ (S3_tensor_product_character i j)

/-- `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` for `S₃`, stated with the categorical biproduct. -/
theorem S3_tensor_iso_biproduct (i j : Fin 3) :
    Nonempty ((irrep i ⊗ irrep j : FDRep ℂ S3) ≅
      ⨁ fun p : (k : Fin 3) × Fin (nS3 i j k) => irrep p.1) :=
  (S3_tensor_iso i j).map fun e => e ≪≫ multSumIsoBiproduct irrep (nS3 i j)

/-- **`ℂ² ⊗ ℂ² ≅ ℂ₊ ⊕ ℂ₋ ⊕ ℂ²`**, the one nontrivial entry of Etingof's `S₃` table, in the
book's own form: each of the three irreducibles occurs exactly once, so the right-hand side is
the plain direct sum of the catalogue `irrep`. -/
theorem stdRep_tensor_stdRep_iso :
    Nonempty ((stdRep ⊗ stdRep : FDRep ℂ S3) ≅ Etingof.FDRep.pi irrep) := by
  have hone : ∀ k, nS3 2 2 k = 1 := by decide
  refine Etingof.charEq_iso _ _ (funext fun g => ?_)
  rw [Etingof.FDRep.character_pi]
  refine (S3_tensor_product_character 2 2 g).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [hone k, Nat.cast_one, one_mul]

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

/-! ## The tensor-product multiplicity table of `A₅`

The irreducible catalogue of `A₅ = alternatingGroup (Fin 5)` is built in `Example4_8_1`
as `Etingof.Example4_8_1.A5.irrepA5 = ![repTriv, repC3plus, repC3minus, repC4, repC5]`, indexed
`0..4` as `ℂ, ℂ³₊, ℂ³₋, ℂ⁴, ℂ⁵`, matching the five rows of the character table `chiA5` over
`ℚ(√5)`.  We reuse it verbatim, exactly as the `S₃` table above uses its own catalogue.

The multiplicity identity is proved over `ℚ(√5)` (`Etingof.Example4_8_1.Q5`), where the `√5²`
relation is baked into the ring multiplication, so the `5·5·5` class-by-class check is pure
rational arithmetic (`nA5_char_Q5`, no `√5` reasoning).  It is transported to `ℂ` through the
ring-homomorphism properties of `Q5toC` (`Q5toC_mul`, `Q5toC_add`), and lifted from the five
conjugacy classes to every group element because characters are class functions
(`irrepA5_char_eq`). -/

section A5
open Etingof.Example4_8_1 Etingof.Example4_8_1.A5

/-- Tensor-product multiplicity table of `A₅`, read off Etingof's `A₅` table in Example 4.9.1.
`nA5 i j k` is the multiplicity of the `k`-th irreducible `irrepA5 k` in `irrepA5 i ⊗ irrepA5 j`
(indices `0..4 = ℂ, ℂ³₊, ℂ³₋, ℂ⁴, ℂ⁵`).  Note the multiplicity-2 constituents in
`ℂ⁴ ⊗ ℂ⁵ = ℂ³₊ ⊕ ℂ³₋ ⊕ 2ℂ⁵ ⊕ ℂ⁴` and `ℂ⁵ ⊗ ℂ⁵ = ℂ ⊕ ℂ³₊ ⊕ ℂ³₋ ⊕ 2ℂ⁴ ⊕ 2ℂ⁵`. -/
def nA5 : Fin 5 → Fin 5 → Fin 5 → ℕ :=
  ![![![1,0,0,0,0], ![0,1,0,0,0], ![0,0,1,0,0], ![0,0,0,1,0], ![0,0,0,0,1]],
    ![![0,1,0,0,0], ![1,1,0,0,1], ![0,0,0,1,1], ![0,0,1,1,1], ![0,1,1,1,1]],
    ![![0,0,1,0,0], ![0,0,0,1,1], ![1,0,1,0,1], ![0,1,0,1,1], ![0,1,1,1,1]],
    ![![0,0,0,1,0], ![0,0,1,1,1], ![0,1,0,1,1], ![1,1,1,1,1], ![0,1,1,1,2]],
    ![![0,0,0,0,1], ![0,1,1,1,1], ![0,1,1,1,1], ![0,1,1,1,2], ![1,1,1,2,2]]]

/-- Each `A₅` character is a class function: `χ_i(g)` equals the tabulated `ℚ(√5)` value
`chiA5 i (classIdxA5 g)` at the conjugacy class of `g`.  Combines `classIdxA5_spec` (every `g`
is conjugate to its class representative) with `FDRep.char_conj` and the class-representative
character values `irrepA5_character_book`. -/
lemma irrepA5_char_eq (i : Fin 5) (g : A5.G) :
    (A5.irrepA5 i).character g = Q5toC (chiA5 i (A5.classIdxA5 g)) := by
  obtain ⟨c, hc⟩ := A5.classIdxA5_spec g
  have key : (A5.irrepA5 i).character g
      = (A5.irrepA5 i).character (A5.classRepA5 (A5.classIdxA5 g)) := by
    rw [← FDRep.char_conj (A5.irrepA5 i) (A5.classRepA5 (A5.classIdxA5 g)) c, hc]
  rw [key]
  simpa only [A5.rowA5, id_eq] using A5.irrepA5_character_book i (A5.classIdxA5 g)

/-- `n : ℕ` as an element of `ℚ(√5)`, with zero `√5`-part. -/
def q5Nat (n : ℕ) : Q5 := ⟨(n : ℚ), 0⟩

/-- `Q5toC` sends the rational element `q5Nat n` to the complex number `n`. -/
lemma Q5toC_q5Nat (n : ℕ) : Q5toC (q5Nat n) = (n : ℂ) := by
  simp [Q5toC, q5Nat]

/-- `Q5toC : ℚ(√5) → ℂ` is multiplicative.  The `ℚ(√5)`-multiplication bakes in `√5² = 5`, so
the two sides differ only by the `√5²` term, discharged by `sqrt5_sq`. -/
lemma Q5toC_mul (a b : Q5) : Q5toC (a * b) = Q5toC a * Q5toC b := by
  have hs := A5.sqrt5_sq
  simp only [Q5toC, Q5.mul_re, Q5.mul_im]
  push_cast
  linear_combination (-((a.im : ℂ) * (b.im : ℂ))) * hs

-- the `5·5·5 = 125`-way `fin_cases` split needs a raised heartbeat budget; each case is
-- closed by rational `norm_num` on the `re`/`im` components
set_option maxHeartbeats 2000000 in
/-- The tabulated multiplicity identity, computed entirely in `ℚ(√5)`:
`χ_i(j) · χ_{i'}(j) = Σ_k n_{ii'}^k · χ_k(j)` at each of the five conjugacy classes `j`.  Because
the `ℚ(√5)`-product already incorporates `√5² = 5`, this is a `5·5·5` case split closed by pure
rational `norm_num` on the `re`/`im` components, with no `√5` reasoning and no `ℂ` arithmetic. -/
lemma nA5_char_Q5 (i i' j : Fin 5) :
    chiA5 i j * chiA5 i' j
      = q5Nat (nA5 i i' 0) * chiA5 0 j + q5Nat (nA5 i i' 1) * chiA5 1 j
        + q5Nat (nA5 i i' 2) * chiA5 2 j + q5Nat (nA5 i i' 3) * chiA5 3 j
        + q5Nat (nA5 i i' 4) * chiA5 4 j := by
  fin_cases i <;> fin_cases i' <;> fin_cases j <;>
    apply Q5.ext <;>
    norm_num [nA5, chiA5, q5Nat, Q5.mul_re, Q5.mul_im, Q5.add_re, Q5.add_im,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Q5.mk_re, Q5.mk_im, Q5.one_re, Q5.one_im, Q5.zero_re, Q5.zero_im,
      Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im]

/-- The tabulated multiplicity identity `χ_i(j) · χ_{i'}(j) = Σ_k n_{ii'}^k · χ_k(j)`, transported
from `ℚ(√5)` (`nA5_char_Q5`) to `ℂ` via the ring-homomorphism properties of `Q5toC`. -/
lemma nA5_char (i i' j : Fin 5) :
    Q5toC (chiA5 i j) * Q5toC (chiA5 i' j)
      = ∑ k, (nA5 i i' k : ℂ) * Q5toC (chiA5 k j) := by
  rw [← Q5toC_mul, nA5_char_Q5, Fin.sum_univ_five]
  simp only [Q5toC_add, Q5toC_mul, Q5toC_q5Nat]

/-- **Tensor-product multiplicity identity for `A₅`** (Etingof Example 4.9.1).  For every group
element `g` and all `i, j`, the product of the two irreducible characters decomposes as the
tabulated integer combination of irreducible characters:
`χ_i(g) · χ_j(g) = Σ_k n_{ij}^k · χ_k(g)`.  Proved from the characters (traces) of the
five representations of `A₅`. -/
theorem A5_tensor_character (i j : Fin 5) (g : A5.G) :
    (A5.irrepA5 i).character g * (A5.irrepA5 j).character g
      = ∑ k, (nA5 i j k : ℂ) * (A5.irrepA5 k).character g := by
  simp only [irrepA5_char_eq]
  exact nA5_char i j (A5.classIdxA5 g)

/-- **Tensor-product decomposition for `A₅`** phrased on `FDRep` tensor products:
`(V_i ⊗ V_j).character g = Σ_k n_{ij}^k · χ_k(g)`, i.e. the character form of
`V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k`.  (Etingof Example 4.9.1) -/
theorem A5_tensor_product_character (i j : Fin 5) (g : A5.G) :
    (A5.irrepA5 i ⊗ A5.irrepA5 j).character g
      = ∑ k, (nA5 i j k : ℂ) * (A5.irrepA5 k).character g := by
  rw [FDRep.char_tensor, Pi.mul_apply]
  exact A5_tensor_character i j g

/-- **Tensor-product decomposition for `A₅`, as an isomorphism of representations**
(Etingof Example 4.9.1).  Every entry of the book's `A₅` table holds at the level of
representations, not merely characters: `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` in `FDRep ℂ A₅`,
including the multiplicity-2 constituents of `ℂ⁴ ⊗ ℂ⁵` and `ℂ⁵ ⊗ ℂ⁵`. -/
theorem A5_tensor_iso (i j : Fin 5) :
    Nonempty ((A5.irrepA5 i ⊗ A5.irrepA5 j : FDRep ℂ A5.G) ≅
      multSum A5.irrepA5 (nA5 i j)) :=
  iso_multSum_of_character A5.irrepA5 (nA5 i j) _ (A5_tensor_product_character i j)

/-- `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` for `A₅`, stated with the categorical biproduct. -/
theorem A5_tensor_iso_biproduct (i j : Fin 5) :
    Nonempty ((A5.irrepA5 i ⊗ A5.irrepA5 j : FDRep ℂ A5.G) ≅
      ⨁ fun p : (k : Fin 5) × Fin (nA5 i j k) => A5.irrepA5 p.1) :=
  (A5_tensor_iso i j).map fun e => e ≪≫ multSumIsoBiproduct A5.irrepA5 (nA5 i j)

/-- `A₅` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the trivial `ℂ`, the two icosahedral `ℂ³₊, ℂ³₋`, and the permutation reps `ℂ⁴, ℂ⁵`).
(Etingof Example 4.9.1) -/
theorem A5_conj_classes :
    Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5 :=
  Etingof.Example4_8_1_A5_conj_classes

end A5

/-! ## The tensor-product multiplicity table of `S₄`

The irreducible catalogue of `S₄ = Equiv.Perm (Fin 4)` is built in `Example4_8_1` as
`Etingof.Example4_8_1.S4.irrepS4 = ![trivRepS4, signRepS4, repC2, repStdPlus, repStd]`, indexed
`0..4` as `ℂ₊, ℂ₋, ℂ², ℂ³₊, ℂ³₋`, matching the five rows of the integer character table `tbl`.
We reuse it verbatim, exactly as the `S₃` and `A₅` tables above use their own catalogues.

Unlike `A₅`, every `S₄` character value is a rational integer (`tbl`), so the multiplicity
identity is pure integer arithmetic, with no `√5`.  As for `A₅`, the identity for every group
element reduces to the five conjugacy classes because characters are class functions
(`irrepS4_char_eq`), and there it is the tabulated integer `5·5·5` case split (`nS4_char_int`). -/

section S4
open Etingof.Example4_8_1 Etingof.Example4_8_1.S4

/-- Tensor-product multiplicity table of `S₄`, read off Etingof's `S₄` table in Example 4.9.1.
`nS4 i j k` is the multiplicity of the `k`-th irreducible `irrepS4 k` in `irrepS4 i ⊗ irrepS4 j`
(indices `0..4 = ℂ₊, ℂ₋, ℂ², ℂ³₊, ℂ³₋`).  For instance
`ℂ³₊ ⊗ ℂ³₊ = ℂ₊ ⊕ ℂ² ⊕ ℂ³₊ ⊕ ℂ³₋` and `ℂ³₊ ⊗ ℂ³₋ = ℂ₋ ⊕ ℂ² ⊕ ℂ³₊ ⊕ ℂ³₋`. -/
def nS4 : Fin 5 → Fin 5 → Fin 5 → ℕ :=
  ![![![1,0,0,0,0], ![0,1,0,0,0], ![0,0,1,0,0], ![0,0,0,1,0], ![0,0,0,0,1]],
    ![![0,1,0,0,0], ![1,0,0,0,0], ![0,0,1,0,0], ![0,0,0,0,1], ![0,0,0,1,0]],
    ![![0,0,1,0,0], ![0,0,1,0,0], ![1,1,1,0,0], ![0,0,0,1,1], ![0,0,0,1,1]],
    ![![0,0,0,1,0], ![0,0,0,0,1], ![0,0,0,1,1], ![1,0,1,1,1], ![0,1,1,1,1]],
    ![![0,0,0,0,1], ![0,0,0,1,0], ![0,0,0,1,1], ![0,1,1,1,1], ![1,0,1,1,1]]]

/-- The index (in `Fin 5`) of the conjugacy class of `g : S₄`, matching the columns of `tbl`
(`Id, (12), (12)(34), (123), (1234)`).  The identity, transpositions and 3-cycles are recognised
by their `4, 2, 1` fixed points on `Fin 4`; the two fixed-point-free classes are told apart by the
sign (`+1` for the even double transpositions, `−1` for the odd 4-cycles). -/
def classIdxS4 (g : S4) : Fin 5 :=
  if fixCardM (G := S4) (α := Fin 4) g = 4 then 0
  else if fixCardM (G := S4) (α := Fin 4) g = 2 then 1
  else if fixCardM (G := S4) (α := Fin 4) g = 1 then 3
  else if Equiv.Perm.sign g = 1 then 2
  else 4

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- `decide` over the 24 elements of `S₄`, with a conjugacy search per element
/-- Every `g : S₄` is conjugate to its class representative `classRepS4 (classIdxS4 g)`. -/
lemma classIdxS4_spec (g : S4) : ∃ c : S4, c * classRepS4 (classIdxS4 g) * c⁻¹ = g := by
  revert g; decide

/-- Each `S₄` character is a class function: `χ_i(g)` equals the tabulated integer value
`tbl i (classIdxS4 g)` at the conjugacy class of `g`.  Combines `classIdxS4_spec` with
`FDRep.char_conj` and the class-representative character values `irrepS4_character`. -/
lemma irrepS4_char_eq (i : Fin 5) (g : S4) :
    (irrepS4 i).character g = (tbl i (classIdxS4 g) : ℂ) := by
  obtain ⟨c, hc⟩ := classIdxS4_spec g
  have key : (irrepS4 i).character g
      = (irrepS4 i).character (classRepS4 (classIdxS4 g)) := by
    rw [← FDRep.char_conj (irrepS4 i) (classRepS4 (classIdxS4 g)) c, hc]
  rw [key, irrepS4_character]

/-- The tabulated multiplicity identity `χ_i(c) · χ_{i'}(c) = Σ_k n_{ii'}^k · χ_k(c)` at each of
the five conjugacy classes `c`, computed with the integer table `tbl`: a pure integer `5·5·5`
case split closed by `decide`. -/
lemma nS4_char_int (i i' c : Fin 5) :
    tbl i c * tbl i' c
      = (nS4 i i' 0 : ℤ) * tbl 0 c + (nS4 i i' 1 : ℤ) * tbl 1 c + (nS4 i i' 2 : ℤ) * tbl 2 c
        + (nS4 i i' 3 : ℤ) * tbl 3 c + (nS4 i i' 4 : ℤ) * tbl 4 c := by
  fin_cases i <;> fin_cases i' <;> fin_cases c <;> decide

/-- **Tensor-product multiplicity identity for `S₄`** (Etingof Example 4.9.1).  For every group
element `g` and all `i, j`, the product of the two irreducible characters decomposes as the
tabulated integer combination of irreducible characters:
`χ_i(g) · χ_j(g) = Σ_k n_{ij}^k · χ_k(g)`.  Proved from the characters (traces) of the
five representations of `S₄`. -/
theorem S4_tensor_character (i j : Fin 5) (g : S4) :
    (irrepS4 i).character g * (irrepS4 j).character g
      = ∑ k, (nS4 i j k : ℂ) * (irrepS4 k).character g := by
  simp only [irrepS4_char_eq, Fin.sum_univ_five]
  have hc := congrArg (fun z : ℤ => (z : ℂ)) (nS4_char_int i j (classIdxS4 g))
  push_cast at hc ⊢
  linear_combination hc

/-- **Tensor-product decomposition for `S₄`** phrased on `FDRep` tensor products:
`(V_i ⊗ V_j).character g = Σ_k n_{ij}^k · χ_k(g)`, i.e. the character form of
`V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k`.  (Etingof Example 4.9.1) -/
theorem S4_tensor_product_character (i j : Fin 5) (g : S4) :
    (irrepS4 i ⊗ irrepS4 j).character g
      = ∑ k, (nS4 i j k : ℂ) * (irrepS4 k).character g := by
  rw [FDRep.char_tensor, Pi.mul_apply]
  exact S4_tensor_character i j g

/-- **Tensor-product decomposition for `S₄`, as an isomorphism of representations**
(Etingof Example 4.9.1).  Every entry of the book's `S₄` table holds at the level of
representations, not merely characters: `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` in `FDRep ℂ S₄`. -/
theorem S4_tensor_iso (i j : Fin 5) :
    Nonempty ((irrepS4 i ⊗ irrepS4 j : FDRep ℂ S4) ≅ multSum irrepS4 (nS4 i j)) :=
  iso_multSum_of_character irrepS4 (nS4 i j) _ (S4_tensor_product_character i j)

/-- `V_i ⊗ V_j ≅ ⊕_k n_{ij}^k V_k` for `S₄`, stated with the categorical biproduct. -/
theorem S4_tensor_iso_biproduct (i j : Fin 5) :
    Nonempty ((irrepS4 i ⊗ irrepS4 j : FDRep ℂ S4) ≅
      ⨁ fun p : (k : Fin 5) × Fin (nS4 i j k) => irrepS4 p.1) :=
  (S4_tensor_iso i j).map fun e => e ≪≫ multSumIsoBiproduct irrepS4 (nS4 i j)

/-- `S₄` has exactly 5 conjugacy classes, hence 5 irreducible representations
(the trivial `ℂ₊`, sign `ℂ₋`, standard `ℂ²`, and the two 3-dimensionals `ℂ³₊, ℂ³₋`).
(Etingof Example 4.9.1) -/
theorem S4_conj_classes :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 4))) = 5 :=
  Etingof.Example4_8_1_S4_conj_classes

end S4

end Etingof.Example4_9_1

end

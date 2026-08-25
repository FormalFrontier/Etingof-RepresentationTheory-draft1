import Mathlib
import EtingofRepresentationTheory.Chapter6.Problem6_1_3_continued_tildeE
import EtingofRepresentationTheory.Chapter6.DimDvdCard
import EtingofRepresentationTheory.Chapter4.Theorem4_2_1
import EtingofRepresentationTheory.Chapter4.Discussion_4_4
import EtingofRepresentationTheory.Chapter5.AbelianFDRep

/-!
# Problem 6.1.6: The McKay graph of a finite subgroup of `SU(2)`

> Let `G ≠ {1}` be a finite subgroup of `SU(2)` and let `V` be the
> `2`-dimensional representation of `G` coming from its embedding into `SU(2)`.
> Let `Vᵢ`, `i ∈ I`, be all the irreducible representations of `G`. Let `rᵢⱼ` be
> the multiplicity of `Vᵢ` in `V ⊗ Vⱼ`.
>
> **(a)** Show that `rᵢⱼ = rⱼᵢ`.
>
> **(b)** The **McKay graph** `M(G)` has vertices `i ∈ I`, with `i` joined to `j`
> by `rᵢⱼ` edges. Show that `M(G)` is connected. (Use Problem 4.12.10.)
>
> **(c)** Show that `M(G)` is an **affine Dynkin diagram**: the matrix
> `aᵢⱼ = 2δᵢⱼ - rᵢⱼ` is positive semidefinite but not definite. (Use 6.1.3.)
>
> **(d)** Which groups from Problem 4.12.8 correspond to which diagrams?
>
> **(e)** Using the McKay graph, the dimensions of the irreducible
> representations are the numbers labeling the vertices of the affine Dynkin
> diagrams (the marks).

## Formalization notes

`SU(2)` is `Matrix.specialUnitaryGroup (Fin 2) ℂ`. The `2`-dimensional
representation `V` is the tautological action of `G ≤ SU(2)` on `ℂ² = Fin 2 → ℂ`
by matrix multiplication. The irreducibles are given as a finite family
`W : Fin m → FDRep ℂ G` (all simple, pairwise non-isomorphic, exhaustive). The
multiplicity `rᵢⱼ = dim Hom(Wᵢ, V ⊗ Wⱼ)` (Schur's lemma), and the affine Cartan
matrix reuses `Etingof.Problem6_1_3_tildeE.IsAffineDynkinDiagram`.

Parts (a), (b), and the affine-Cartan argument in (c) for graphs with at least
three vertices are proved below, as is the kernel equation underlying (e). The
two-vertex double-edge `Ã₁` case, the family-by-family correspondence in (d),
and the explicit normalized marks remaining in (e) are intentionally omitted by
the project-wide scope decision in `skipped-exercises.md`. They are documented
omissions, not placeholder declarations.
-/

namespace Etingof.Problem6_1_6

open Matrix CategoryTheory MonoidalCategory Module

/-- The tautological `2`-dimensional representation of `G ≤ SU(2)` on `ℂ²`:
`g` acts by matrix multiplication `v ↦ (g : Matrix).mulVec v`. -/
noncomputable def tautRep (G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) :
    Representation ℂ G (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    simp only [OneMemClass.coe_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    simp only [Submonoid.coe_mul, Subgroup.coe_mul, Matrix.toLin'_mul]; rfl

/-- The `2`-dimensional representation `V` of `G` as an `FDRep`. -/
noncomputable def V (G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) : FDRep ℂ G :=
  FDRep.of (tautRep G)

variable {G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} [Finite G]
  {m : ℕ} (W : Fin m → FDRep ℂ G)

/-- `W` is a **complete list of irreducibles**: each `W i` is simple, the `W i`
are pairwise non-isomorphic, and every simple `FDRep` is isomorphic to some
`W i`. -/
structure IsCompleteIrreps : Prop where
  simple : ∀ i, Simple (W i)
  distinct : ∀ i j, Nonempty (W i ≅ W j) → i = j
  exhaustive : ∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ W i)

/-- The multiplicity `rᵢⱼ` of `Wᵢ` in `V ⊗ Wⱼ`, computed as
`dim Hom(Wᵢ, V ⊗ Wⱼ)` (Schur's lemma). -/
noncomputable def mult (i j : Fin m) : ℕ := finrank ℂ (W i ⟶ V G ⊗ W j)

/-- The McKay adjacency matrix `rᵢⱼ` (as an integer matrix). -/
noncomputable def mckayAdj (i j : Fin m) : ℤ := (mult W i j : ℤ)

/-- The affine Cartan matrix `aᵢⱼ = 2δᵢⱼ - rᵢⱼ` of the McKay graph. -/
noncomputable def mckayCartan (i j : Fin m) : ℤ :=
  2 * (if i = j then 1 else 0) - mult W i j

/-! ## Part (a): symmetry of the multiplicities -/

omit [Finite G] in
/-- The character of the tautological representation is the matrix trace of the
`SU(2)`-element. -/
lemma charV_eq (g : G) :
    (V G).character g =
      Matrix.trace ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [FDRep.character, V, FDRep.of_ρ']
  exact Matrix.trace_toLin'_eq _

omit [Finite G] in
/-- **Reality/self-duality of `χ_V`.** For `g ∈ SU(2)` the trace is invariant
under inversion: `χ_V(g⁻¹) = χ_V(g)`. This holds because for a `2×2` matrix `A`
of determinant `1` one has `A⁻¹ = adj A`, and `tr (adj A) = tr A`. -/
lemma charV_inv (g : G) : (V G).character g⁻¹ = (V G).character g := by
  rw [charV_eq, charV_eq]
  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA
  set B : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g⁻¹.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hB
  -- `B` is a left inverse of `A` (group law pushed to matrices).
  have hBA : B * A = 1 := by
    rw [hB, hA, ← MulMemClass.coe_mul, ← MulMemClass.coe_mul, inv_mul_cancel]
    rfl
  -- `det A = 1` from `SU(2)`-membership.
  have hdet : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).2
  -- Hence `B = A⁻¹ = adj A`, whose trace equals `tr A`.
  have hBinv : B = A⁻¹ := (Matrix.inv_eq_left_inv hBA).symm
  rw [hBinv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two,
    Matrix.trace_fin_two_of, Matrix.trace_fin_two]
  ring

/-- **Reality of `χ_V`.** For `g ∈ SU(2)` the character value `χ_V(g)` is fixed by complex
conjugation: `conj (χ_V g) = χ_V g`. Combines `Etingof.char_inv_eq_conj`
(`χ_V(g⁻¹) = conj(χ_V g)`) with the self-duality `charV_inv` (`χ_V(g⁻¹) = χ_V g`). -/
lemma charV_conj (g : G) :
    (starRingEnd ℂ) ((V G).character g) = (V G).character g := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [← Etingof.char_inv_eq_conj, charV_inv]

/-- The imaginary part of `χ_V(g)` vanishes: `χ_V(g)` is a real number. -/
lemma charV_im_zero (g : G) : ((V G).character g).im = 0 :=
  Complex.conj_eq_iff_im.mp (charV_conj g)

omit [Finite G] in
/-- **The `SU(2)` trace bound.** For `g ∈ SU(2)` the real part of `χ_V(g) = tr(g)` is at most `2`.
Each diagonal entry of the unitary matrix `g` has modulus `≤ 1` (its column has unit norm), so its
real part is `≤ 1`, and the trace is the sum of the two diagonal entries. -/
lemma charV_re_le_two (g : G) : ((V G).character g).re ≤ 2 := by
  classical
  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA
  -- `A` is unitary, hence `star A * A = 1`
  have hu : A ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).1
  have hstar : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  -- each diagonal entry has real part `≤ 1`
  have hdiag : ∀ i : Fin 2, (A i i).re ≤ 1 := by
    intro i
    -- column `i` has unit norm: `∑ₖ |A k i|² = 1`
    have hsum : ∑ k : Fin 2, Complex.normSq (A k i) = 1 := by
      have hii : (star A * A) i i = 1 := by rw [hstar, Matrix.one_apply_eq]
      rw [Matrix.mul_apply] at hii
      have hterm : ∀ k : Fin 2, (star A) i k * A k i
          = ((Complex.normSq (A k i) : ℝ) : ℂ) := by
        intro k
        rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
      rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Complex.ofReal_sum] at hii
      exact_mod_cast hii
    have hle : Complex.normSq (A i i) ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun k => Complex.normSq (A k i))
        (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    have hre2 : (A i i).re * (A i i).re ≤ 1 := by
      have hns := Complex.normSq_apply (A i i)
      nlinarith [mul_self_nonneg (A i i).im, hle, hns]
    nlinarith [hre2]
  -- `χ_V(g) = tr A = A 0 0 + A 1 1`
  have htr : (V G).character g = A 0 0 + A 1 1 := by
    rw [charV_eq, ← hA, Matrix.trace_fin_two]
  rw [htr, Complex.add_re]
  linarith [hdiag 0, hdiag 1]

/-- **(a)** `rᵢⱼ = rⱼᵢ`. (Because `V` is self-dual: `V ≅ V*` as `V` is the
`2`-dimensional `SU(2)`-representation, so `dim Hom(Wᵢ, V ⊗ Wⱼ) =
dim Hom(Wⱼ, V ⊗ Wᵢ)`.) -/
theorem mult_symm (_hW : IsCompleteIrreps W) (i j : Fin m) :
    mult W i j = mult W j i := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have h1 := FDRep.scalar_product_char_eq_finrank_equivariant_fintype (V G ⊗ W j) (W i)
  have h2 := FDRep.scalar_product_char_eq_finrank_equivariant_fintype (V G ⊗ W i) (W j)
  have hC : (mult W i j : ℂ) = (mult W j i : ℂ) := by
    simp only [mult]
    rw [← h1, ← h2]
    congr 1
    simp only [FDRep.char_tensor, Pi.mul_apply]
    rw [← Equiv.sum_comp (Equiv.inv G)
      (fun g => (V G).character g * (W i).character g * (W j).character g⁻¹)]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    simp only [Equiv.inv_apply, inv_inv]
    rw [charV_inv]
    ring
  exact_mod_cast hC

/-! ## Complete reducibility: dimension count over a complete irreducible list -/

/-- **Character decomposition (complete reducibility over `ℂ`).** The character of
any `S : FDRep ℂ G` is the `ℂ`-linear combination of the irreducible characters
with the `Hom`-multiplicities `finrank (Wⱼ ⟶ S)` as coefficients. The difference
`χ_S - ∑ⱼ mⱼ χ_{Wⱼ}` is a class function orthogonal to every simple character, so
it vanishes by character completeness (`classFunction_eq_zero_of_orthogonal_simples`). -/
lemma char_eq_sum_mult (hW : IsCompleteIrreps W) (S : FDRep ℂ G) :
    S.character = ∑ j, (finrank ℂ (W j ⟶ S) : ℂ) • (W j).character := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hzero : S.character - ∑ j, (finrank ℂ (W j ⟶ S) : ℂ) • (W j).character = 0 := by
    apply Etingof.classFunction_eq_zero_of_orthogonal_simples
    · -- the difference is a class function
      intro g h
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FDRep.char_conj]
    · -- orthogonal to every simple character
      intro V' _
      obtain ⟨k, ⟨isok⟩⟩ := hW.exhaustive V' ‹Simple V'›
      haveI : Simple (W k) := hW.simple k
      rw [FDRep.char_iso isok]
      -- expand the difference termwise
      have step : ∀ g : G,
          (S.character - ∑ j, (finrank ℂ (W j ⟶ S) : ℂ) • (W j).character) g
              * (W k).character g⁻¹
            = S.character g * (W k).character g⁻¹
              - ∑ j, (finrank ℂ (W j ⟶ S) : ℂ)
                  * ((W j).character g * (W k).character g⁻¹) := by
        intro g
        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
          Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [Finset.sum_congr rfl (fun g _ => step g), Finset.sum_sub_distrib, Finset.sum_comm]
      -- LHS scalar product: `∑_g χ_S χ_{Wₖ}(·⁻¹) = |G| · mₖ`
      have hL : ∑ g : G, S.character g * (W k).character g⁻¹
          = (Fintype.card G : ℂ) * (finrank ℂ (W k ⟶ S) : ℂ) := by
        have h := FDRep.scalar_product_char_eq_finrank_equivariant_fintype S (W k)
        rw [smul_eq_mul] at h
        rw [← h, ← mul_assoc, mul_invOf_self, one_mul]
      -- orthogonality of irreducible characters
      have hO : ∀ j : Fin m, ∑ g : G, (W j).character g * (W k).character g⁻¹
          = (Fintype.card G : ℂ) * (if j = k then 1 else 0) := by
        intro j
        haveI : Simple (W j) := hW.simple j
        have h := FDRep.char_orthonormal_fintype (W j) (W k)
        rw [smul_eq_mul] at h
        -- collapse the `Nonempty (Wⱼ ≅ Wₖ)` condition to `j = k`
        have hval : ⅟(Fintype.card G : ℂ) * ∑ g : G, (W j).character g * (W k).character g⁻¹
            = (if j = k then (1 : ℂ) else 0) := by
          rw [h]
          by_cases hjk : j = k
          · rw [if_pos (⟨eqToIso (congrArg W hjk)⟩ : Nonempty (W j ≅ W k)), if_pos hjk]
          · rw [if_neg (fun hh => hjk (hW.distinct j k hh)), if_neg hjk]
        calc ∑ g : G, (W j).character g * (W k).character g⁻¹
            = (Fintype.card G : ℂ)
                * (⅟(Fintype.card G : ℂ) * ∑ g : G, (W j).character g * (W k).character g⁻¹) := by
              rw [← mul_assoc, mul_invOf_self, one_mul]
          _ = (Fintype.card G : ℂ) * (if j = k then 1 else 0) := by rw [hval]
      -- assemble both sides
      simp_rw [← Finset.mul_sum, hO]
      rw [hL]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ k
        (fun j => (finrank ℂ (W j ⟶ S) : ℂ) * (Fintype.card G : ℂ))]
      rw [if_pos (Finset.mem_univ k)]
      ring
  exact sub_eq_zero.mp hzero

/-- **Dimension count.** For a complete list of irreducibles `W`, the dimension of
any `S : FDRep ℂ G` is `∑ⱼ (finrank Hom(Wⱼ, S)) · dim Wⱼ`. Obtained from
`char_eq_sum_mult` by evaluating characters at `1 ∈ G`. -/
lemma finrank_eq_sum_mult (hW : IsCompleteIrreps W) (S : FDRep ℂ G) :
    (finrank ℂ S : ℤ) = ∑ j, (finrank ℂ (W j ⟶ S) : ℤ) * (finrank ℂ (W j) : ℤ) := by
  have h1 := congrFun (char_eq_sum_mult W hW S) (1 : G)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FDRep.char_one] at h1
  exact_mod_cast h1

/-- **Marks identity (part (e), auxiliary).** The dimension vector `dⱼ = dim Wⱼ`
lies in the kernel of the McKay Cartan matrix: `∑ⱼ (2δᵢⱼ - rᵢⱼ) dⱼ = 0`. This is
the dimension count `dim(V ⊗ Wᵢ) = 2 dim Wᵢ` combined with `rᵢⱼ = rⱼᵢ`. Stated
early so both part (e) and the "not positive definite" half of part (c) can use it. -/
lemma mckay_marks_aux (hW : IsCompleteIrreps W) (i : Fin m) :
    (∑ j, mckayCartan W i j * (finrank ℂ (W j) : ℤ)) = 0 := by
  classical
  -- `∑ⱼ rᵢⱼ dⱼ = dim(V ⊗ Wᵢ) = 2 dim Wᵢ`
  have key : (∑ j, (mult W i j : ℤ) * (finrank ℂ (W j) : ℤ)) = 2 * (finrank ℂ (W i) : ℤ) := by
    set S : FDRep ℂ G := V G ⊗ W i with hS
    have hswap : (∑ j, (mult W i j : ℤ) * (finrank ℂ (W j) : ℤ))
        = ∑ j, (mult W j i : ℤ) * (finrank ℂ (W j) : ℤ) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mult_symm W hW i j]
    have hcount : (∑ j, (mult W j i : ℤ) * (finrank ℂ (W j) : ℤ)) = (finrank ℂ S : ℤ) := by
      rw [finrank_eq_sum_mult W hW S]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rfl
    rw [hswap, hcount]
    -- `dim(V ⊗ Wᵢ) = 2 · dim Wᵢ` from characters at `1`
    have htensor : (finrank ℂ S : ℂ) = 2 * (finrank ℂ (W i) : ℂ) := by
      have e1 : S.character 1 = (finrank ℂ S : ℂ) := FDRep.char_one _
      have e3 : (W i).character 1 = (finrank ℂ (W i) : ℂ) := FDRep.char_one _
      have e2 : (V G).character 1 = 2 := by
        rw [charV_eq]
        have hone : (((1 : G).val : specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
        rw [hone, Matrix.trace_one]; simp
      have h1 := congrFun (FDRep.char_tensor (V G) (W i)) (1 : G)
      rw [Pi.mul_apply, e2, e3] at h1
      rw [← e1, hS]; exact h1
    exact_mod_cast htensor
  -- expand `mckayCartan` and reduce to `key`
  have expand : ∀ j, mckayCartan W i j * (finrank ℂ (W j) : ℤ)
      = (if i = j then 2 * (finrank ℂ (W j) : ℤ) else 0)
        - (mult W i j : ℤ) * (finrank ℂ (W j) : ℤ) := by
    intro j
    simp only [mckayCartan]
    split_ifs with h <;> ring
  rw [Finset.sum_congr rfl (fun j _ => expand j), Finset.sum_sub_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => 2 * (finrank ℂ (W j) : ℤ)),
    if_pos (Finset.mem_univ i), key]
  ring

/-! ## Part (b): the McKay graph is connected -/

/-- The McKay adjacency relation on vertices: at least one edge `i → j`
(`rᵢⱼ ≥ 1`). -/
def McKayAdj (i j : Fin m) : Prop := 1 ≤ mult W i j

/-- `McKayJoined i j`: there is a walk in the McKay graph from `i` to `j`, i.e. a
list of vertices starting at `i`, ending at `j`, whose consecutive entries are
joined by an edge (`IsChain` of `McKayAdj`). -/
def McKayJoined (i j : Fin m) : Prop :=
  ∃ p : List (Fin m), p.head? = some i ∧ p.getLast? = some j ∧ p.IsChain (McKayAdj W)

variable {W}

omit [Finite G] in
/-- The trivial walk `[i]` joins `i` to itself. -/
lemma McKayJoined.refl (i : Fin m) : McKayJoined W i i :=
  ⟨[i], rfl, rfl, List.isChain_singleton i⟩

omit [Finite G] in
/-- A single edge `rᵢⱼ ≥ 1` gives a walk `i → j`. -/
lemma McKayJoined.edge {i j : Fin m} (h : 1 ≤ mult W i j) : McKayJoined W i j :=
  ⟨[i, j], rfl, rfl, List.isChain_pair.mpr h⟩

omit [Finite G] in
/-- Walks compose: a walk `i → j` followed by a walk `j → k` gives a walk `i → k`
(splice the two lists at the shared vertex `j`). -/
lemma McKayJoined.trans {i j k : Fin m}
    (hij : McKayJoined W i j) (hjk : McKayJoined W j k) : McKayJoined W i k := by
  obtain ⟨p, hp1, hp2, hpc⟩ := hij
  obtain ⟨q, hq1, hq2, hqc⟩ := hjk
  -- `q` starts at `j`, so `q = j :: t`.
  obtain ⟨t, rfl⟩ : ∃ t, q = j :: t := by
    cases q with
    | nil => simp at hq1
    | cons a t => exact ⟨t, by simp only [List.head?_cons, Option.some.injEq] at hq1; rw [hq1]⟩
  refine ⟨p ++ t, ?_, ?_, ?_⟩
  · rw [List.head?_append, hp1]; rfl
  · rw [List.getLast?_append, hp2]
    have ht : (j :: t).getLast? = t.getLast?.or (some j) := by
      cases t <;> simp [List.getLast?_cons]
    rw [← ht]; exact hq2
  · refine hpc.append (List.isChain_cons.mp hqc).2 ?_
    intro x hx y hy
    rw [hp2, Option.mem_some_iff] at hx
    subst hx
    exact (List.isChain_cons.mp hqc).1 y hy

/-- Walks reverse: since `rᵢⱼ = rⱼᵢ` (`mult_symm`), a walk `i → j` gives a walk
`j → i`. -/
lemma McKayJoined.symm (hW : IsCompleteIrreps W) {i j : Fin m}
    (hij : McKayJoined W i j) : McKayJoined W j i := by
  obtain ⟨p, hp1, hp2, hpc⟩ := hij
  refine ⟨p.reverse, ?_, ?_, ?_⟩
  · rw [List.head?_reverse]; exact hp2
  · rw [List.getLast?_reverse]; exact hp1
  · rw [List.isChain_reverse]
    refine hpc.imp ?_
    intro a b hab
    unfold McKayAdj at hab ⊢
    rwa [mult_symm W hW b a]

variable (W)

omit [Finite G] in
/-- **`SU(2)` trace rigidity.** For `g ∈ G ⊆ SU(2)`, if `χ_V(g) = 2` then `g = 1`.
The matrix `A` of `g` is unitary with unit columns, so each diagonal entry has
`normSq ≤ 1` and real part `≤ 1`; the (real) trace `A₀₀ + A₁₁ = 2` forces both real
parts to be `1`, hence (with `normSq ≤ 1`) both diagonal entries equal `1` and the
off-diagonal entries vanish. So `A = 1` and therefore `g = 1`. This is the
faithfulness input of Problem 4.12.10 specialized to the tautological `SU(2)`
representation. -/
lemma taut_char_eq_two_imp_one (g : G) (htr : (V G).character g = 2) : g = 1 := by
  classical
  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA
  -- `A` is unitary, so its columns have unit norm.
  have hu : A ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).1
  have hstar : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hcol : ∀ i : Fin 2, ∑ k : Fin 2, Complex.normSq (A k i) = 1 := by
    intro i
    have hii : (star A * A) i i = 1 := by rw [hstar, Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at hii
    have hterm : ∀ k : Fin 2, (star A) i k * A k i
        = ((Complex.normSq (A k i) : ℝ) : ℂ) := by
      intro k; rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
    rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Complex.ofReal_sum] at hii
    exact_mod_cast hii
  have hnormle : ∀ i : Fin 2, Complex.normSq (A i i) ≤ 1 := by
    intro i; rw [← hcol i]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (A k i))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  -- `χ_V(g) = tr A = A₀₀ + A₁₁ = 2`.
  have htr2 : A 0 0 + A 1 1 = 2 := by
    have hchar : (V G).character g = A 0 0 + A 1 1 := by
      rw [charV_eq, ← hA, Matrix.trace_fin_two]
    rw [← hchar, htr]
  -- Each diagonal entry has real part `≤ 1`.
  have hre : ∀ i : Fin 2, (A i i).re ≤ 1 := by
    intro i
    have hns := Complex.normSq_apply (A i i)
    nlinarith [mul_self_nonneg (A i i).im, hnormle i, hns]
  have hre_sum : (A 0 0).re + (A 1 1).re = 2 := by
    have := congrArg Complex.re htr2
    simpa [Complex.add_re] using this
  have hre0 : (A 0 0).re = 1 := by linarith [hre 0, hre 1]
  have hre1 : (A 1 1).re = 1 := by linarith [hre 0, hre 1]
  -- A real part of `1` together with `normSq ≤ 1` forces the entry to be `1`.
  have hdiag_one : ∀ i : Fin 2, (A i i).re = 1 → A i i = 1 := by
    intro i hrei
    have him : (A i i).im = 0 := by
      have hns := Complex.normSq_apply (A i i)
      nlinarith [hnormle i, hns, hrei, mul_self_nonneg (A i i).im]
    apply Complex.ext <;> simp [hrei, him]
  have hd0 : A 0 0 = 1 := hdiag_one 0 hre0
  have hd1 : A 1 1 = 1 := hdiag_one 1 hre1
  -- Off-diagonal entries vanish (unit columns with the diagonal already norm `1`).
  have hoff01 : A 0 1 = 0 := by
    have hs := hcol 1
    rw [Fin.sum_univ_two] at hs
    have h11 : Complex.normSq (A 1 1) = 1 := by rw [hd1]; simp
    have hz : Complex.normSq (A 0 1) = 0 := by
      rw [h11] at hs; linarith [Complex.normSq_nonneg (A 0 1)]
    exact Complex.normSq_eq_zero.mp hz
  have hoff10 : A 1 0 = 0 := by
    have hs := hcol 0
    rw [Fin.sum_univ_two] at hs
    have h00 : Complex.normSq (A 0 0) = 1 := by rw [hd0]; simp
    have hz : Complex.normSq (A 1 0) = 0 := by
      rw [h00] at hs; linarith [Complex.normSq_nonneg (A 1 0)]
    exact Complex.normSq_eq_zero.mp hz
  -- Assemble `A = 1` and conclude `g = 1`.
  have hAexpand : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := by
    ext r c; fin_cases r <;> fin_cases c <;> rfl
  have hAone : A = 1 := by
    rw [hAexpand, hd0, hd1, hoff01, hoff10, ← Matrix.one_fin_two]
  have hval1 : (g.val : specialUnitaryGroup (Fin 2) ℂ) = 1 := by
    ext; rw [← hA, hAone]; rfl
  exact Subtype.ext hval1

/-- **(b)** The McKay graph is **connected**: any two vertices are joined by a
path of edges (`rᵢⱼ ≥ 1` steps). -/
theorem mckay_connected (hW : IsCompleteIrreps W) (i j : Fin m) :
    ∃ path : List (Fin m), path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        1 ≤ mult W (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- `occ n a`: character-scalar multiplicity of `W a` in `V^{⊗ n}`.
  let occ : ℕ → Fin m → ℂ := fun n a =>
    ⅟(Fintype.card G : ℂ) * ∑ g : G, ((V G).character g) ^ n * (W a).character g⁻¹
  -- dimensions are nonzero
  have hdimne : ∀ b : Fin m, Module.finrank ℂ (W b) ≠ 0 := by
    intro b h0
    haveI : Simple (W b) := hW.simple b
    haveI : Subsingleton (W b : Type) := finrank_zero_iff.mp h0
    have hz : (𝟙 (W b) : W b ⟶ W b) = 0 :=
      Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => Subsingleton.elim _ _)))
    exact id_nonzero (W b) hz
  -- **Recurrence** `occ (n+1) a = ∑ⱼ rₐⱼ · occ n j`.
  have hrec : ∀ n a, occ (n + 1) a = ∑ j, (mult W a j : ℂ) * occ n j := by
    intro n a
    have hdecomp : ∀ h : G, (V G).character h * (W a).character h
        = ∑ j, (mult W j a : ℂ) * (W j).character h := by
      intro h
      have hh := congrFun (char_eq_sum_mult W hW (V G ⊗ W a)) h
      simp only [FDRep.char_tensor, Pi.mul_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at hh
      exact hh
    have hpg : ∀ g : G, ((V G).character g) ^ (n + 1) * (W a).character g⁻¹
        = ∑ j, (mult W j a : ℂ) * (((V G).character g) ^ n * (W j).character g⁻¹) := by
      intro g
      have hgi := hdecomp g⁻¹
      rw [charV_inv] at hgi
      rw [pow_succ, mul_assoc, hgi, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    change ⅟(Fintype.card G : ℂ) * ∑ g : G, ((V G).character g) ^ (n + 1) * (W a).character g⁻¹
        = ∑ j, (mult W a j : ℂ) *
            (⅟(Fintype.card G : ℂ) * ∑ g : G, ((V G).character g) ^ n * (W j).character g⁻¹)
    rw [Finset.sum_congr rfl (fun g (_ : g ∈ Finset.univ) => hpg g), Finset.sum_comm,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mult_symm W hW a j, ← Finset.mul_sum]
    ring
  -- **Trivial vertex** `i₀` with `W i₀ ≅ 1`.
  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  have hchar1 : ∀ g : G, (FDRep.of (Representation.trivial ℂ G ℂ)).character g = 1 := by
    intro g; simp [FDRep.character, FDRep.of_ρ']
  haveI htrivsimple : Simple (FDRep.of (Representation.trivial ℂ G ℂ)) := by
    rw [FDRep.simple_iff_char_is_norm_one]
    simp [hchar1, Nat.card_eq_fintype_card]
  obtain ⟨i₀, ⟨iso₀⟩⟩ := hW.exhaustive (FDRep.of (Representation.trivial ℂ G ℂ)) htrivsimple
  -- **Base case** `occ 0 a ≠ 0 → a = i₀`.
  have hbase : ∀ a, occ 0 a ≠ 0 → a = i₀ := by
    intro a ha
    have hval : occ 0 a
        = (Module.finrank ℂ (W a ⟶ FDRep.of (Representation.trivial ℂ G ℂ)) : ℂ) := by
      have hsp := FDRep.scalar_product_char_eq_finrank_equivariant_fintype
        (FDRep.of (Representation.trivial ℂ G ℂ)) (W a)
      rw [smul_eq_mul] at hsp
      change ⅟(Fintype.card G : ℂ) * ∑ g : G, ((V G).character g) ^ 0 * (W a).character g⁻¹ = _
      rw [← hsp]
      congr 1
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [pow_zero, one_mul, hchar1 g, one_mul]
    rw [hval] at ha
    haveI : Simple (W a) := hW.simple a
    have hfr : Module.finrank ℂ (W a ⟶ FDRep.of (Representation.trivial ℂ G ℂ)) ≠ 0 := by
      intro h0; rw [h0] at ha; simp at ha
    rw [FDRep.finrank_hom_simple_simple] at hfr
    by_contra hne
    have : ¬ Nonempty (W a ≅ FDRep.of (Representation.trivial ℂ G ℂ)) := by
      rintro ⟨e⟩
      exact hne (hW.distinct a i₀ ⟨e ≪≫ iso₀⟩)
    rw [if_neg this] at hfr
    exact hfr rfl
  -- **Reachability** `occ n a ≠ 0 → i₀ ⇝ a`.
  have hreach : ∀ n a, occ n a ≠ 0 → McKayJoined W i₀ a := by
    intro n
    induction n with
    | zero => intro a ha; rw [hbase a ha]; exact McKayJoined.refl i₀
    | succ n ih =>
      intro a ha
      rw [hrec n a] at ha
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
      have hmj : mult W a j ≠ 0 := by
        intro h0; rw [h0] at hj; simp at hj
      have hoccj : occ n j ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hj; exact hj rfl
      have hedge : (1 : ℕ) ≤ mult W j a := by
        rw [mult_symm W hW j a]; omega
      exact (ih j hoccj).trans (McKayJoined.edge hedge)
  -- **Seed** every vertex occurs in some `V^{⊗ n}` (faithfulness + polynomial).
  have hseed : ∀ a, ∃ n, occ n a ≠ 0 := by
    intro a
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    -- `∀ n, ∑_g (χ_V g)^n χ_{Wₐ}(g⁻¹) = 0`.
    have hsum : ∀ n, ∑ g : G, ((V G).character g) ^ n * (W a).character g⁻¹ = 0 := by
      intro n
      have h2 : ⅟(Fintype.card G : ℂ) *
          ∑ g : G, ((V G).character g) ^ n * (W a).character g⁻¹ = 0 := hcon n
      have h3 := congrArg (fun z => (Fintype.card G : ℂ) * z) h2
      simp only [mul_zero, ← mul_assoc, mul_invOf_self, one_mul] at h3
      exact h3
    -- polynomial weighting
    have hpoly : ∀ p : Polynomial ℂ,
        ∑ g : G, p.eval ((V G).character g) * (W a).character g⁻¹ = 0 := by
      intro p
      simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro k _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, hsum k, mul_zero]
    set d : ℂ := 2 with hd
    set S : Finset ℂ := (Finset.univ.image (fun g : G => (V G).character g)).erase d with hS
    set p : Polynomial ℂ := ∏ μ ∈ S, (Polynomial.X - Polynomial.C μ) with hp
    have hp_eval : ∀ x : ℂ, p.eval x = ∏ μ ∈ S, (x - μ) := by
      intro x
      rw [hp, Polynomial.eval_prod]
      exact Finset.prod_congr rfl fun μ _ => by
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hpd_ne : p.eval d ≠ 0 := by
      rw [hp_eval]
      apply Finset.prod_ne_zero_iff.mpr
      intro μ hμ
      exact sub_ne_zero.mpr fun hc => (Finset.mem_erase.mp hμ).1 hc.symm
    have hval := hpoly p
    rw [Finset.sum_eq_single (1 : G)] at hval
    · rw [inv_one] at hval
      have hV1 : (V G).character 1 = 2 := by
        rw [charV_eq]
        have hone : (((1 : G).val : specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
        rw [hone, Matrix.trace_one]; simp
      rw [hV1, ← hd] at hval
      have hW1 : (W a).character 1 = (Module.finrank ℂ (W a) : ℂ) := FDRep.char_one _
      rw [hW1] at hval
      exact (mul_ne_zero hpd_ne (Nat.cast_ne_zero.mpr (hdimne a))) hval
    · intro b _ hb1
      have hbne : (V G).character b ≠ d := by
        rw [hd]; intro hc; exact hb1 (taut_char_eq_two_imp_one b hc)
      have : (V G).character b ∈ S := by
        rw [hS]; exact Finset.mem_erase.mpr ⟨hbne, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩
      rw [hp_eval]
      have : (∏ μ ∈ S, ((V G).character b - μ)) = 0 :=
        Finset.prod_eq_zero this (by rw [sub_self])
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ 1) h
  -- **Assemble**: every vertex reachable from `i₀`, then splice `i ⇝ i₀ ⇝ j`.
  have hall : ∀ a, McKayJoined W i₀ a := fun a =>
    (hseed a).elim (fun n hn => hreach n a hn)
  obtain ⟨p, hp1, hp2, hpc⟩ := ((hall i).symm hW).trans (hall j)
  refine ⟨p, hp1, hp2, fun k hk => ?_⟩
  have := (List.isChain_iff_getElem.mp hpc) k hk
  simpa [List.get_eq_getElem, McKayAdj] using this

/-! ## Part (c): positive semidefinite but not definite (explicit form)

The full statement `mckay_isAffineDynkin` (all six conjuncts of
`IsAffineDynkinDiagram`) appears below, after the `mckayCartan_posSemidef` /
`mckayCartan_not_posDef` lemmas it uses. -/

/-- **(c)** The McKay Cartan form is positive semidefinite. Following the book's hint, set
`f = ∑ᵢ xᵢ χ_{Wᵢ}` and compute `((2 - χ_V) f, f) = (1/|G|) ∑_g (2 - χ_V(g)) |f(g)|²`. Each factor
`2 - χ_V(g) ≥ 0` (the `SU(2)` trace bound `charV_re_le_two`, with `χ_V` real by `charV_im_zero`)
and `|f(g)|² ≥ 0`, so the sum is `≥ 0`. Orthonormality of the irreducible characters
(`FDRep.char_orthonormal`) and the multiplicity identity
(`FDRep.scalar_product_char_eq_finrank_equivariant`) identify this Hermitian value with the Cartan
form `xᵀ(2δ − r)x`. -/
theorem mckayCartan_posSemidef (hW : IsCompleteIrreps W) (hne : Nontrivial G)
    (x : Fin m → ℤ) :
    0 ≤ dotProduct x ((Matrix.of (mckayCartan W)).mulVec x) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- the class function `f = ∑ᵢ xᵢ χ_{Wᵢ}` and the target quadratic form `Q`
  set f : G → ℂ := fun g => ∑ i, (x i : ℂ) * (W i).character g with hf
  set Q : ℤ := dotProduct x ((Matrix.of (mckayCartan W)).mulVec x) with hQ
  set R : ℂ := ∑ g : G, (2 - (V G).character g) * (f g * f g⁻¹) with hR
  -- **Per-pair character identity** `∑_g (2 − χ_V) χ_{Wᵢ} χ_{Wⱼ}(·⁻¹) = |G| · (2δᵢⱼ − rᵢⱼ)`.
  have key_ij : ∀ i j : Fin m,
      (∑ g : G, (2 - (V G).character g) * (W i).character g * (W j).character g⁻¹)
        = (Fintype.card G : ℂ) * (mckayCartan W i j : ℂ) := by
    intro i j
    -- orthonormality: `∑_g χ_{Wᵢ} χ_{Wⱼ}(·⁻¹) = |G| · δᵢⱼ`
    have orth : (∑ g : G, (W i).character g * (W j).character g⁻¹)
        = (Fintype.card G : ℂ) * (if i = j then (1 : ℂ) else 0) := by
      haveI : Simple (W i) := hW.simple i
      haveI : Simple (W j) := hW.simple j
      have h := FDRep.char_orthonormal_fintype (W i) (W j)
      rw [smul_eq_mul] at h
      have hval : (if Nonempty (W i ≅ W j) then (1 : ℂ) else 0)
          = (if i = j then (1 : ℂ) else 0) := by
        by_cases hij : i = j
        · rw [if_pos (⟨eqToIso (congrArg W hij)⟩ : Nonempty (W i ≅ W j)), if_pos hij]
        · rw [if_neg (fun hh => hij (hW.distinct i j hh)), if_neg hij]
      rw [← hval, ← h, ← mul_assoc, mul_invOf_self, one_mul]
    -- multiplicity: `∑_g χ_V χ_{Wᵢ} χ_{Wⱼ}(·⁻¹) = |G| · rⱼᵢ`
    have sca : (∑ g : G, (V G).character g * (W i).character g * (W j).character g⁻¹)
        = (Fintype.card G : ℂ) * (mult W j i : ℂ) := by
      have h := FDRep.scalar_product_char_eq_finrank_equivariant_fintype (V G ⊗ W i) (W j)
      rw [smul_eq_mul] at h
      have hs : (∑ g : G, (V G ⊗ W i).character g * (W j).character g⁻¹)
          = ∑ g : G, (V G).character g * (W i).character g * (W j).character g⁻¹ := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [FDRep.char_tensor, Pi.mul_apply]
      rw [hs] at h
      simp only [mult]
      rw [← h, ← mul_assoc, mul_invOf_self, one_mul]
    -- combine
    calc (∑ g : G, (2 - (V G).character g) * (W i).character g * (W j).character g⁻¹)
        = 2 * (∑ g : G, (W i).character g * (W j).character g⁻¹)
            - (∑ g : G, (V G).character g * (W i).character g * (W j).character g⁻¹) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun g _ => by ring)
      _ = 2 * ((Fintype.card G : ℂ) * (if i = j then (1 : ℂ) else 0))
            - (Fintype.card G : ℂ) * (mult W j i : ℂ) := by rw [orth, sca]
      _ = (Fintype.card G : ℂ) * (mckayCartan W i j : ℂ) := by
          rw [mult_symm W hW j i]
          simp only [mckayCartan]
          split_ifs with h <;> push_cast <;> ring
  -- **Algebraic identity** `R = |G| · Q`.
  have hQcast : (Q : ℂ) = ∑ i, ∑ j, (x i : ℂ) * (mckayCartan W i j : ℂ) * (x j : ℂ) := by
    rw [hQ]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hexp : R = ∑ i, ∑ j, (x i : ℂ) * (x j : ℂ) *
      (∑ g : G, (2 - (V G).character g) * (W i).character g * (W j).character g⁻¹) := by
    rw [hR]
    have hpg : ∀ g : G, (2 - (V G).character g) * (f g * f g⁻¹)
        = ∑ i, ∑ j, (x i : ℂ) * (x j : ℂ) *
            ((2 - (V G).character g) * (W i).character g * (W j).character g⁻¹) := by
      intro g
      simp only [hf]
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl (fun g _ => hpg g), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum]
  have hA_identity : R = (Fintype.card G : ℂ) * (Q : ℂ) := by
    rw [hexp, hQcast, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [key_ij i j]
    ring
  -- **Reality/nonnegativity** `R = ↑(∑_g (2 − Re χ_V(g)) · |f(g)|²)` with each summand `≥ 0`.
  set S₀ : ℝ := ∑ g : G, (2 - ((V G).character g).re) * Complex.normSq (f g) with hS0
  have hS0_nonneg : 0 ≤ S₀ := by
    rw [hS0]
    refine Finset.sum_nonneg (fun g _ => ?_)
    exact mul_nonneg (by linarith [charV_re_le_two g]) (Complex.normSq_nonneg _)
  have hB : R = (S₀ : ℂ) := by
    rw [hR, hS0, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    -- `f g⁻¹ = conj (f g)`
    have hfconj : f g⁻¹ = (starRingEnd ℂ) (f g) := by
      simp only [hf, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Etingof.char_inv_eq_conj (W i) g, map_mul, map_intCast]
    -- `2 - χ_V g = ↑(2 - Re χ_V g)` since `χ_V g` is real
    have hVreal : (2 : ℂ) - (V G).character g = ((2 - ((V G).character g).re : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, charV_im_zero g]
    rw [hfconj, Complex.mul_conj, hVreal, ← Complex.ofReal_mul]
  -- **Assemble.** `|G| · Q = S₀ ≥ 0` and `|G| > 0`, so `Q ≥ 0`.
  have hfinal : (Fintype.card G : ℂ) * (Q : ℂ) = (S₀ : ℂ) := by rw [← hA_identity, hB]
  have hreal : (Fintype.card G : ℝ) * (Q : ℝ) = S₀ := by exact_mod_cast hfinal
  have hcard_pos : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hQnonneg : 0 ≤ (Q : ℝ) := by nlinarith [hreal, hS0_nonneg, hcard_pos]
  exact_mod_cast hQnonneg

/-- **(c)** The McKay Cartan form is not positive definite: the vector of
irreducible dimensions is a nonzero null vector. -/
theorem mckayCartan_not_posDef (hW : IsCompleteIrreps W) (hne : Nontrivial G) :
    ∃ x : Fin m → ℤ, x ≠ 0 ∧
      dotProduct x ((Matrix.of (mckayCartan W)).mulVec x) = 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  -- the trivial representation is simple, hence isomorphic to some `W i₀`
  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  haveI htrivsimple : Simple (FDRep.of (Representation.trivial ℂ G ℂ)) := by
    haveI : IsSimpleModule (MonoidAlgebra ℂ G) (Representation.trivial ℂ G ℂ).asModule := by
      rw [isSimpleModule_iff]
      -- Fix `V := asModule` explicitly and prove `finrank ℂ = 1` through `asModuleEquiv`,
      -- so the canonical (transferred) `Module ℂ asModule` is used consistently with the
      -- `IsScalarTower ℂ ℂ[G] asModule` instance. Passing `Module.finrank_self ℂ` directly
      -- pins `Module ℂ V` to `Complex.instModule`, which no longer matches the scalar-tower
      -- instance (defined with reduced transparency) and fails synthesis.
      refine is_simple_module_of_finrank_eq_one (K := ℂ) (A := MonoidAlgebra ℂ G)
        (V := (Representation.trivial ℂ G ℂ).asModule) ?_
      rw [(Representation.trivial ℂ G ℂ).asModuleEquiv.finrank_eq, Module.finrank_self]
    infer_instance
  obtain ⟨i₀, ⟨iso₀⟩⟩ := hW.exhaustive (FDRep.of (Representation.trivial ℂ G ℂ)) htrivsimple
  -- `dim W i₀ = 1`
  have hfr : finrank ℂ (W i₀) = 1 := by
    have hc := congrFun (FDRep.char_iso iso₀) (1 : G)
    rw [FDRep.char_one, FDRep.char_one] at hc
    have htrivfr : finrank ℂ (FDRep.of (Representation.trivial ℂ G ℂ)) = 1 :=
      Module.finrank_self ℂ
    rw [htrivfr] at hc
    exact_mod_cast hc.symm
  refine ⟨fun j => (finrank ℂ (W j) : ℤ), ?_, ?_⟩
  · -- nonzero, since the `i₀` entry is `1`
    intro hx
    have h0 : (finrank ℂ (W i₀) : ℤ) = 0 := by have := congrFun hx i₀; simpa using this
    rw [hfr] at h0
    norm_num at h0
  · -- null vector: each row dots to `0` by the marks identity
    apply Finset.sum_eq_zero
    intro i _
    have hinner : (Matrix.of (mckayCartan W)).mulVec (fun j => (finrank ℂ (W j) : ℤ)) i = 0 := by
      simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
      exact mckay_marks_aux W hW i
    rw [hinner, mul_zero]

/-! ## Part (c): combining into `IsAffineDynkinDiagram` -/

omit [Finite G] in
/-- Each irreducible `W b` is a nonzero object, so its dimension is positive. -/
lemma finrank_W_ne_zero (hW : IsCompleteIrreps W) (b : Fin m) :
    finrank ℂ (W b) ≠ 0 := by
  intro h0
  haveI : Simple (W b) := hW.simple b
  haveI : Subsingleton (W b : Type) := finrank_zero_iff.mp h0
  have hz : (𝟙 (W b) : W b ⟶ W b) = 0 :=
    Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => Subsingleton.elim _ _)))
  exact id_nonzero (W b) hz

/-- The **marks identity** in additive form: `∑ⱼ rᵢⱼ dⱼ = 2 dᵢ`, where `dⱼ = dim Wⱼ`.
Rearrangement of `mckay_marks_aux`. -/
lemma mckay_marks_sum (hW : IsCompleteIrreps W) (i : Fin m) :
    (∑ j, (mult W i j : ℤ) * (finrank ℂ (W j) : ℤ)) = 2 * (finrank ℂ (W i) : ℤ) := by
  have h := mckay_marks_aux W hW i
  have expand : ∀ j, mckayCartan W i j * (finrank ℂ (W j) : ℤ)
      = (if i = j then 2 * (finrank ℂ (W j) : ℤ) else 0)
        - (mult W i j : ℤ) * (finrank ℂ (W j) : ℤ) := by
    intro j; simp only [mckayCartan]; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => expand j), Finset.sum_sub_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => 2 * (finrank ℂ (W j) : ℤ)),
    if_pos (Finset.mem_univ i)] at h
  linarith

open Etingof.AbelianFDRep in
/-- **Cyclic case, nontriviality.** For a finite **cyclic** `G ⊂ SU(2)` with `3 ≤ m`
irreducibles, `G` is nontrivial. Since `G` is abelian, each irreducible `Wⱼ` is
`1`-dimensional, hence isomorphic to `charFDRep ξⱼ` for a character `ξⱼ : G →* ℂˣ`; the `m`
pairwise non-isomorphic `Wⱼ` give `m` distinct characters, so `m ≤ |G →* ℂˣ| = |G|`, and
`3 ≤ m` forces `|G| ≥ 3 > 1`. -/
lemma nontrivial_of_cyclic (hW : IsCompleteIrreps W) (hcyc : IsCyclic G) (hm : 3 ≤ m) :
    Nontrivial G := by
  classical
  letI : CommGroup G := hcyc.commGroup
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  have hchar : ∀ j : Fin m, ∃ ξ : G →* ℂˣ, Nonempty (W j ≅ charFDRep ξ) := by
    intro j
    haveI := hW.simple j
    exact exists_charFDRep_iso (W j)
  choose ξ hξ using hchar
  have hinj : Function.Injective ξ := by
    intro a b hab
    apply hW.distinct a b
    obtain ⟨ea⟩ := hξ a
    obtain ⟨eb⟩ := hξ b
    exact ⟨ea ≪≫ eqToIso (congrArg charFDRep hab) ≪≫ eb.symm⟩
  have hle : m ≤ Nat.card G := by
    have h1 : Fintype.card (Fin m) ≤ Fintype.card (G →* ℂˣ) :=
      Fintype.card_le_of_injective ξ hinj
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card (α := G →* ℂˣ),
      card_charFDRep_dual] at h1
    exact h1
  rw [← Finite.one_lt_card_iff_nontrivial]
  omega

/-- **Cyclic case, no invariants.** The tautological `2`-dimensional representation of a
nontrivial `G ⊂ SU(2)` has no nonzero invariant vector. A vector fixed by all of `G` is in
particular fixed by some `g ≠ 1`; then `1` is an eigenvalue of the `SU(2)`-matrix `A` of `g`,
so `det (A - 1) = 0`, and the `2×2` identity `det (A - 1) = 2 - tr A` gives `χ_V(g) = tr A = 2`,
whence `g = 1` by `taut_char_eq_two_imp_one`, a contradiction. -/
lemma finrank_invariants_V_eq_zero (hne : Nontrivial G) :
    Module.finrank ℂ (Representation.invariants (V G).ρ) = 0 := by
  classical
  have hbot : Representation.invariants (V G).ρ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Representation.mem_invariants] at hv
    rw [Submodule.mem_bot]
    by_contra hv0
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    set A : Matrix (Fin 2) (Fin 2) ℂ :=
      ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA
    -- `(V G).ρ g v` is defeq to `Matrix.toLin' A v = A *ᵥ v`; chain through the
    -- defeq with `Eq.trans` (which unfolds at default transparency) rather than a
    -- `rw [show … from rfl]`, whose pattern match runs at `instances` transparency
    -- and no longer aligns the `FDRep.of`-derived instances.
    have hgv : A *ᵥ v = v := (Matrix.toLin'_apply A v).symm.trans (hv g)
    have hker : (A - 1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hgv, sub_self]
    have hdet0 : (A - 1).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hker⟩
    have hdetA : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).2
    have hsum : A 0 0 + A 1 1 = 2 := by
      rw [Matrix.det_fin_two] at hdetA
      rw [Matrix.det_fin_two] at hdet0
      simp only [Matrix.sub_apply, Matrix.one_apply, Fin.isValue,
        show ((0 : Fin 2) = 1) = False from by simp,
        show ((1 : Fin 2) = 0) = False from by simp, if_true, if_false,
        eq_self_iff_true] at hdet0
      linear_combination hdetA - hdet0
    have hχ2 : (V G).character g = 2 := by
      rw [charV_eq, ← hA, Matrix.trace_fin_two]; exact hsum
    exact hg (taut_char_eq_two_imp_one g hχ2)
  rw [hbot]
  exact finrank_bot ℂ _

open Etingof.AbelianFDRep in
/-- **(c), cyclic case.** For a finite **cyclic** `G ⊂ SU(2)` with `3 ≤ m`, the McKay graph
has no self-loops: `rᵢᵢ = 0`. Since `G` is abelian, `Wᵢ ≅ charFDRep ξ` is `1`-dimensional, so
`χ_{Wᵢ}(g)·χ_{Wᵢ}(g⁻¹) = ξ(g)·ξ(g)⁻¹ = 1`; hence the character scalar product collapses to
`rᵢᵢ = ⅟|G| ∑_g χ_V(g) = dim V^G = 0` (the tautological representation of the nontrivial `G`
has no invariants). -/
theorem mckayAdj_no_selfLoop_cyclic
    (hW : IsCompleteIrreps W) (hcyc : IsCyclic G) (hm : 3 ≤ m) (i : Fin m) :
    mckayAdj W i i = 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  letI : CommGroup G := hcyc.commGroup
  haveI := hW.simple i
  obtain ⟨ξ, ⟨e⟩⟩ := exists_charFDRep_iso (W i)
  have hchar_eq : (W i).character = (charFDRep ξ).character := FDRep.char_iso e
  have hunit : ∀ g : G, (W i).character g * (W i).character g⁻¹ = 1 := by
    intro g
    rw [hchar_eq, charFDRep_character, charFDRep_character, map_inv]
    exact Units.mul_inv (ξ g)
  have hmult : (mult W i i : ℂ) = Module.finrank ℂ (Representation.invariants (V G).ρ) := by
    have hsp := FDRep.scalar_product_char_eq_finrank_equivariant (W i) (V G ⊗ W i)
    have havg := FDRep.average_char_eq_finrank_invariants (V G)
    have key : (Module.finrank ℂ (W i ⟶ V G ⊗ W i) : ℂ)
        = Module.finrank ℂ (Representation.invariants (V G).ρ) := by
      rw [← hsp, ← havg]
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      rw [FDRep.char_tensor, Pi.mul_apply, mul_assoc, hunit g, mul_one]
    simpa only [mult] using key
  rw [finrank_invariants_V_eq_zero (nontrivial_of_cyclic W hW hcyc hm)] at hmult
  have hmz : mult W i i = 0 := by exact_mod_cast hmult
  simp [mckayAdj, hmz]

/-! ### The central element `-Id ∈ SU(2)` (non-cyclic-case machinery)

The book's part-(c) argument uses the central element `-Id ∈ SU(2)`: it acts on the
tautological representation `V` as the scalar `-1` (so `χ_V(-Id) = -2`). These are the
concrete `SU(2)` facts; the Schur/character argument that turns them into
`rᵢᵢ = 0` is carried out both in the non-cyclic case
(`mckayAdj_no_selfLoop_of_central_neg`) and the cyclic case
(`mckayAdj_no_selfLoop_cyclic`), combined in `mckayAdj_no_selfLoop`. -/

/-- The central element `-Id ∈ SU(2)`: the negation of the identity matrix. Its
determinant is `(-1)² = 1` and it is unitary (`star (-1) * (-1) = 1`), so it lies in
`specialUnitaryGroup (Fin 2) ℂ`. -/
def negIdSU : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨-1, Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨by
      rw [Matrix.mem_unitaryGroup_iff']
      simp,
     by
      rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
      norm_num⟩⟩

@[simp] lemma negIdSU_coe :
    ((negIdSU : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

/-- `-Id` is central in `SU(2)`: as the scalar `-1` it commutes with every element. -/
lemma negIdSU_central (A : specialUnitaryGroup (Fin 2) ℂ) : negIdSU * A = A * negIdSU := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, negIdSU_coe, neg_one_mul, mul_neg_one]

omit [Finite G] in
/-- The tautological action of `-Id` on `V = ℂ²` is negation: `(-Id) · v = -v`. -/
lemma tautRep_negId (z : G)
    (hz : (z.val : specialUnitaryGroup (Fin 2) ℂ) = negIdSU) (v : Fin 2 → ℂ) :
    (tautRep G) z v = -v := by
  have hmat : ((z.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    rw [hz, negIdSU_coe]
  simp only [tautRep, MonoidHom.coe_mk, OneHom.coe_mk, hmat]
  rw [Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.one_mulVec]

omit [Finite G] in
/-- `χ_V(-Id) = -2`: the trace of `-Id : Matrix (Fin 2) (Fin 2) ℂ` is `-2`. -/
lemma charV_negId (z : G)
    (hz : (z.val : specialUnitaryGroup (Fin 2) ℂ) = negIdSU) :
    (V G).character z = -2 := by
  rw [charV_eq, hz, negIdSU_coe, Matrix.trace_fin_two]
  simp only [Matrix.neg_apply, Matrix.one_apply_eq]
  norm_num

/-! ### The cyclic-vs-`-Id` dichotomy for finite subgroups of `SU(2)`

The book's part-(c) argument (Problem 4.12.8 material) rests on: a finite subgroup
`G ⊂ SU(2)` is either cyclic or contains the central `-Id`. The elementary route:

* `-Id` is the **unique** order-2 element of `SU(2)` (`eq_negIdSU_of_sq_eq_one`): via
  Cayley–Hamilton, `g² = 1` with `det g = 1` forces `(tr g) • g = 2 • 1`, so `tr g = ±2`
  and `g = ±Id`.
* If `|G|` is **even**, Cauchy gives an order-2 element, which must be `-Id`
  (`even_card_contains_negId`).
* If `|G|` is **odd**, `G` is cyclic (`isCyclic_of_odd_card`, the hard half). -/

open Matrix in
/-- The **unique order-2 element** of `SU(2)` is `-Id`: any `g ∈ SU(2)` with `g² = 1`
and `g ≠ 1` equals `negIdSU`. Proof by Cayley–Hamilton on the `2 × 2` matrix `A = g`:
with `det A = 1` and `A * A = 1` the identity `A * A = (tr A) • A - (det A) • 1`
gives `(tr A) • A = 2 • 1`; taking determinants forces `(tr A)² = 4`, so `tr A = ±2`
and correspondingly `A = 1` (excluded) or `A = -1`. -/
lemma eq_negIdSU_of_sq_eq_one {g : specialUnitaryGroup (Fin 2) ℂ}
    (hsq : g ^ 2 = 1) (hne : g ≠ 1) : g = negIdSU := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) with hAdef
  have hdet : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  -- `A * A = 1` from `g² = 1`.
  have hAA : A * A = 1 := by
    have h1 : ((g ^ 2 : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [hsq]; rfl
    rw [pow_two, Submonoid.coe_mul] at h1
    exact h1
  -- Cayley–Hamilton for `2 × 2`: `A * A = (tr A) • A - (det A) • 1`.
  have hCH : A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.trace_fin_two, Matrix.det_fin_two, smul_eq_mul] <;> ring
  -- Hence `(tr A) • A = 2 • 1`.
  have hT : A.trace • A = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h := hCH
    rw [hAA, hdet, one_smul] at h
    -- `h : 1 = A.trace • A - 1`
    linear_combination (norm := module) -h
  -- Determinant of `hT`: `(tr A)² = 4`.
  have hdisc : A.trace ^ 2 = 4 := by
    have hd := congrArg Matrix.det hT
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, hdet, Matrix.det_one] at hd
    linear_combination hd
  -- So `tr A = 2` or `tr A = -2`.
  have hpm : A.trace = 2 ∨ A.trace = -2 := by
    have hfac : (A.trace - 2) * (A.trace + 2) = 0 := by linear_combination hdisc
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  -- `A = -1`, then `g = negIdSU`.
  have hAeq : A = -1 := by
    rcases hpm with h2 | h2
    · -- `tr A = 2` ⇒ `A = 1` ⇒ `g = 1`, contradicting `hne`.
      rw [h2] at hT
      have hA1 : A = 1 := (smul_right_inj (two_ne_zero)).mp hT
      exact absurd (Subtype.ext (show (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 by
        rw [← hAdef, hA1])) hne
    · -- `tr A = -2` ⇒ `A = -1`.
      rw [h2] at hT
      have hne2 : (-2 : ℂ) ≠ 0 := by norm_num
      have hgoal : (-2 : ℂ) • A = (-2 : ℂ) • (-1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [hT]; module
      exact (smul_right_inj hne2).mp hgoal
  exact Subtype.ext (by rw [← hAdef, hAeq, negIdSU_coe])

/-- If `|G|` is **even**, the central `-Id ∈ SU(2)` lies in `G`: Cauchy provides an
order-2 element, which is `-Id` by `eq_negIdSU_of_sq_eq_one`. -/
lemma even_card_contains_negId {G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} [Finite G]
    (hev : Even (Nat.card G)) : negIdSU ∈ G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card G := hev.two_dvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 hdvd
  -- `x : ↥G` has order 2: `x² = 1`, `x ≠ 1`.
  have hxsq : x ^ 2 = 1 := by have h := pow_orderOf_eq_one x; rwa [hx] at h
  have hxne : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx; norm_num at hx
  -- Push to the matrix group.
  have hvalsq : (x : specialUnitaryGroup (Fin 2) ℂ) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hxsq, Subgroup.coe_one]
  have hvalne : (x : specialUnitaryGroup (Fin 2) ℂ) ≠ 1 := by
    intro h; exact hxne (Subtype.ext h)
  have hxval : (x : specialUnitaryGroup (Fin 2) ℂ) = negIdSU :=
    eq_negIdSU_of_sq_eq_one hvalsq hvalne
  rw [← hxval]
  exact x.property

/-- **Eigenvalue character from reducibility.** If the tautological representation `V G`
is *not* simple, then `G` carries a character `χ : G →* ℂˣ` reading off the eigenvalue on a
`G`-invariant line, and `χ_V(g) = χ(g) + χ(g)⁻¹`.

Reducibility gives a proper nonzero `G`-invariant subspace of `ℂ²`, necessarily a line
`ℂ · v₀`; each `g` acts on it by a scalar `χ(g) ∈ ℂˣ` (multiplicative and nonzero because
`ρ` is a representation into invertibles). Since `g ∈ SU(2)` has `det = 1`, the matrix `A` of
`g` satisfies `det (A - χ(g)·I) = 0`, i.e. `χ(g)` is a root of `t² - χ_V(g)·t + 1`, giving
`χ_V(g) = χ(g) + χ(g)⁻¹`. -/
private lemma exists_eigen_character_of_not_simple
    {G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} [Finite G] (hns : ¬ Simple (V G)) :
    ∃ χ : G →* ℂˣ, ∀ g : G, (V G).character g = (χ g : ℂ) + ((χ g : ℂ))⁻¹ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- `V G = FDRep.of (tautRep G)` reducible ⟹ its `ℂ[G]`-module is not simple.
  have hnsm : ¬ IsSimpleModule (MonoidAlgebra ℂ G) (Representation.asModule (tautRep G)) := by
    intro h
    exact hns (by haveI := h; exact Etingof.simple_fdRepOf_of_isSimpleModule (tautRep G))
  -- the module is nontrivial (`ℂ²`), so non-simplicity yields a proper nonzero submodule.
  have hnt : Nontrivial (Representation.asModule (tautRep G)) := by
    let e := Representation.asModuleEquiv (tautRep G)
    refine ⟨e.symm 0, e.symm 1, fun h => ?_⟩
    exact zero_ne_one (e.symm.injective h)
  obtain ⟨N, hNb, hNt⟩ :
      ∃ N : Submodule (MonoidAlgebra ℂ G) (Representation.asModule (tautRep G)),
        N ≠ ⊥ ∧ N ≠ ⊤ := by
    by_contra hcon
    push Not at hcon
    haveI : Nontrivial (Representation.asModule (tautRep G)) := hnt
    exact hnsm { eq_bot_or_eq_top := fun N => (em (N = ⊥)).imp id (hcon N) }
  -- transport `N` to a `G`-invariant subspace `P` of `ℂ²`.
  set S : Subrepresentation (tautRep G) := Subrepresentation.ofSubmodule' N with hS
  set P : Submodule ℂ (Fin 2 → ℂ) := S.toSubmodule with hP
  have hPbot : P ≠ ⊥ := by
    obtain ⟨w, hwN, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNb
    intro hbot
    have hwP : w ∈ P := (Subrepresentation.mem_ofSubmodule'_iff).mpr hwN
    rw [hbot] at hwP
    -- `w : (tautRep G).asModule` but `P : Submodule ℂ (Fin 2 → ℂ)`, so the membership
    -- carries a mismatched element-type index that blocks a `Submodule.mem_bot` rewrite;
    -- use `.mp` (elaborated up to defeq) instead.
    exact hw0 ((Submodule.mem_bot ℂ).mp hwP)
  obtain ⟨v₀, hv0P, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPbot
  have hPtop : P ≠ ⊤ := by
    intro htop
    apply hNt
    rw [eq_top_iff]
    intro u _
    -- `u : (tautRep G).asModule`; pin `M := Fin 2 → ℂ` so `Submodule.mem_top`
    -- reads its module carrier from `P` rather than from `u`'s `asModule` type
    -- (whose `Module ℂ` instance the elaborator otherwise fails to find here).
    have huP : u ∈ P := by rw [htop]; exact Submodule.mem_top (R := ℂ) (M := Fin 2 → ℂ)
    -- `u ∈ P` and `u ∈ N` are defeq (`mem_ofSubmodule'_iff` is `Iff.rfl`); close by
    -- `exact` to avoid the lemma's implicit-argument synthesis picking up an
    -- unresolvable `Module ℂ (tautRep G).asModule` metavariable in this context.
    exact huP
  -- `P` is one-dimensional: proper (`≠ ⊤`) and nonzero (`v₀`) in the `2`-dimensional `ℂ²`.
  have hspanle : Submodule.span ℂ {v₀} ≤ P := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hv0P
  have hfr2 : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hfrspan : Module.finrank ℂ (Submodule.span ℂ {v₀}) = 1 := finrank_span_singleton hv0
  have hfrP_lt : Module.finrank ℂ P < 2 := by
    have h := Submodule.finrank_lt hPtop
    rwa [hfr2] at h
  have hPspan : Submodule.span ℂ {v₀} = P :=
    Submodule.eq_of_le_of_finrank_le hspanle (by rw [hfrspan]; omega)
  -- the eigenvalue of `g` on the line `ℂ · v₀`.
  have heig : ∀ g : G, ∃ c : ℂ, (tautRep G) g v₀ = c • v₀ := by
    intro g
    have hmem : (tautRep G) g v₀ ∈ P := S.apply_mem_toSubmodule g hv0P
    rw [← hPspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  -- scalars on the line are determined (as `v₀ ≠ 0`), so the eigenvalue is multiplicative.
  have hscal : ∀ a b : ℂ, a • v₀ = b • v₀ → a = b := by
    intro a b hab
    have hz : (a - b) • v₀ = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp hz with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  set cf : G → ℂ := fun g => (heig g).choose with hcfdef
  have hcf : ∀ g, (tautRep G) g v₀ = cf g • v₀ := fun g => (heig g).choose_spec
  have hcf1 : cf 1 = 1 := by
    have h := hcf 1
    rw [map_one, Module.End.one_apply] at h
    exact (hscal 1 (cf 1) (by rw [one_smul]; exact h)).symm
  have hcfmul : ∀ g h : G, cf (g * h) = cf g * cf h := by
    intro g h
    have e2 : (tautRep G) (g * h) v₀ = (cf g * cf h) • v₀ := by
      rw [map_mul, Module.End.mul_apply, hcf h, map_smul, hcf g, smul_smul, mul_comm]
    exact hscal _ _ ((hcf (g * h)).symm.trans e2)
  have hcfne : ∀ g : G, cf g ≠ 0 := by
    intro g hg0
    have h1 : cf g * cf g⁻¹ = cf 1 := by rw [← hcfmul, mul_inv_cancel]
    rw [hg0, zero_mul, hcf1] at h1
    exact one_ne_zero h1.symm
  let χ : G →* ℂˣ :=
    { toFun := fun g => Units.mk0 (cf g) (hcfne g)
      map_one' := Units.ext (by simp [hcf1])
      map_mul' := fun g h => Units.ext (by simp [hcfmul g h]) }
  refine ⟨χ, fun g => ?_⟩
  -- the eigenvalue reads off `χ_V(g) = χ(g) + χ(g)⁻¹` via `det = 1` on `SU(2)`.
  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    ((g.val : specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA
  have hgv : A *ᵥ v₀ = cf g • v₀ := by
    have h := hcf g
    rw [show (tautRep G) g = Matrix.toLin' A from rfl, Matrix.toLin'_apply] at h
    exact h
  have hker : (A - cf g • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ v₀ = 0 := by
    rw [Matrix.sub_mulVec, hgv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hdet0 : (A - cf g • 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v₀, hv0, hker⟩
  have hdetA : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.val.property).2
  rw [Matrix.det_fin_two] at hdet0 hdetA
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.isValue,
    show ((0 : Fin 2) = 1) = False from by simp,
    show ((1 : Fin 2) = 0) = False from by simp, if_true, if_false, smul_eq_mul, mul_one,
    mul_zero, sub_zero] at hdet0
  have key : cf g * (A 0 0 + A 1 1) = cf g * cf g + 1 := by linear_combination hdetA - hdet0
  have hchar : (V G).character g = A 0 0 + A 1 1 := by
    rw [charV_eq, hA, Matrix.trace_fin_two]
  have hcval : ((χ g : ℂˣ) : ℂ) = cf g := rfl
  rw [hchar, hcval]
  have hcne : cf g ≠ 0 := hcfne g
  field_simp
  linear_combination key

/-- **Odd-order case.** A finite subgroup of `SU(2)` of odd order is cyclic.

Argument (self-contained, no `SO(3)` classification): `|G|` odd ⇒ the tautological
`2`-dimensional representation `V` is reducible (an odd-order group has no even-dimensional
irreducible, since `dim ∣ |G|` (`finrank_dvd_card_of_irreducible`) would force `2 ∣ |G|`),
so `V` splits off a `G`-invariant line. The eigenvalue character `χ : G → ℂˣ`
(`exists_eigen_character_of_not_simple`) satisfies `χ_V(g) = χ(g) + χ(g)⁻¹`; when `χ(g) = 1`
this gives `χ_V(g) = 2`, so `g = 1` by faithfulness (`taut_char_eq_two_imp_one`). Thus `χ`
is injective and exhibits `G` as a finite subgroup of `ℂˣ`, hence cyclic by
`isCyclic_of_injective_ringHom`. -/
lemma isCyclic_of_odd_card {G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)} [Finite G]
    (hodd : Odd (Nat.card G)) : IsCyclic G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- `V G` is reducible: a `2`-dimensional irreducible would force `2 ∣ |G|`.
  have hns : ¬ Simple (V G) := by
    intro hS
    haveI := hS
    have hdvd : Module.finrank ℂ (V G) ∣ Fintype.card G := finrank_dvd_card_of_irreducible (V G)
    have hfr : Module.finrank ℂ (V G) = 2 := by
      have h1 : (Module.finrank ℂ (V G) : ℂ) = 2 := by
        rw [← FDRep.char_one (V G), charV_eq]
        have hone : (((1 : G).val : specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
        rw [hone, Matrix.trace_one]; simp
      exact_mod_cast h1
    rw [hfr] at hdvd
    rw [Nat.card_eq_fintype_card] at hodd
    obtain ⟨j, hj⟩ := hdvd
    obtain ⟨t, ht⟩ := hodd
    omega
  -- read off the eigenvalue character and use faithfulness for injectivity.
  obtain ⟨χ, hχ⟩ := exists_eigen_character_of_not_simple hns
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h2 : (V G).character g = 2 := by
      rw [hχ g, hg]; simp only [Units.val_one, inv_one]; norm_num
    exact taut_char_eq_two_imp_one g h2
  -- a finite subgroup of the units of the field `ℂ` is cyclic.
  exact isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp χ)
    (Units.val_injective.comp hinj)

/-- **The cyclic-vs-`-Id` dichotomy** (Problem 4.12.8 (b), the ingredient the book's
part-(c) hint invokes): a finite subgroup `G ⊂ SU(2)` is cyclic or contains `-Id`. -/
theorem su2_finite_cyclic_or_contains_negId
    (G : Subgroup (specialUnitaryGroup (Fin 2) ℂ)) [Finite G] :
    IsCyclic G ∨ (negIdSU ∈ G) := by
  rcases Nat.even_or_odd (Nat.card G) with hev | hodd
  · exact Or.inr (even_card_contains_negId hev)
  · exact Or.inl (isCyclic_of_odd_card hodd)

/-! ### Schur scalar helper and the non-cyclic case of no self-loops

The book's part-(c) argument for `rᵢᵢ = 0` in the **non-cyclic** case uses the central
`-Id ∈ SU(2)`. Abstractly: a central involution `z` acts on each simple `Wᵢ` by a scalar
`εᵢ = ±1` (Schur), and on `V` by `-1`; reindexing the character-scalar-product `g ↦ z·g`
picks up a factor `εᵢ⁻¹·(-εᵢ) = -1`, forcing the sum to equal its own negation, hence `0`. -/

/-- A simple `FDRep ℂ G` has positive finrank (it is a nonzero object). -/
private lemma finrank_pos_of_simple (S : FDRep ℂ G) [Simple S] : 0 < Module.finrank ℂ S := by
  by_contra h
  push Not at h
  have h0 : Module.finrank ℂ S = 0 := Nat.le_zero.mp h
  have hsub : Subsingleton S := Module.finrank_zero_iff.mp h0
  have hsub2 : Subsingleton (S ⟶ S) := by
    refine ⟨fun f g => ?_⟩
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  have e1 : Module.finrank ℂ (S ⟶ S) = 1 := by rw [FDRep.finrank_hom_simple_simple]; simp
  have e0 : Module.finrank ℂ (S ⟶ S) = 0 := Module.finrank_zero_of_subsingleton
  omega

/-- **Schur (scalar form).** A linear endomorphism `T` of a simple `S : FDRep ℂ G` that
commutes with the `G`-action is a scalar multiple of the identity. -/
lemma exists_scalar_of_commuting (S : FDRep ℂ G) [Simple S]
    (T : S →ₗ[ℂ] S) (hT : ∀ g : G, T ∘ₗ S.ρ g = S.ρ g ∘ₗ T) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- `T` is a `G`-equivariant endomorphism, i.e. an invariant of `linHom S.ρ S.ρ`.
  have hmemT : T ∈ (Representation.linHom S.ρ S.ρ).invariants := by
    intro g
    rw [Representation.linHom_apply, hT g⁻¹, ← LinearMap.comp_assoc,
      show S.ρ g ∘ₗ S.ρ g⁻¹ = LinearMap.id by
        rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_eq_id],
      LinearMap.id_comp]
  -- the invariant space is one-dimensional (categorical Schur)
  have h1dim : Module.finrank ℂ (Representation.linHom S.ρ S.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom S S)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ S
  -- the identity is a nonzero invariant, so every invariant is a scalar multiple of it
  have hid_mem : (LinearMap.id : S →ₗ[ℂ] S) ∈ (Representation.linHom S.ρ S.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (S.ρ g * S.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  have hdim_ne : (Module.finrank ℂ S : ℂ) ≠ 0 := by
    exact_mod_cast (finrank_pos_of_simple S).ne'
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom S.ρ S.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro h
    have : (Module.finrank ℂ S : ℂ) = 0 := by
      rw [← LinearMap.trace_id (R := ℂ) (M := S), h, map_zero]
    exact hdim_ne this
  obtain ⟨c, hc⟩ := ((finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom S.ρ S.ρ).invariants) hid_ne).mp h1dim)
    ⟨T, hmemT⟩
  refine ⟨c, ?_⟩
  have := congr_arg Subtype.val hc
  simpa using this.symm

/-- **Deliverable 1.** A central involution `z` (`∀ h, z·h = h·z`, `z² = 1`) acts on any
simple `S : FDRep ℂ G` as a scalar `ε` with `ε² = 1`. Schur makes `S.ρ z` a scalar, and
`z² = 1` forces the scalar to square to `1`. -/
lemma central_involution_scalar (z : G) (hz : ∀ h : G, z * h = h * z) (hz2 : z ^ 2 = 1)
    (S : FDRep ℂ G) [Simple S] :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ v, S.ρ z v = ε • v := by
  -- `S.ρ z` commutes with the action (centrality of `z`)
  have hcomm : ∀ g : G, (S.ρ z) ∘ₗ S.ρ g = S.ρ g ∘ₗ (S.ρ z) := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, hz g]
  obtain ⟨c, hc⟩ := exists_scalar_of_commuting S (S.ρ z) hcomm
  refine ⟨c, ?_, ?_⟩
  · -- `c² = 1` because `(S.ρ z)² = S.ρ (z²) = S.ρ 1 = id`
    have happ : ∀ v : S, (c * c) • v = v := by
      intro v
      have hzz : (S.ρ (z * z)) v = v := by rw [← pow_two, hz2, map_one, Module.End.one_apply]
      rw [map_mul, Module.End.mul_apply] at hzz
      have e : (S.ρ z) v = c • v := by rw [hc]; simp
      rw [e, map_smul, e, smul_smul] at hzz
      exact hzz
    have hcc : (c * c) • (LinearMap.id : S →ₗ[ℂ] S) = LinearMap.id := by
      ext v; simp only [LinearMap.smul_apply, LinearMap.id_apply]; exact happ v
    have hfin : (Module.finrank ℂ S : ℂ) ≠ 0 := by
      exact_mod_cast (finrank_pos_of_simple S).ne'
    have htr : (c * c) * (Module.finrank ℂ S : ℂ) = (Module.finrank ℂ S : ℂ) := by
      have h := congrArg (LinearMap.trace ℂ S) hcc
      rwa [map_smul, LinearMap.trace_id, smul_eq_mul] at h
    have hcc1 : c * c = 1 := mul_right_cancel₀ hfin (by rw [htr, one_mul])
    rw [pow_two]; exact hcc1
  · intro v; rw [hc]; simp only [LinearMap.smul_apply, LinearMap.id_apply]

/-- **Deliverable 2 (non-cyclic case).** If a central `z` acts on `V` as `-1`, then the McKay
graph has no self-loop at `i`: `rᵢᵢ = 0`. The central involution acts by `εᵢ = ±1` on `Wᵢ`
and by `-1` on `V`, so reindexing the character scalar product `g ↦ z·g` negates it. -/
lemma mckayAdj_no_selfLoop_of_central_neg (hW : IsCompleteIrreps W)
    (z : G) (hz_central : ∀ h : G, z * h = h * z)
    (hzV : ∀ v, (V G).ρ z v = -v) (i : Fin m) :
    mckayAdj W i i = 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hcard
  haveI := hW.simple i
  -- `z² = 1` from faithfulness of `V`: `z²` acts as `1` on `V`, so `χ_V(z²) = 2`.
  have hrho : (V G).ρ (z ^ 2) = LinearMap.id := by
    ext v
    rw [pow_two, map_mul, Module.End.mul_apply, hzV, hzV, neg_neg, LinearMap.id_apply]
  have hfr : (Module.finrank ℂ (V G) : ℂ) = 2 := by
    rw [← FDRep.char_one (V G), charV_eq]
    have hone : (((1 : G).val : specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
    rw [hone, Matrix.trace_one]; simp
  have hz2 : z ^ 2 = 1 := by
    apply taut_char_eq_two_imp_one
    rw [FDRep.character, hrho, LinearMap.trace_id, hfr]
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  -- Schur scalar `ε = ±1` for `Wᵢ`
  obtain ⟨ε, hε2, hεW⟩ := central_involution_scalar z hz_central hz2 (W i)
  have hεε : ε * ε = 1 := by rw [← pow_two]; exact hε2
  -- character behaviour of `z·g` on `V` and `Wᵢ`
  have hVchar : ∀ g : G, (V G).character (z * g) = - (V G).character g := by
    intro g
    have hmul : (V G).ρ (z * g) = -(V G).ρ g := by
      ext v; simp only [map_mul, Module.End.mul_apply, LinearMap.neg_apply, hzV]
    rw [FDRep.character, FDRep.character, hmul, map_neg]
  have hWchar : ∀ g : G, (W i).character (z * g) = ε * (W i).character g := by
    intro g
    have hmul : (W i).ρ (z * g) = ε • (W i).ρ g := by
      ext v
      simp only [map_mul, Module.End.mul_apply, LinearMap.smul_apply, hεW]
    rw [FDRep.character, FDRep.character, hmul, map_smul, smul_eq_mul]
  have hWchar_inv : ∀ g : G, (W i).character (z * g)⁻¹ = ε * (W i).character g⁻¹ := by
    intro g
    rw [_root_.mul_inv_rev, hzinv]
    have hmul : (W i).ρ (g⁻¹ * z) = ε • (W i).ρ g⁻¹ := by
      ext v
      simp only [map_mul, Module.End.mul_apply, hεW, LinearMap.map_smul, LinearMap.smul_apply]
    rw [FDRep.character, FDRep.character, hmul, map_smul, smul_eq_mul]
  -- the character scalar product
  set f : G → ℂ := fun g => (V G).character g * (W i).character g * (W i).character g⁻¹ with hf
  have hmultC : (mult W i i : ℂ) = ⅟(Fintype.card G : ℂ) • ∑ g : G, f g := by
    have h := FDRep.scalar_product_char_eq_finrank_equivariant_fintype (V G ⊗ W i) (W i)
    simp only [mult]
    rw [← h]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    simp only [FDRep.char_tensor, Pi.mul_apply, hf, mul_assoc]
  -- reindexing `g ↦ z·g` negates every summand
  have hkey : ∀ g : G, f (z * g) = - f g := by
    intro g
    simp only [hf]
    rw [hVchar, hWchar, hWchar_inv]
    linear_combination
      (-((V G).character g * (W i).character g * (W i).character g⁻¹)) * hεε
  have h1 : ∑ g : G, f (z * g) = ∑ g : G, f g := by
    have := Equiv.sum_comp (Equiv.mulLeft z) f
    simpa only [Equiv.coe_mulLeft] using this
  have h2b : ∑ g : G, f (z * g) = - ∑ g : G, f g := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun g _ => hkey g)
  have hSum : ∑ g : G, f g = - ∑ g : G, f g := h1.symm.trans h2b
  have hz0 : ∑ g : G, f g = 0 := by
    have key : ∑ g : G, f g + ∑ g : G, f g = 0 := by nth_rewrite 2 [hSum]; ring
    have h2 : (2 : ℂ) * ∑ g : G, f g = 0 := by rw [two_mul]; exact key
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hmult0 : (mult W i i : ℂ) = 0 := by rw [hmultC, hz0, smul_zero]
  have hmultN : mult W i i = 0 := by exact_mod_cast hmult0
  simp only [mckayAdj, hmultN, Nat.cast_zero]

/-- **(c)** The McKay graph has **no self-loops**: `rᵢᵢ = 0`, i.e. `Wᵢ` does not
occur in `V ⊗ Wᵢ`.

The book's argument (part (c) hint): the central element `-Id ∈ SU(2)` acts on `V`
as the scalar `-1` (`χ_V(-Id) = -2`) and on each irreducible `Wᵢ` as a scalar
`εᵢ ∈ {±1}` (Schur), so it acts on `V ⊗ Wᵢ` as `-εᵢ ≠ εᵢ`; the central characters
differ, hence no copy of `Wᵢ` sits inside `V ⊗ Wᵢ`. When `G` is not cyclic it
contains `-Id`; when `G` is cyclic (so `G ⊂ U(1)`, type `Ãₙ` with `n ≥ 3` by
`3 ≤ m`), `V` splits as `χ ⊕ χ⁻¹` with `χ` a nontrivial character, and `V ⊗ Wᵢ`
returns two characters distinct from `Wᵢ`.

This uses the `SU(2)` subgroup infrastructure of Problem 4.12.8: the central
`-Id` (`negIdSU` / `negIdSU_central`), the
cyclic-vs-`-Id` dichotomy (`su2_finite_cyclic_or_contains_negId`), and the
cyclic case (`mckayAdj_no_selfLoop_cyclic`, where `V` splits as `χ ⊕ χ⁻¹`). -/
lemma mckayAdj_no_selfLoop (hW : IsCompleteIrreps W) (hm : 3 ≤ m) (hne : Nontrivial G)
    (i : Fin m) : mckayAdj W i i = 0 := by
  -- Dichotomy (Problem 4.12.8): a finite `G ⊂ SU(2)` is cyclic or contains `-Id`.
  rcases su2_finite_cyclic_or_contains_negId G with hcyc | hneg
  · -- Cyclic case: `V ≅ χ ⊕ χ⁻¹` with `χ` nontrivial, so `V ⊗ Wᵢ` never returns `Wᵢ`.
    exact mckayAdj_no_selfLoop_cyclic W hW hcyc hm i
  · -- Non-cyclic case: the central `-Id ∈ G` acts as `-1` on `V`.
    set z : G := ⟨negIdSU, hneg⟩ with hz
    have hz_central : ∀ h : G, z * h = h * z := by
      intro h
      exact Subtype.ext (negIdSU_central h.val)
    have hzval : (z.val : specialUnitaryGroup (Fin 2) ℂ) = negIdSU := rfl
    have hzV : ∀ v, (V G).ρ z v = -v := by
      intro v
      -- `(V G).ρ z v` is defeq to `(tautRep G) z v`; close by `exact` (default
      -- transparency) rather than `simpa`, whose rewritten goal keeps the
      -- `FGModuleCat.of` carrier and no longer matches `h`'s `Fin 2 → ℂ` carrier.
      exact tautRep_negId z hzval v
    exact mckayAdj_no_selfLoop_of_central_neg W hW z hz_central hzV i

/-- **(c)** Off-diagonal multiplicities are at most `1` (single edges): for `i ≠ j`
and `3 ≤ m`, `rᵢⱼ ≤ 1`.

Proof: the marks vector `d` (all positive) satisfies `∑ₖ rᵢₖ dₖ = 2 dᵢ`, so the
single term `rᵢⱼ dⱼ ≤ 2 dᵢ` and symmetrically `rᵢⱼ dᵢ ≤ 2 dⱼ`; multiplying gives
`rᵢⱼ² ≤ 4`. If `rᵢⱼ = 2` these force `dᵢ = dⱼ` and, via the marks sum, `rᵢₖ = 0`
for all `k ≠ j` and `rⱼₖ = 0` for all `k ≠ i`, so `{i, j}` is an isolated pair,
contradicting connectivity of the McKay graph once `m ≥ 3`. -/
lemma mult_le_one_off (hW : IsCompleteIrreps W) (hm : 3 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    mult W i j ≤ 1 := by
  classical
  have hd : ∀ k, (1 : ℤ) ≤ (finrank ℂ (W k) : ℤ) := fun k => by
    have h := finrank_W_ne_zero W hW k; omega
  have hterm_nonneg : ∀ (a : Fin m) (k : Fin m),
      (0 : ℤ) ≤ (mult W a k : ℤ) * (finrank ℂ (W k) : ℤ) :=
    fun a k => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  -- single-term bounds from the marks identity
  have step1 : (mult W i j : ℤ) * (finrank ℂ (W j) : ℤ) ≤ 2 * (finrank ℂ (W i) : ℤ) := by
    rw [← mckay_marks_sum W hW i]
    exact Finset.single_le_sum (fun k _ => hterm_nonneg i k) (Finset.mem_univ j)
  have step2 : (mult W i j : ℤ) * (finrank ℂ (W i) : ℤ) ≤ 2 * (finrank ℂ (W j) : ℤ) := by
    have h := Finset.single_le_sum (f := fun k => (mult W j k : ℤ) * (finrank ℂ (W k) : ℤ))
      (fun k _ => hterm_nonneg j k) (Finset.mem_univ i)
    rw [mckay_marks_sum W hW j] at h
    rwa [mult_symm W hW j i] at h
  -- isolate: if a-row concentrates its mass on `b`, all other `a`-multiplicities vanish
  have isolate : ∀ (a b : Fin m),
      (mult W a b : ℤ) * (finrank ℂ (W b) : ℤ) = 2 * (finrank ℂ (W a) : ℤ) →
      ∀ k, k ≠ b → mult W a k = 0 := by
    intro a b hab k hk
    by_contra hne0
    have hdk : (0 : ℤ) < (finrank ℂ (W k) : ℤ) := by have := hd k; linarith
    have hpos : 0 < (mult W a k : ℤ) * (finrank ℂ (W k) : ℤ) :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hne0) hdk
    have hsub : (∑ l ∈ ({b, k} : Finset (Fin m)), (mult W a l : ℤ) * (finrank ℂ (W l) : ℤ))
        ≤ ∑ l, (mult W a l : ℤ) * (finrank ℂ (W l) : ℤ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun l _ _ => hterm_nonneg a l)
    rw [Finset.sum_pair (Ne.symm hk), mckay_marks_sum W hW a, hab] at hsub
    linarith
  -- the main bound, by contradiction
  by_contra hcon
  push Not at hcon
  have hR2 : (2 : ℤ) ≤ (mult W i j : ℤ) := by
    have : 2 ≤ mult W i j := hcon; exact_mod_cast this
  have hprod1 : (0 : ℤ) ≤ ((mult W i j : ℤ) - 2) * (finrank ℂ (W j) : ℤ) :=
    mul_nonneg (by linarith) (by linarith [hd j])
  have hprod2 : (0 : ℤ) ≤ ((mult W i j : ℤ) - 2) * (finrank ℂ (W i) : ℤ) :=
    mul_nonneg (by linarith) (by linarith [hd i])
  have hdle1 : (finrank ℂ (W j) : ℤ) ≤ (finrank ℂ (W i) : ℤ) := by nlinarith [step1, hprod1]
  have hdle2 : (finrank ℂ (W i) : ℤ) ≤ (finrank ℂ (W j) : ℤ) := by nlinarith [step2, hprod2]
  have hdeq : (finrank ℂ (W i) : ℤ) = (finrank ℂ (W j) : ℤ) := le_antisymm hdle2 hdle1
  have hfj_ge : 2 * (finrank ℂ (W i) : ℤ) ≤ (mult W i j : ℤ) * (finrank ℂ (W j) : ℤ) := by
    nlinarith [hprod1, hdeq]
  have hfj : (mult W i j : ℤ) * (finrank ℂ (W j) : ℤ) = 2 * (finrank ℂ (W i) : ℤ) :=
    le_antisymm step1 hfj_ge
  have hfj2_ge : 2 * (finrank ℂ (W j) : ℤ) ≤ (mult W i j : ℤ) * (finrank ℂ (W i) : ℤ) := by
    nlinarith [hprod2, hdeq]
  have hfj2 : (mult W j i : ℤ) * (finrank ℂ (W i) : ℤ) = 2 * (finrank ℂ (W j) : ℤ) := by
    rw [mult_symm W hW j i]; exact le_antisymm step2 hfj2_ge
  have hzi : ∀ k, k ≠ j → mult W i k = 0 := isolate i j hfj
  have hzj : ∀ k, k ≠ i → mult W j k = 0 := isolate j i hfj2
  -- connectivity contradiction: `{i, j}` cannot be an isolated pair when `m ≥ 3`
  obtain ⟨l, hl⟩ : ∃ l : Fin m, l ∉ ({i, j} : Finset (Fin m)) := by
    by_contra hc
    push Not at hc
    have hsubuniv : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := fun l _ => hc l
    have h1 := Finset.card_le_card hsubuniv
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ({i, j} : Finset (Fin m)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  -- every vertex reachable from `i` lies in `{i, j}`
  have allmem : ∀ (q : List (Fin m)), q.IsChain (McKayAdj W) →
      ∀ a, q.head? = some a → (a = i ∨ a = j) → ∀ y ∈ q, y = i ∨ y = j := by
    intro q
    induction q with
    | nil => intro _ a ha _ _ _; simp at ha
    | cons c t ih =>
      intro hchain a ha hab y hy
      simp only [List.head?_cons, Option.some.injEq] at ha
      subst c
      rcases List.mem_cons.mp hy with rfl | hyt
      · exact hab
      · cases t with
        | nil => simp at hyt
        | cons b t' =>
          have hchain' := List.isChain_cons.mp hchain
          have hadj : McKayAdj W a b := hchain'.1 b (by simp)
          have hb : b = i ∨ b = j := by
            rcases hab with rfl | rfl
            · by_contra hbc
              push Not at hbc
              have h0 := hzi b hbc.2
              unfold McKayAdj at hadj; omega
            · by_contra hbc
              push Not at hbc
              have h0 := hzj b hbc.1
              unfold McKayAdj at hadj; omega
          exact ih hchain'.2 b (by simp) hb y hyt
  -- connectivity gives a walk `i → l`, forcing `l ∈ {i, j}`
  obtain ⟨p, hp1, hp2, hpc⟩ := mckay_connected W hW i l
  have hchainp : p.IsChain (McKayAdj W) := by
    rw [List.isChain_iff_getElem]
    intro k hk
    simpa [List.get_eq_getElem, McKayAdj] using hpc k hk
  have hlmem : l ∈ p := List.mem_of_getLast? hp2
  rcases allmem p hchainp i hp1 (Or.inl rfl) l hlmem with h | h
  · exact hl.1 h
  · exact hl.2 h

/-- **(c)** All McKay multiplicities are `0` or `1`: `rᵢⱼ ≤ 1` for every `i, j`
(diagonal by `mckayAdj_no_selfLoop`, off-diagonal by `mult_le_one_off`). -/
lemma mult_le_one (hW : IsCompleteIrreps W) (hm : 3 ≤ m) (hne : Nontrivial G) (i j : Fin m) :
    mult W i j ≤ 1 := by
  by_cases h : i = j
  · subst h
    have h0 := mckayAdj_no_selfLoop W hW hm hne i
    simp only [mckayAdj] at h0
    omega
  · exact mult_le_one_off W hW hm h

/-- **(c)** The McKay adjacency matrix is symmetric with `0/1` entries and no
self-loops, its graph is connected, and its Cartan matrix `2δ - r` is positive
semidefinite but not definite, that is (for `3 ≤ m`) the McKay graph is an
affine Dynkin diagram. The `3 ≤ m` hypothesis excludes the `m = 2` case
`G ≅ ℤ/2`, whose McKay graph is the double edge `Ã₁` (violating `0/1` adjacency). -/
theorem mckay_isAffineDynkin (hW : IsCompleteIrreps W) (hm : 3 ≤ m)
    (hne : Nontrivial G) :
    Problem6_1_3_tildeE.IsAffineDynkinDiagram m (mckayAdj W) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- symmetric
    unfold Matrix.IsSymm
    ext i j
    simp only [Matrix.transpose_apply, mckayAdj]
    rw [mult_symm W hW j i]
  · -- no self-loops
    intro i
    exact mckayAdj_no_selfLoop W hW hm hne i
  · -- `0/1` entries
    intro i j
    simp only [mckayAdj]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (mult_le_one W hW hm hne i j) with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  · -- connected, with every edge labelled `1`
    intro i j
    obtain ⟨p, hp1, hp2, hpc⟩ := mckay_connected W hW i j
    refine ⟨p, hp1, hp2, fun k hk => ?_⟩
    simp only [mckayAdj]
    exact_mod_cast le_antisymm (mult_le_one W hW hm hne _ _) (hpc k hk)
  · -- positive semidefinite
    intro x
    convert mckayCartan_posSemidef W hW hne x using 3
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      mckayCartan, mckayAdj]
    split_ifs <;> simp
  · -- not positive definite
    obtain ⟨x, hx0, hx⟩ := mckayCartan_not_posDef W hW hne
    refine ⟨x, hx0, ?_⟩
    convert hx using 3
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      mckayCartan, mckayAdj]
    split_ifs <;> simp

/-! ## Part (e): irreducible dimensions are the marks -/

/-- **(e)** The dimensions of the irreducibles are the vertex labels (marks) of
the affine Dynkin diagram: the vector `dᵢ = dim Wᵢ` spans the kernel of the
McKay Cartan matrix, `∑ⱼ (2δᵢⱼ - rᵢⱼ) dⱼ = 0` for every `i`. -/
theorem mckay_dims_are_marks (hW : IsCompleteIrreps W) (i : Fin m) :
    (∑ j, mckayCartan W i j * (finrank ℂ (W j) : ℤ)) = 0 :=
  mckay_marks_aux W hW i

/-! ## Intentional omissions in parts (c)–(e)

The two-vertex double-edge `Ã₁` case, the explicit identification of the finite
subgroup families with affine ADE types in part (d), and the normalized mark
tables beyond `mckay_dims_are_marks` are intentionally outside the project scope.
See `skipped-exercises.md`. In particular, there is no proposition-valued
placeholder standing in for the omitted correspondence theorem.
-/

end Etingof.Problem6_1_6

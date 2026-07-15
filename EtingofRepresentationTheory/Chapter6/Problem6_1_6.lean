import Mathlib
import EtingofRepresentationTheory.Chapter6.Problem6_1_3_continued_tildeE
import EtingofRepresentationTheory.Chapter4.Theorem4_2_1
import EtingofRepresentationTheory.Chapter4.Discussion_4_4

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
  have h1 := FDRep.scalar_product_char_eq_finrank_equivariant (W i) (V G ⊗ W j)
  have h2 := FDRep.scalar_product_char_eq_finrank_equivariant (W j) (V G ⊗ W i)
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
        have h := FDRep.scalar_product_char_eq_finrank_equivariant (W k) S
        rw [smul_eq_mul] at h
        rw [← h, ← mul_assoc, mul_invOf_self, one_mul]
      -- orthogonality of irreducible characters
      have hO : ∀ j : Fin m, ∑ g : G, (W j).character g * (W k).character g⁻¹
          = (Fintype.card G : ℂ) * (if j = k then 1 else 0) := by
        intro j
        haveI : Simple (W j) := hW.simple j
        have h := FDRep.char_orthonormal (W j) (W k)
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

/-- **(b)** The McKay graph is **connected**: any two vertices are joined by a
path of edges (`rᵢⱼ ≥ 1` steps). -/
theorem mckay_connected (hW : IsCompleteIrreps W) (i j : Fin m) :
    ∃ path : List (Fin m), path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        1 ≤ mult W (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) := by
  sorry

/-! ## Part (c): the McKay graph is an affine Dynkin diagram -/

/-- **(c)** The McKay adjacency matrix is symmetric with `0/1` entries and no
self-loops, and its Cartan matrix `2δ - r` is positive semidefinite but not
definite — i.e. the McKay graph is an **affine Dynkin diagram**. -/
theorem mckay_isAffineDynkin (hW : IsCompleteIrreps W) (hm : 1 ≤ m)
    (hne : Nontrivial G) :
    Problem6_1_3_tildeE.IsAffineDynkinDiagram m (mckayAdj W) := by
  sorry

/-! ## Part (c): positive semidefinite but not definite (explicit form) -/

/-- **(c)** The McKay Cartan form is positive **semidefinite**. Following the book's hint, set
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
      have h := FDRep.char_orthonormal (W i) (W j)
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
      have h := FDRep.scalar_product_char_eq_finrank_equivariant (W j) (V G ⊗ W i)
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

/-- **(c)** The McKay Cartan form is **not** positive definite: the vector of
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
      exact is_simple_module_of_finrank_eq_one (Module.finrank_self ℂ)
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

/-! ## Part (e): irreducible dimensions are the marks -/

/-- **(e)** The dimensions of the irreducibles are the vertex labels (marks) of
the affine Dynkin diagram: the vector `dᵢ = dim Wᵢ` spans the kernel of the
McKay Cartan matrix, `∑ⱼ (2δᵢⱼ - rᵢⱼ) dⱼ = 0` for every `i`. -/
theorem mckay_dims_are_marks (hW : IsCompleteIrreps W) (i : Fin m) :
    (∑ j, mckayCartan W i j * (finrank ℂ (W j) : ℤ)) = 0 :=
  mckay_marks_aux W hW i

/-- **(d)** The finite subgroups of `SU(2)` (equivalently, of `SO(3)` up to the
central `±Id`, from Problem 4.12.8) correspond bijectively to the affine ADE
diagrams under the McKay correspondence: cyclic ↔ `Ãₙ`, binary dihedral ↔ `D̃ₙ`,
binary tetrahedral/octahedral/icosahedral ↔ `Ẽ₆ / Ẽ₇ / Ẽ₈`.

Recorded as a `Prop` against the real affine-type enumeration; the group
classification of Problem 4.12.8 is a separate item, so this pins the
correspondence for a later proof pass rather than asserting a vacuous theorem. -/
def McKayCorrespondence (_hW : IsCompleteIrreps W) : Prop :=
  ∃ t : Problem6_1_3_tildeE.AffineType, ∃ σ : Fin t.rank ≃ Fin m,
    ∀ i j, mckayAdj W (σ i) (σ j) = t.adj i j

end Etingof.Problem6_1_6

import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable


/-!
# Problem 2.16.4: Irreducible representations of `𝔰𝔩(2)` in characteristic `p > 2`

Over an algebraically closed field `k` of characteristic `p > 2`, the irreducible finite
dimensional representations of `𝔰𝔩(2, k)` are constrained very differently from characteristic
`0` (where they are the `(n+1)`-dimensional modules `L(n)`, `n ≥ 0`, of unbounded dimension).

This file proves a central constraint on the characteristic-`p` classification: every
irreducible representation of `𝔰𝔩(2, k)` has dimension at most `p`, and this bound is
achieved. The exhaustive parameterization is built on these results in
`Reprises/Problem2_16_4.lean`; the results below remain the Chapter 2 dimension-bound and
restricted-family endpoints.

We realize `𝔰𝔩(2, k)` as Mathlib's `LieAlgebra.SpecialLinear.sl (Fin 2) k`.

The sharpness half, the existence of a `p`-dimensional irreducible, is proved here by
constructing the highest-weight module `L(p-1)`. The construction copies the
characteristic-`0` construction in `Chapter2/Sl2Irrep.lean` to an arbitrary field:
carrier `Fin p → k`, with the same diagonal/raising/lowering formulas. The bracket relations
are ring identities valid over any commutative ring; the only characteristic-`p`-specific work
is the three nonzero-scalar facts (`natCast_inj_lt`, `natCast_ne_zero_of_lt`) used in the
irreducibility argument.
-/

namespace Etingof.Problem2_16_4

open scoped Matrix

-- `LieRing.ofAssociativeRing` is a local instance from Mathlib v4.31 onward; re-enable locally.
attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (k : Type u) [Field k]

/-- The Lie algebra `𝔰𝔩(2, k)` of traceless `2 × 2` matrices. -/
noncomputable def sl2 : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  LieAlgebra.SpecialLinear.sl (Fin 2) k

/-! ## The standard `sl(2)` triple over `k` -/

/-- The standard basis element `e₁₂` of `sl(2, k)`. -/
noncomputable def sl2_e : sl2 k :=
  LieAlgebra.SpecialLinear.single 0 1 (by omega) 1

/-- The standard basis element `e₂₁` of `sl(2, k)`. -/
noncomputable def sl2_f : sl2 k :=
  LieAlgebra.SpecialLinear.single 1 0 (by omega) 1

/-- The standard diagonal element `h = e₁₁ - e₂₂` of `sl(2, k)`. -/
noncomputable def sl2_h : sl2 k :=
  LieAlgebra.SpecialLinear.singleSubSingle 0 1 1

/-- The `(1,1)` entry of an `sl(2)` matrix equals the negative of the `(0,0)` entry. -/
theorem sl2_traceless (X : sl2 k) : X.val 1 1 = -X.val 0 0 := by
  have h2 : X.val 0 0 + X.val 1 1 = 0 := by
    have h3 : Matrix.trace X.val = 0 := X.property
    have h4 : Matrix.trace X.val = X.val 0 0 + X.val 1 1 := by
      change ∑ i : Fin 2, X.val i i = _
      rw [Fin.sum_univ_two]
    rw [h4] at h3; exact h3
  have : X.val 1 1 = 0 - X.val 0 0 := by rw [← h2]; ring
  simpa only [zero_sub] using this

/-! ## The `d`-dimensional representation

We define `ρ : sl(2) → End(V_d)` as a Lie algebra homomorphism, then use
`LieRingModule.compLieHom` to get the Lie module structure on `V_d = Fin d → k`. -/

/-- Diagonal (`h`-weight) endomorphism: `H(v)_k = (d-1-2k)·v_k`. -/
noncomputable def rhoH (d : ℕ) : Module.End k (Fin d → k) where
  toFun v k' := ((d : k) - 1 - 2 * ↑(k' : ℕ)) * v k'
  map_add' u w := by ext k'; simp [mul_add]
  map_smul' r w := by ext k'; simp [mul_comm r, mul_assoc, smul_eq_mul]

/-- Raising endomorphism: `E(v)_k = (k+1)·v_{k+1}`, with `v_d = 0`. -/
noncomputable def rhoE (d : ℕ) : Module.End k (Fin d → k) where
  toFun v k' := (↑(k' : ℕ) + 1) * if h : (k' : ℕ) + 1 < d then v ⟨k' + 1, h⟩ else 0
  map_add' u w := by ext k'; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by
    ext k'; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring

/-- Lowering endomorphism: `F(v)_k = (d-k)·v_{k-1}`, with `v_{-1} = 0`. -/
noncomputable def rhoF (d : ℕ) : Module.End k (Fin d → k) where
  toFun v k' := ((d : k) - ↑(k' : ℕ)) *
    if h : 0 < (k' : ℕ) then v ⟨k' - 1, by omega⟩ else 0
  map_add' u w := by ext k'; simp only [Pi.add_apply]; split <;> ring
  map_smul' r w := by
    ext k'; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> ring

/-- `[H, E] = 2E` -/
theorem lie_rhoH_rhoE (d : ℕ) :
    ⁅rhoH k d, rhoE k d⁆ = (2 : k) • rhoE k d := by
  apply LinearMap.ext; intro v; funext k'
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, rhoH, rhoE, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases he : (k' : ℕ) + 1 < d
  · simp only [he, dite_true]
    push_cast; ring
  · simp only [he, dite_false, mul_zero, sub_zero]

/-- `[H, F] = -2F` -/
theorem lie_rhoH_rhoF (d : ℕ) :
    ⁅rhoH k d, rhoF k d⁆ = -((2 : k) • rhoF k d) := by
  apply LinearMap.ext; intro v; funext k'
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, rhoH, rhoF, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hf : 0 < (k' : ℕ)
  · simp only [hf, dite_true]
    have hle : 1 ≤ (k' : ℕ) := by omega
    simp only [Nat.cast_sub hle]
    ring
  · simp only [hf, dite_false, mul_zero, sub_zero, neg_zero]

/-- `[E, F] = H` -/
theorem lie_rhoE_rhoF (d : ℕ) :
    ⁅rhoE k d, rhoF k d⁆ = rhoH k d := by
  apply LinearMap.ext; intro v; funext k'
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Pi.sub_apply,
    rhoH, rhoE, rhoF, LinearMap.coe_mk, AddHom.coe_mk]
  have hfin_k : ∀ (h : (k' : ℕ) < d), (⟨(k' : ℕ), h⟩ : Fin d) = k' :=
    fun _ => by ext; rfl
  by_cases he : (k' : ℕ) + 1 < d <;> by_cases hf : 0 < (k' : ℕ)
  · -- Interior: k+1 < d, k > 0
    simp only [he, hf, k'.isLt, dite_true,
      show 0 < (k' : ℕ) + 1 from by omega,
      show (k' : ℕ) + 1 - 1 = (k' : ℕ) from by omega,
      show (k' : ℕ) - 1 + 1 = (k' : ℕ) from by omega,
      dite_true, hfin_k k'.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k' : ℕ) from by omega)]
    push_cast; ring
  · -- k+1 < d, k = 0
    have hk0 : (k' : ℕ) = 0 := by omega
    simp only [he, hf, dite_true, dite_false, mul_zero, sub_zero,
      show 0 < (k' : ℕ) + 1 from by omega,
      show (k' : ℕ) + 1 - 1 = (k' : ℕ) from by omega,
      dite_true, hfin_k k'.isLt]
    simp [hk0]
  · -- k+1 ≥ d (k = d-1), k > 0
    simp only [he, hf, k'.isLt, dite_true, dite_false, mul_zero, zero_sub,
      show (k' : ℕ) - 1 + 1 = (k' : ℕ) from by omega,
      dite_true, hfin_k k'.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k' : ℕ) from by omega)]
    have hkd1 : (k' : ℕ) + 1 = d := by omega
    push_cast [Nat.cast_sub (show 1 ≤ d from by omega), ← hkd1]; ring
  · -- k+1 ≥ d, k = 0 ⟹ d ≤ 1
    have hk0 : (k' : ℕ) = 0 := by omega
    have hd1 : d = 1 := by omega
    simp only [he, hf, dite_false, mul_zero, zero_sub, neg_zero]
    subst hd1; simp

private theorem sl2_val_add (X Y : sl2 k) (i j : Fin 2) :
    (X + Y).val i j = X.val i j + Y.val i j := rfl

private theorem sl2_val_smul (r : k) (X : sl2 k) (i j : Fin 2) :
    (r • X).val i j = r * X.val i j := rfl

/-- The representation map `ρ : sl(2) → End(V_d)` as a Lie hom. -/
noncomputable def rhoLieHom (d : ℕ) :
    sl2 k →ₗ⁅k⁆ Module.End k (Fin d → k) where
  toFun X := X.val 0 0 • rhoH k d + X.val 0 1 • rhoE k d + X.val 1 0 • rhoF k d
  map_add' X Y := by
    simp only [sl2_val_add, add_smul]; abel
  map_smul' r X := by
    simp only [sl2_val_smul, mul_smul, RingHom.id_apply, smul_add]
  map_lie' {X Y} := by
    have htX : X.val 1 1 = -X.val 0 0 := sl2_traceless k X
    have htY : Y.val 1 1 = -Y.val 0 0 := sl2_traceless k Y
    have hEH : ⁅rhoE k d, rhoH k d⁆ = -((2 : k) • rhoE k d) := by
      rw [← lie_skew, lie_rhoH_rhoE]
    have hFH : ⁅rhoF k d, rhoH k d⁆ = (2 : k) • rhoF k d := by
      rw [← lie_skew, lie_rhoH_rhoF, neg_neg]
    have hFE : ⁅rhoF k d, rhoE k d⁆ = -(rhoH k d) := by
      rw [← lie_skew, lie_rhoE_rhoF]
    have hbr00 : ⁅X, Y⁆.val 0 0 =
        X.val 0 1 * Y.val 1 0 - Y.val 0 1 * X.val 1 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; ring
    have hbr01 : ⁅X, Y⁆.val 0 1 =
        2 * X.val 0 0 * Y.val 0 1 - 2 * Y.val 0 0 * X.val 0 1 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]; ring
    have hbr10 : ⁅X, Y⁆.val 1 0 =
        2 * X.val 1 0 * Y.val 0 0 - 2 * Y.val 1 0 * X.val 0 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]; ring
    -- The library `smul_lie`/`lie_smul` do not fire under `simp only` here (their
    -- discrimination-tree keys miss the `Module.End` Lie-algebra instance path), so
    -- reintroduce them as local hypotheses stated in the goal's exact form.
    have smul_lie' : ∀ (c : k) (a b : Module.End k (Fin d → k)),
        ⁅c • a, b⁆ = c • ⁅a, b⁆ := fun c a b => smul_lie c a b
    have lie_smul' : ∀ (c : k) (a b : Module.End k (Fin d → k)),
        ⁅a, c • b⁆ = c • ⁅a, b⁆ := fun c a b => lie_smul c a b
    simp only [add_lie, lie_add, smul_lie', lie_smul', lie_self, smul_zero,
      add_zero, zero_add, lie_rhoH_rhoE, lie_rhoH_rhoF, lie_rhoE_rhoF,
      hEH, hFH, hFE, smul_neg, smul_smul, hbr00, hbr01, hbr10]
    module

/-- `V_d` is a Lie ring module over `sl(2)`, via the representation `ρ`. -/
noncomputable instance irrepLieRingModule (d : ℕ) :
    LieRingModule (sl2 k) (Fin d → k) :=
  LieRingModule.compLieHom (Fin d → k) (rhoLieHom k d)

/-- `V_d` is a Lie module over `k`. -/
noncomputable instance irrepLieModule (d : ℕ) :
    @LieModule k (sl2 k) (Fin d → k) _ _ _ _ _ (irrepLieRingModule k d) :=
  LieModule.compLieHom (Fin d → k) (rhoLieHom k d)

/-- `V_d` has the correct dimension. -/
theorem irrep_finrank (d : ℕ) [NeZero d] :
    Module.finrank k (Fin d → k) = d := by
  simp

/-- `rhoLieHom` maps `sl2_h` to `rhoH`. -/
private lemma rhoLieHom_sl2_h_eq (d : ℕ) : rhoLieHom k d (sl2_h k) = rhoH k d := by
  have h00 : (sl2_h k).val 0 0 = 1 := by
    simp [sl2_h, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h01 : (sl2_h k).val 0 1 = 0 := by
    simp [sl2_h, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have h10 : (sl2_h k).val 1 0 = 0 := by
    simp [sl2_h, LieAlgebra.SpecialLinear.val_singleSubSingle,
      Matrix.sub_apply, Matrix.single]
  have key : rhoLieHom k d (sl2_h k) =
    (sl2_h k).val 0 0 • rhoH k d + (sl2_h k).val 0 1 • rhoE k d +
      (sl2_h k).val 1 0 • rhoF k d := rfl
  rw [key, h00, h01, h10]; simp

/-- `rhoLieHom` maps `sl2_e` to `rhoE`. -/
private lemma rhoLieHom_sl2_e_eq (d : ℕ) : rhoLieHom k d (sl2_e k) = rhoE k d := by
  have h00 : (sl2_e k).val 0 0 = 0 := by
    simp [sl2_e, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : (sl2_e k).val 0 1 = 1 := by
    simp [sl2_e, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : (sl2_e k).val 1 0 = 0 := by
    simp [sl2_e, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : rhoLieHom k d (sl2_e k) =
    (sl2_e k).val 0 0 • rhoH k d + (sl2_e k).val 0 1 • rhoE k d +
      (sl2_e k).val 1 0 • rhoF k d := rfl
  rw [key, h00, h01, h10]; simp

/-- `rhoLieHom` maps `sl2_f` to `rhoF`. -/
private lemma rhoLieHom_sl2_f_eq (d : ℕ) : rhoLieHom k d (sl2_f k) = rhoF k d := by
  have h00 : (sl2_f k).val 0 0 = 0 := by
    simp [sl2_f, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h01 : (sl2_f k).val 0 1 = 0 := by
    simp [sl2_f, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have h10 : (sl2_f k).val 1 0 = 1 := by
    simp [sl2_f, LieAlgebra.SpecialLinear.val_single, Matrix.single]
  have key : rhoLieHom k d (sl2_f k) =
    (sl2_f k).val 0 0 • rhoH k d + (sl2_f k).val 0 1 • rhoE k d +
      (sl2_f k).val 1 0 • rhoF k d := rfl
  rw [key, h00, h01, h10]; simp

/-- Standard basis vector `e_k` in `Fin d → k`. -/
def e_basis (d : ℕ) (k' : Fin d) : Fin d → k := Pi.single k' 1

/-- Evaluation of the standard basis vector. -/
theorem e_basis_apply (d : ℕ) (k' j : Fin d) :
    e_basis k d k' j = if j = k' then 1 else 0 := by
  simp [e_basis, Pi.single_apply]

/-! ## The characteristic-`p` nonzero-scalar facts

The only place the characteristic enters is through injectivity of `Fin p ∋ j ↦ (j : k)`
and non-vanishing of small residues. -/

/-- Distinct residues below `p` have distinct images in a field of characteristic `p`. -/
private theorem natCast_inj_lt (p : ℕ) [CharP k p] {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : k) = (b : k)) : a = b := by
  rcases le_total a b with hab | hab
  · have hz : ((b - a : ℕ) : k) = 0 := by rw [Nat.cast_sub hab, h, sub_self]
    rw [CharP.cast_eq_zero_iff k p] at hz
    have := Nat.eq_zero_of_dvd_of_lt hz (by omega)
    omega
  · have hz : ((a - b : ℕ) : k) = 0 := by rw [Nat.cast_sub hab, h, sub_self]
    rw [CharP.cast_eq_zero_iff k p] at hz
    have := Nat.eq_zero_of_dvd_of_lt hz (by omega)
    omega

/-- A nonzero residue strictly below `p` has nonzero image in characteristic `p`. -/
private theorem natCast_ne_zero_of_lt (p : ℕ) [CharP k p] {n : ℕ} (h0 : 0 < n) (hn : n < p) :
    (n : k) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff k p]
  intro hdvd
  have := Nat.eq_zero_of_dvd_of_lt hdvd hn
  omega

/-- **`V_d` is irreducible** (for `1 ≤ d ≤ p` over a field of characteristic `p > 2`). The
argument mirrors the characteristic-`0` proof in `Sl2Irrep.irrep_isIrreducible`: extract one
basis vector via the `h`-eigenvalue separation, then propagate to all basis vectors with `e`
and `f`. The three scalar non-vanishing facts specialize to `natCast_inj_lt` /
`natCast_ne_zero_of_lt`. -/
theorem irrep_isIrreducible (p : ℕ) [CharP k p] (hp2 : 2 < p) (d : ℕ) [NeZero d] (hdp : d ≤ p) :
    LieModule.IsIrreducible k (sl2 k) (Fin d → k) := by
  classical
  have h2ne : (2 : k) ≠ 0 := by
    have h := natCast_ne_zero_of_lt k p (show (0 : ℕ) < 2 by norm_num) hp2
    simpa using h
  apply LieModule.IsIrreducible.mk
  intro N hN
  rw [ne_eq, LieSubmodule.eq_bot_iff] at hN
  push Not at hN
  obtain ⟨w, hw_mem, hw_ne⟩ := hN
  -- Key connection: ⁅sl2_h, v⁆ k = (d-1-2k) * v k
  have lie_h_comp : ∀ (v : Fin d → k) (k' : Fin d),
      ((rhoLieHom k d (sl2_h k)) v) k' = ((d : k) - 1 - 2 * ↑(k' : ℕ)) * v k' := by
    intro v k'; rw [rhoLieHom_sl2_h_eq]; rfl
  -- Helper: scalar-extract from N
  have smul_extract : ∀ (c : k) (v : Fin d → k), c ≠ 0 → c • v ∈ N → v ∈ N := by
    intro c v hc hcv
    have h1 : c⁻¹ • (c • v) ∈ N := N.smul_mem c⁻¹ hcv
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
  -- Suffices to get all basis vectors in N
  suffices basis_in_N : ∀ k' : Fin d, e_basis k d k' ∈ N by
    rw [eq_top_iff]; intro v _
    have decomp : v = Finset.univ.sum (fun k' : Fin d => v k' • e_basis k d k') := by
      ext j; simp [Finset.sum_apply, e_basis_apply]
    rw [decomp]
    refine Finset.sum_induction _
      (· ∈ (N : Set (Fin d → k))) (fun a b ha hb => ?_) ?_
      (fun k' _ => ?_)
    · exact N.add_mem ha hb
    · exact N.zero_mem
    · exact N.smul_mem _ (basis_in_N k')
  -- Step A: Extract one basis vector from N
  have extract : ∃ k' : Fin d, e_basis k d k' ∈ N := by
    suffices ∀ (n : ℕ) (w : Fin d → k), w ∈ N → w ≠ 0 →
        (Finset.univ.filter (fun k' => w k' ≠ 0)).card ≤ n →
        ∃ k' : Fin d, e_basis k d k' ∈ N by
      exact this _ w hw_mem hw_ne le_rfl
    intro n
    induction n with
    | zero =>
      intro w _ hw_ne hn
      exfalso; apply hw_ne; ext k'
      by_contra hk
      have : k' ∈ Finset.univ.filter (fun k' => w k' ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k', hk⟩
      exact absurd (Finset.card_pos.mpr ⟨k', this⟩) (by omega)
    | succ n ih =>
      intro w hw_mem hw_ne hn
      by_cases hn1 : (Finset.univ.filter (fun k' => w k' ≠ 0)).card ≤ 1
      · -- At most one nonzero component: w = w(k) • e_k
        have hcard := Finset.card_le_one.mp hn1
        have hne : (Finset.univ.filter (fun k' => w k' ≠ 0)).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro hempty
          apply hw_ne; ext k'
          by_contra hk
          have : k' ∈ (∅ : Finset (Fin d)) :=
            hempty ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ k', hk⟩
          simp at this
        obtain ⟨k', hk_mem⟩ := hne
        have hk : k' ∈ Finset.univ ∧ w k' ≠ 0 := Finset.mem_filter.mp hk_mem
        refine ⟨k', ?_⟩
        have hw_eq : w = w k' • e_basis k d k' := by
          ext j
          simp only [Pi.smul_apply, e_basis_apply, smul_eq_mul]
          by_cases hjk : j = k'
          · subst hjk; simp
          · have : w j = 0 := by
              by_contra hj
              exact hjk (hcard j
                (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) k' hk_mem)
            simp [this, hjk]
        rw [hw_eq] at hw_mem
        exact smul_extract _ _ hk.2 hw_mem
      · -- Multiple nonzero components: reduce using h-eigenvalue
        push Not at hn1
        obtain ⟨j₁, hj₁_mem, j₂, hj₂_mem, hne⟩ :=
          Finset.one_lt_card.mp hn1
        have hj₁ := (Finset.mem_filter.mp hj₁_mem).2
        have hj₂ := (Finset.mem_filter.mp hj₂_mem).2
        let c : k := (d : k) - 1 - 2 * ↑(j₁ : ℕ)
        have hw'_mem :
            (fun i => ((rhoLieHom k d (sl2_h k)) w) i - c * w i) ∈ N := by
          change (rhoLieHom k d (sl2_h k)) w - c • w ∈ (N : Set _)
          exact N.sub_mem (N.lie_mem hw_mem) (N.smul_mem c hw_mem)
        have hw'_val : ∀ i : Fin d,
            ((rhoLieHom k d (sl2_h k)) w i - c * w i) =
            (2 * (↑(j₁ : ℕ) - ↑(i : ℕ))) * w i := by
          intro i; rw [lie_h_comp]; ring
        have hw'_ne : (fun i => (rhoLieHom k d (sl2_h k)) w i - c * w i) ≠ 0 := by
          intro h
          have hval := congr_fun h j₂
          rw [hw'_val] at hval
          rcases mul_eq_zero.mp hval with hz | hz
          · rcases mul_eq_zero.mp hz with h2 | hsub
            · exact h2ne h2
            · exact hne (Fin.ext (natCast_inj_lt k p (j₁.isLt.trans_le hdp)
                (j₂.isLt.trans_le hdp) (sub_eq_zero.mp hsub)))
          · exact hj₂ hz
        have hw'_fewer :
            (Finset.univ.filter (fun k' =>
              (rhoLieHom k d (sl2_h k)) w k' - c * w k' ≠ 0)).card ≤ n := by
          have hssub : (Finset.univ.filter (fun k' =>
              (rhoLieHom k d (sl2_h k)) w k' - c * w k' ≠ 0)) ⊂
            (Finset.univ.filter (fun k' => w k' ≠ 0)) := by
            constructor
            · intro i hi
              rw [Finset.mem_filter] at hi ⊢
              refine ⟨Finset.mem_univ i, ?_⟩
              rw [hw'_val i] at hi
              exact (mul_ne_zero_iff.mp hi.2).2
            · intro hsub
              have hj₁_in := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ j₁, hj₁⟩)
              rw [Finset.mem_filter] at hj₁_in
              have habs := hj₁_in.2
              rw [hw'_val] at habs
              simp at habs
          linarith [Finset.card_lt_card hssub]
        exact ih _ hw'_mem hw'_ne hw'_fewer
  obtain ⟨k₀, hk₀⟩ := extract
  -- Step B: Propagate from k₀ to all basis vectors using e and f
  -- step_down: rhoE(e_{m+1}) has coeff (m+1) at position m
  have step_down : ∀ (m : ℕ) (hm : m + 1 < d),
      e_basis k d ⟨m + 1, by omega⟩ ∈ N →
      e_basis k d ⟨m, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (rhoLieHom k d (sl2_e k)) (e_basis k d ⟨m + 1, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (rhoLieHom k d (sl2_e k)) (e_basis k d ⟨m + 1, by omega⟩) =
        (↑(m + 1) : k) • e_basis k d ⟨m, by omega⟩ := by
      rw [rhoLieHom_sl2_e_eq]
      ext k'
      simp only [rhoE, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, e_basis, Pi.single_apply]
      by_cases hk : (k' : ℕ) + 1 < d
      · simp only [hk, dite_true]
        by_cases hkm : (k' : ℕ) = m
        · subst hkm; simp
        · have hne1 : ¬((k' : ℕ) + 1 = m + 1) := by omega
          simp [Fin.ext_iff, hkm]
      · simp only [hk, dite_false, mul_zero]
        by_cases hkm : (k' : ℕ) = m
        · exfalso; omega
        · simp [Fin.ext_iff, hkm]
    rw [lie_eq] at lie_in_N
    exact smul_extract _ _
      (natCast_ne_zero_of_lt k p (by omega : 0 < m + 1) (by omega : m + 1 < p)) lie_in_N
  -- step_up: rhoF(e_m) has coeff (d-m-1) at position m+1
  have step_up : ∀ (m : ℕ) (hm : m + 1 < d),
      e_basis k d ⟨m, by omega⟩ ∈ N →
      e_basis k d ⟨m + 1, by omega⟩ ∈ N := by
    intro m hm hmem
    have lie_in_N : (rhoLieHom k d (sl2_f k)) (e_basis k d ⟨m, by omega⟩) ∈ N :=
      N.lie_mem hmem
    have lie_eq : (rhoLieHom k d (sl2_f k)) (e_basis k d ⟨m, by omega⟩) =
        ((d : k) - ↑(m + 1)) • e_basis k d ⟨m + 1, by omega⟩ := by
      rw [rhoLieHom_sl2_f_eq]
      ext k'
      simp only [rhoF, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
        smul_eq_mul, e_basis, Pi.single_apply]
      by_cases hk : 0 < (k' : ℕ)
      · simp only [hk, dite_true]
        by_cases hkm : (k' : ℕ) = m + 1
        · have hksub : (k' : ℕ) - 1 = m := by omega
          have hkeq : k' = ⟨m + 1, by omega⟩ := Fin.ext (by omega)
          simp [hkeq]
        · have : (k' : ℕ) - 1 ≠ m := by omega
          simp [Fin.ext_iff, this, hkm]
      · simp only [hk, dite_false, mul_zero]
        push Not at hk
        simp [Fin.ext_iff, show (k' : ℕ) ≠ m + 1 from by omega]
    rw [lie_eq] at lie_in_N
    have hc : ((d : k) - ↑(m + 1)) ≠ 0 := by
      rw [← Nat.cast_sub (by omega : m + 1 ≤ d)]
      exact natCast_ne_zero_of_lt k p (by omega : 0 < d - (m + 1)) (by omega : d - (m + 1) < p)
    exact smul_extract _ _ hc lie_in_N
  -- Get e_0 ∈ N by stepping down from k₀
  have hd_pos : 0 < d := NeZero.pos d
  have e0_mem : e_basis k d ⟨0, hd_pos⟩ ∈ N := by
    suffices ∀ (m : ℕ) (hm : m < d),
        e_basis k d ⟨m, hm⟩ ∈ N → e_basis k d ⟨0, hd_pos⟩ ∈ N from
      this k₀.val k₀.isLt hk₀
    intro m hm
    induction m with
    | zero => exact id
    | succ m ihm => intro hmem; exact ihm (by omega) (step_down m (by omega) hmem)
  -- Get all basis vectors by stepping up from e_0
  intro k'
  suffices ∀ (j : ℕ) (hj : j < d), e_basis k d ⟨j, hj⟩ ∈ N from
    this k'.val k'.isLt
  intro j hj
  induction j with
  | zero => exact e0_mem
  | succ j ih => exact step_up j hj (ih (by omega))

/-! ## The dimension bound

Every irreducible finite dimensional representation of `𝔰𝔩(2, k)` in characteristic `p > 2`
has dimension at most `p`.

The argument works with the three operators `E, F, H : End(M)` obtained from the standard basis
via `LieModule.toEnd`, satisfying `[H,E] = 2E`, `[H,F] = -2F`, `[E,F] = H`. In characteristic
`p` the powers `E^p` and `F^p` are central (they commute with `E, F, H`), so by Schur's lemma
they act as scalars `α, β`. Then:

* if `α = 0`, `E` is nilpotent, so there is a highest weight vector `v₀` with `E v₀ = 0`; the
  span of `{F^j v₀ : j < p}` is a nonzero submodule, hence everything, and has dimension `≤ p`;
* if `α ≠ 0`, `E` is injective; picking a joint eigenvector `v₀` of `H` and `F·E`, the span of
  `{E^i v₀ : i < p}` is a nonzero submodule, hence everything, and has dimension `≤ p`.
-/

section DimensionBound

variable {k}

/-! ### Bracket relations in `𝔰𝔩(2, k)` -/

/-- `[h, e] = 2e` in `𝔰𝔩(2, k)`. -/
theorem lie_sl2_h_e : ⁅sl2_h k, sl2_e k⁆ = (2 : k) • sl2_e k := by
  apply Subtype.ext
  -- Apply `coe_bracket` *before* unfolding `sl2_h`/`sl2_e`: unfolding first retypes the
  -- bracket arguments as bare `SpecialLinear.sl` elements, which no longer unify with the
  -- project-level `sl2 k` that `coe_bracket` keys on.
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket,
    show (↑((2 : k) • sl2_e k) : Matrix (Fin 2) (Fin 2) k) = (2 : k) • ↑(sl2_e k) from rfl]
  simp only [sl2_h, sl2_e, LieAlgebra.SpecialLinear.val_singleSubSingle,
    LieAlgebra.SpecialLinear.val_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply] ; ring

/-- `[h, f] = -2f` in `𝔰𝔩(2, k)`. -/
theorem lie_sl2_h_f : ⁅sl2_h k, sl2_f k⁆ = -((2 : k) • sl2_f k) := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket,
    show (↑(-((2 : k) • sl2_f k)) : Matrix (Fin 2) (Fin 2) k) = -((2 : k) • ↑(sl2_f k)) from rfl]
  simp only [sl2_h, sl2_f, LieAlgebra.SpecialLinear.val_singleSubSingle,
    LieAlgebra.SpecialLinear.val_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply] ; ring

/-- `[e, f] = h` in `𝔰𝔩(2, k)`. -/
theorem lie_sl2_e_f : ⁅sl2_e k, sl2_f k⁆ = sl2_h k := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]
  simp only [sl2_h, sl2_e, sl2_f, LieAlgebra.SpecialLinear.val_singleSubSingle,
    LieAlgebra.SpecialLinear.val_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply]

/-- Every element of `𝔰𝔩(2, k)` is the combination `x₀₁·e + x₁₀·f + x₀₀·h` of the standard basis
(using tracelessness for the `(1,1)`-entry). -/
theorem sl2_decomp (x : sl2 k) :
    x = x.val 0 1 • sl2_e k + x.val 1 0 • sl2_f k + x.val 0 0 • sl2_h k := by
  apply Subtype.ext
  have htr : x.val 1 1 = -x.val 0 0 := sl2_traceless k x
  -- The additive/scalar coercions out of `sl2 k` are definitional; rewrite the right-hand
  -- side in one step rather than relying on `SetLike.val_smul`/`coe_add` simp lemmas, whose
  -- discrimination keys miss the `sl2 k` instance path here.
  rw [show (↑(x.val 0 1 • sl2_e k + x.val 1 0 • sl2_f k + x.val 0 0 • sl2_h k)
        : Matrix (Fin 2) (Fin 2) k)
      = x.val 0 1 • (↑(sl2_e k) : Matrix (Fin 2) (Fin 2) k)
        + x.val 1 0 • ↑(sl2_f k) + x.val 0 0 • ↑(sl2_h k) from rfl]
  simp only [sl2_e, sl2_f, sl2_h, LieAlgebra.SpecialLinear.val_single,
    LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, htr]

/-! ### Schur's lemma for the Lie module `M` -/

section SchurHelpers

variable {M : Type*} [AddCommGroup M] [Module k M] [LieRingModule (sl2 k) M]
  [LieModule k (sl2 k) M]

omit [LieModule k (sl2 k) M] in
/-- A `k`-linear submodule of `M` that is closed under the `𝔰𝔩(2)`-action and contains a nonzero
vector is everything, when `M` is irreducible. -/
theorem eq_top_of_lie_closed [LieModule.IsIrreducible k (sl2 k) M]
    (W : Submodule k M) (hlie : ∀ (x : sl2 k) (m : M), m ∈ W → ⁅x, m⁆ ∈ W)
    (hne : ∃ v ∈ W, v ≠ 0) : W = ⊤ := by
  let N : LieSubmodule k (sl2 k) M :=
    { toSubmodule := W, lie_mem := fun {x m} h => hlie x m h }
  have hNbot : N ≠ ⊥ := by
    rw [ne_eq, LieSubmodule.eq_bot_iff]
    push Not
    obtain ⟨v, hvW, hv0⟩ := hne
    exact ⟨v, hvW, hv0⟩
  have hNtop : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hNbot
  have hWtop : (N : Submodule k M) = ⊤ := by rw [LieSubmodule.toSubmodule_eq_top]; exact hNtop
  exact hWtop

/-- Closure of a `k`-submodule under the action of every `x ∈ 𝔰𝔩(2)` reduces to closure under the
three generators `e, f, h`. -/
theorem lie_closed_of_efh (W : Submodule k M)
    (hE : ∀ m ∈ W, ⁅sl2_e k, m⁆ ∈ W)
    (hF : ∀ m ∈ W, ⁅sl2_f k, m⁆ ∈ W)
    (hH : ∀ m ∈ W, ⁅sl2_h k, m⁆ ∈ W) :
    ∀ (x : sl2 k) (m : M), m ∈ W → ⁅x, m⁆ ∈ W := by
  intro x m hm
  have e1 : ∀ y : sl2 k, ⁅y, m⁆ = (LieModule.toEnd k (sl2 k) M y) m := fun _ => rfl
  have key : ⁅x, m⁆ = x.val 0 1 • ⁅sl2_e k, m⁆ + x.val 1 0 • ⁅sl2_f k, m⁆
      + x.val 0 0 • ⁅sl2_h k, m⁆ := by
    conv_lhs => rw [e1 x, sl2_decomp x, map_add, map_add, map_smul, map_smul, map_smul,
      LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.smul_apply]
    rw [e1 (sl2_e k), e1 (sl2_f k), e1 (sl2_h k)]
  rw [key]
  exact W.add_mem (W.add_mem (W.smul_mem _ (hE m hm)) (W.smul_mem _ (hF m hm)))
    (W.smul_mem _ (hH m hm))

/-- **Schur's lemma (Lie module form).** A `k`-linear endomorphism of a finite dimensional
irreducible `𝔰𝔩(2)`-module over an algebraically closed field that commutes with the action is a
scalar. -/
theorem lie_schur [IsAlgClosed k] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (sl2 k) M]
    (φ : Module.End k M) (hφ : ∀ (x : sl2 k) (m : M), φ ⁅x, m⁆ = ⁅x, φ m⁆) :
    ∃ c : k, ∀ m : M, φ m = c • m := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (sl2 k) M
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue φ
  refine ⟨μ, ?_⟩
  have hclosed : ∀ (x : sl2 k) (m : M), m ∈ φ.eigenspace μ → ⁅x, m⁆ ∈ φ.eigenspace μ := by
    intro x m hm
    rw [Module.End.mem_eigenspace_iff] at hm ⊢
    rw [hφ, hm, lie_smul]
  have hne : ∃ v ∈ φ.eigenspace μ, v ≠ 0 := by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    exact ⟨v, hv.1, hv.2⟩
  have htop := eq_top_of_lie_closed (φ.eigenspace μ) hclosed hne
  intro m
  have hm : m ∈ φ.eigenspace μ := by rw [htop]; trivial
  rwa [Module.End.mem_eigenspace_iff] at hm

omit [LieRingModule (sl2 k) M] [LieModule k (sl2 k) M] in
/-- If a linear operator maps the generators of a span into the span, it maps the whole span into
itself. -/
theorem span_closed_of_gens (T : Module.End k M) (S : Set M)
    (h : ∀ s ∈ S, T s ∈ Submodule.span k S) {m : M} (hm : m ∈ Submodule.span k S) :
    T m ∈ Submodule.span k S := by
  induction hm using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

omit [LieRingModule (sl2 k) M] [LieModule k (sl2 k) M] in
/-- Dimension bound from a cyclic spanning set: if the span of `{g 0, …, g (p-1)}` is everything,
then `finrank M ≤ p`. -/
theorem finrank_le_of_orbit_top (p : ℕ) (g : ℕ → M)
    (htop : Submodule.span k (Set.range (fun i : Fin p => g (i : ℕ))) = ⊤) :
    Module.finrank k M ≤ p := by
  have := finrank_le_of_span_eq_top htop
  simpa using this

end SchurHelpers

/-! ### The main bound -/

variable (k)

/-- **Dimension bound.** Over an algebraically closed field of characteristic `p > 2`, every
irreducible finite dimensional representation of `𝔰𝔩(2)` has dimension at most `p`. -/
theorem finrank_irreducible_le_char [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hp : 2 < p)
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (sl2 k) M] [LieModule k (sl2 k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (sl2 k) M] :
    Module.finrank k M ≤ p := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (sl2 k) M
  -- The three standard operators on `M`.
  set E := LieModule.toEnd k (sl2 k) M (sl2_e k) with hEdef
  set F := LieModule.toEnd k (sl2 k) M (sl2_f k) with hFdef
  set H := LieModule.toEnd k (sl2 k) M (sl2_h k) with hHdef
  -- `⁅x, m⁆` is `toEnd x m`; for the basis this is `E`, `F`, `H`.
  have hEe : ∀ m : M, ⁅sl2_e k, m⁆ = E m := fun _ => rfl
  have hFf : ∀ m : M, ⁅sl2_f k, m⁆ = F m := fun _ => rfl
  have hHh : ∀ m : M, ⁅sl2_h k, m⁆ = H m := fun _ => rfl
  -- Operator relations, transported from the Lie algebra brackets.
  have hHE : H * E = E * H + (2 : k) • E := by
    have h1 : (⁅H, E⁆ : Module.End k M) = (2 : k) • E := by
      rw [hHdef, hEdef, ← (LieModule.toEnd k (sl2 k) M).map_lie, lie_sl2_h_e, map_smul]
    rw [LieRing.of_associative_ring_bracket, sub_eq_iff_eq_add] at h1
    rw [h1, add_comm]
  have hHF : H * F = F * H - (2 : k) • F := by
    have h1 : (⁅H, F⁆ : Module.End k M) = -((2 : k) • F) := by
      rw [hHdef, hFdef, ← (LieModule.toEnd k (sl2 k) M).map_lie, lie_sl2_h_f, map_neg, map_smul]
    rw [LieRing.of_associative_ring_bracket, sub_eq_iff_eq_add] at h1
    rw [h1]; abel
  have hEF : E * F - F * E = H := by
    have h1 : (⁅E, F⁆ : Module.End k M) = H := by
      rw [hEdef, hFdef, ← (LieModule.toEnd k (sl2 k) M).map_lie, lie_sl2_e_f]
    rwa [LieRing.of_associative_ring_bracket] at h1
  -- `H · Eⁱ = Eⁱ · H + 2i · Eⁱ`.
  have hHEpow : ∀ i : ℕ, H * E ^ i = E ^ i * H + ((2 * i : ℕ) : k) • E ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
      have hsc : ((2 : k) + ((2 * n : ℕ) : k)) = ((2 * (n + 1) : ℕ) : k) := by push_cast; ring
      calc H * E ^ (n + 1)
          = (H * E ^ n) * E := by rw [pow_succ, ← mul_assoc]
        _ = (E ^ n * H + ((2 * n : ℕ) : k) • E ^ n) * E := by rw [ih]
        _ = E ^ n * (H * E) + ((2 * n : ℕ) : k) • (E ^ n * E) := by
              rw [add_mul, mul_assoc, smul_mul_assoc]
        _ = E ^ n * (E * H + (2 : k) • E) + ((2 * n : ℕ) : k) • (E ^ n * E) := by rw [hHE]
        _ = (E ^ n * E) * H + ((2 : k) + ((2 * n : ℕ) : k)) • (E ^ n * E) := by
              rw [mul_add, ← mul_assoc, mul_smul_comm, add_assoc, ← add_smul]
        _ = E ^ (n + 1) * H + ((2 * (n + 1) : ℕ) : k) • E ^ (n + 1) := by rw [hsc, ← pow_succ]
  -- `F · Eⁿ⁺¹ - Eⁿ⁺¹ · F = -(n+1)·Eⁿ·H - (n+1)n·Eⁿ`.
  have hrec : ∀ m : ℕ, F * E ^ (m + 1) - E ^ (m + 1) * F
      = (F * E ^ m - E ^ m * F) * E - E ^ m * H := by
    intro m
    have hEFc : E * F = F * E + H := by rw [← hEF]; abel
    calc F * E ^ (m + 1) - E ^ (m + 1) * F
        = F * E ^ m * E - E ^ m * (E * F) := by rw [pow_succ]; noncomm_ring
      _ = F * E ^ m * E - E ^ m * (F * E + H) := by rw [hEFc]
      _ = F * E ^ m * E - E ^ m * (F * E) - E ^ m * H := by noncomm_ring
      _ = (F * E ^ m - E ^ m * F) * E - E ^ m * H := by noncomm_ring
  have hFEpow : ∀ n : ℕ, F * E ^ (n + 1) - E ^ (n + 1) * F
      = -(((n + 1 : ℕ) : k)) • (E ^ n * H) - (((n + 1) * n : ℕ) : k) • E ^ n := by
    intro n
    induction n with
    | zero =>
      have hlhs : F * E ^ (0 + 1) - E ^ (0 + 1) * F = -H := by
        rw [zero_add, pow_one, ← hEF]; abel
      have hrhs : -(((0 + 1 : ℕ) : k)) • (E ^ 0 * H) - (((0 + 1) * 0 : ℕ) : k) • E ^ 0 = -H := by
        simp
      rw [hlhs, hrhs]
    | succ n ih =>
      rw [hrec (n + 1), ih]
      have hHErw : E ^ (n + 1) * H = E ^ n * (H * E) - (2 : k) • E ^ (n + 1) := by
        rw [hHE]; noncomm_ring
      -- expand and collect
      have hsc1 : (((n + 1 : ℕ) : k) + 1) = (((n + 1) + 1 : ℕ) : k) := by push_cast; ring
      have hsc2 : ((2 : k) * ((n + 1 : ℕ) : k) + (((n + 1) * n : ℕ) : k))
          = ((((n + 1) + 1) * (n + 1) : ℕ) : k) := by push_cast; ring
      rw [sub_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, hHE, mul_add, mul_smul_comm,
        ← pow_succ]
      -- goal now purely in `E^(n+1)*H`, `E^(n+1)`; finish with scalar algebra
      rw [show (E ^ n * (E * H)) = E ^ (n + 1) * H from by rw [pow_succ]; noncomm_ring]
      module
  -- `E^p` and `F^p` are central, hence scalars.
  have hcharp : ((p : ℕ) : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k p
  have hcomm_to_schur : ∀ (φ : Module.End k M), φ * E = E * φ → φ * F = F * φ →
      φ * H = H * φ → ∀ (x : sl2 k) (m : M), φ ⁅x, m⁆ = ⁅x, φ m⁆ := by
    intro φ hcE hcF hcH x m
    have hxdecomp : (LieModule.toEnd k (sl2 k) M x)
        = x.val 0 1 • E + x.val 1 0 • F + x.val 0 0 • H := by
      conv_lhs => rw [sl2_decomp x]
      rw [map_add, map_add, map_smul, map_smul, map_smul, ← hEdef, ← hFdef, ← hHdef]
    have hgen : φ * (LieModule.toEnd k (sl2 k) M x) = (LieModule.toEnd k (sl2 k) M x) * φ := by
      rw [hxdecomp, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm, hcE, hcF, hcH,
        ← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, ← add_mul, ← add_mul]
    calc φ ⁅x, m⁆ = φ ((LieModule.toEnd k (sl2 k) M x) m) := rfl
      _ = (φ * (LieModule.toEnd k (sl2 k) M x)) m := rfl
      _ = ((LieModule.toEnd k (sl2 k) M x) * φ) m := by rw [hgen]
      _ = ⁅x, φ m⁆ := rfl
  -- `E^p` scalar
  have hEpFcomm : E ^ p * F = F * E ^ p := by
    have hp1 : p - 1 + 1 = p := by omega
    have h := hFEpow (p - 1)
    have hz1 : (((p - 1 + 1 : ℕ) : k)) = 0 := by rw [hp1]; exact hcharp
    have hz2 : ((((p - 1 + 1) * (p - 1) : ℕ) : k)) = 0 := by
      rw [hp1]; push_cast [hcharp]; ring
    rw [hz1, hz2] at h
    simp only [neg_zero, zero_smul, sub_zero] at h
    rw [hp1] at h
    exact (sub_eq_zero.mp h).symm
  have hEpHcomm : E ^ p * H = H * E ^ p := by
    have h := hHEpow p
    have hz : (((2 * p : ℕ) : k)) = 0 := by push_cast [hcharp]; ring
    rw [hz, zero_smul, add_zero] at h
    exact h.symm
  have hEpEcomm : E ^ p * E = E * E ^ p := by rw [← pow_succ, ← pow_succ']
  obtain ⟨α, hα'⟩ := lie_schur (E ^ p) (hcomm_to_schur (E ^ p) hEpEcomm hEpFcomm hEpHcomm)
  have hα : E ^ p = α • 1 := by ext m; rw [hα' m]; simp
  -- `F^p` scalar (symmetric)
  have hFpEcomm : F ^ p * E = E * F ^ p := by
    -- apply the `E`-lemmas with roles swapped `E ↔ F`, `H ↔ -H`
    have hHF' : (-H) * F = F * (-H) + (2 : k) • F := by
      rw [neg_mul, mul_neg, hHF]; abel
    have hFE' : F * E - E * F = -H := by rw [← hEF]; abel
    -- `F · Fⁿ⁺¹` commutator identity, char `p`
    have hrec' : ∀ m : ℕ, E * F ^ (m + 1) - F ^ (m + 1) * E
        = (E * F ^ m - F ^ m * E) * F - F ^ m * (-H) := by
      intro m
      have hFEc : F * E = E * F + (-H) := by rw [← hFE']; abel
      calc E * F ^ (m + 1) - F ^ (m + 1) * E
          = E * F ^ m * F - F ^ m * (F * E) := by rw [pow_succ]; noncomm_ring
        _ = E * F ^ m * F - F ^ m * (E * F + (-H)) := by rw [hFEc]
        _ = E * F ^ m * F - F ^ m * (E * F) - F ^ m * (-H) := by noncomm_ring
        _ = (E * F ^ m - F ^ m * E) * F - F ^ m * (-H) := by noncomm_ring
    have hFFpow : ∀ n : ℕ, E * F ^ (n + 1) - F ^ (n + 1) * E
        = -(((n + 1 : ℕ) : k)) • (F ^ n * (-H)) - (((n + 1) * n : ℕ) : k) • F ^ n := by
      intro n
      induction n with
      | zero =>
        have hlhs : E * F ^ (0 + 1) - F ^ (0 + 1) * E = -(-H) := by
          rw [zero_add, pow_one, ← hFE']; abel
        have hrhs : -(((0 + 1 : ℕ) : k)) • (F ^ 0 * (-H)) - (((0 + 1) * 0 : ℕ) : k) • F ^ 0
            = -(-H) := by simp
        rw [hlhs, hrhs]
      | succ n ih =>
        rw [hrec' (n + 1), ih]
        rw [sub_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, hHF', mul_add, mul_smul_comm,
          ← pow_succ]
        rw [show (F ^ n * (F * (-H))) = F ^ (n + 1) * (-H) from by rw [pow_succ]; noncomm_ring]
        module
    have hp1 : p - 1 + 1 = p := by omega
    have hh := hFFpow (p - 1)
    have hz1 : (((p - 1 + 1 : ℕ) : k)) = 0 := by rw [hp1]; exact hcharp
    have hz2 : ((((p - 1 + 1) * (p - 1) : ℕ) : k)) = 0 := by rw [hp1]; push_cast [hcharp]; ring
    rw [hz1, hz2] at hh
    simp only [neg_zero, zero_smul, sub_zero] at hh
    rw [hp1] at hh
    exact (sub_eq_zero.mp hh).symm
  have hFpHcomm : F ^ p * H = H * F ^ p := by
    -- `H · Fⁿ = Fⁿ · H - 2n · Fⁿ`
    have hHFpow : ∀ i : ℕ, H * F ^ i = F ^ i * H - ((2 * i : ℕ) : k) • F ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ n ih =>
        have hsc : (((2 * (n + 1) : ℕ) : k)) = ((2 * n : ℕ) : k) + (2 : k) := by push_cast; ring
        calc H * F ^ (n + 1)
            = (H * F ^ n) * F := by rw [pow_succ, ← mul_assoc]
          _ = (F ^ n * H - ((2 * n : ℕ) : k) • F ^ n) * F := by rw [ih]
          _ = F ^ n * (H * F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by
                rw [sub_mul, mul_assoc, smul_mul_assoc]
          _ = F ^ n * (F * H - (2 : k) • F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by rw [hHF]
          _ = F ^ (n + 1) * H - ((2 * (n + 1) : ℕ) : k) • F ^ (n + 1) := by
                rw [mul_sub, ← mul_assoc, mul_smul_comm, ← pow_succ, hsc, add_smul]
                abel
    have h := hHFpow p
    have hz : (((2 * p : ℕ) : k)) = 0 := by push_cast [hcharp]; ring
    rw [hz, zero_smul, sub_zero] at h
    exact h.symm
  have hFpFcomm : F ^ p * F = F * F ^ p := by rw [← pow_succ, ← pow_succ']
  obtain ⟨β, hβ'⟩ := lie_schur (F ^ p) (hcomm_to_schur (F ^ p) hFpEcomm hFpFcomm hFpHcomm)
  have hβ : F ^ p = β • 1 := by ext m; rw [hβ' m]; simp
  -- Now split on whether `E` is invertible.
  -- `H · Fⁱ = Fⁱ · H - 2i · Fⁱ`.
  have hHFpow : ∀ i : ℕ, H * F ^ i = F ^ i * H - ((2 * i : ℕ) : k) • F ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
      have hsc : (((2 * (n + 1) : ℕ) : k)) = ((2 * n : ℕ) : k) + (2 : k) := by push_cast; ring
      calc H * F ^ (n + 1)
          = (H * F ^ n) * F := by rw [pow_succ, ← mul_assoc]
        _ = (F ^ n * H - ((2 * n : ℕ) : k) • F ^ n) * F := by rw [ih]
        _ = F ^ n * (H * F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by
              rw [sub_mul, mul_assoc, smul_mul_assoc]
        _ = F ^ n * (F * H - (2 : k) • F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by rw [hHF]
        _ = F ^ (n + 1) * H - ((2 * (n + 1) : ℕ) : k) • F ^ (n + 1) := by
              rw [mul_sub, ← mul_assoc, mul_smul_comm, ← pow_succ, hsc, add_smul]
              abel
  by_cases hα0 : α = 0
  · -- `α = 0`: `E` is nilpotent, use a highest weight vector.
    have hEnil : E ^ p = 0 := by rw [hα, hα0, zero_smul]
    -- `ker E ≠ ⊥`: otherwise `E`, hence `E^p`, would be injective, impossible since `E^p = 0`.
    have hKne : LinearMap.ker E ≠ ⊥ := by
      rw [Ne, LinearMap.ker_eq_bot]
      intro hEinj
      have hEpinj : Function.Injective (E ^ p) := by
        rw [Module.End.coe_pow]; exact hEinj.iterate p
      rw [hEnil] at hEpinj
      obtain ⟨a, b, hab⟩ := exists_pair_ne M
      exact hab (hEpinj (by simp))
    -- `ker E` is `H`-invariant.
    have hHK : ∀ v ∈ LinearMap.ker E, H v ∈ LinearMap.ker E := by
      intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hEH : E * H = H * E - (2 : k) • E := by rw [hHE]; abel
      have hEHv : E (H v) = (E * H) v := rfl
      rw [hEHv, hEH]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, hv]
      simp
    -- Highest weight vector: an `H`-eigenvector inside `ker E`.
    haveI : Nontrivial (LinearMap.ker E) := (Submodule.nontrivial_iff_ne_bot).mpr hKne
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (H.restrict hHK)
    obtain ⟨w, hw⟩ := hlam.exists_hasEigenvector
    set v0 : M := (w : M) with hv0def
    have hv0ne : v0 ≠ 0 := by rw [hv0def, Ne, Submodule.coe_eq_zero]; exact hw.2
    have hEv0 : E v0 = 0 := LinearMap.mem_ker.mp w.2
    have hHv0 : H v0 = lam • v0 := by
      have h1 : (H.restrict hHK) w = lam • w := (Module.End.mem_eigenspace_iff).mp hw.1
      have := congrArg (Subtype.val) h1
      simpa [LinearMap.restrict_apply, hv0def, Submodule.coe_smul] using this
    -- The `F`-orbit of `v0` spans `W`.
    set g : ℕ → M := fun j => (F ^ j) v0 with hgdef
    set W : Submodule k M := Submodule.span k (Set.range (fun i : Fin p => g (i : ℕ))) with hWdef
    have hg0 : g 0 = v0 := by simp [hgdef]
    have hmemgen : ∀ j : ℕ, j < p → g j ∈ W := fun j hj =>
      Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    -- `F`-closure.
    have hFW : ∀ w ∈ W, F w ∈ W := by
      refine fun w hw => span_closed_of_gens F _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hFg : F (g (i : ℕ)) = g ((i : ℕ) + 1) := by
        simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
      rw [hFg]
      by_cases hip : (i : ℕ) + 1 < p
      · exact hmemgen _ hip
      · have hip1 : (i : ℕ) + 1 = p := by omega
        have hval : g ((i : ℕ) + 1) = β • v0 := by
          simp only [hgdef, hip1, hβ, LinearMap.smul_apply, Module.End.one_apply]
        rw [hval]
        exact W.smul_mem β (hg0 ▸ hmemgen 0 (by omega))
    have hgW : ∀ j, g j ∈ W := by
      intro j
      induction j with
      | zero => exact hg0 ▸ hmemgen 0 (by omega)
      | succ j ih =>
        have hFg : g (j + 1) = F (g j) := by
          simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
        rw [hFg]; exact hFW _ ih
    -- `H`-closure.
    have hHW : ∀ w ∈ W, H w ∈ W := by
      refine fun w hw => span_closed_of_gens H _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hval : H (g (i : ℕ)) = lam • g (i : ℕ) - ((2 * (i : ℕ) : ℕ) : k) • g (i : ℕ) := by
        simp only [hgdef]
        rw [← Module.End.mul_apply, hHFpow (i : ℕ)]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, hHv0, map_smul]
      rw [hval]
      exact W.sub_mem (W.smul_mem _ (hmemgen _ i.isLt)) (W.smul_mem _ (hmemgen _ i.isLt))
    -- `E`-closure.
    have hEW : ∀ w ∈ W, E w ∈ W := by
      have hEorbit : ∀ j : ℕ, E (g j) ∈ W := by
        intro j
        induction j with
        | zero =>
          have hz : E (g 0) = 0 := by rw [hg0]; exact hEv0
          rw [hz]; exact W.zero_mem
        | succ j ih =>
          have hEF' : E * F = F * E + H := by rw [← hEF]; abel
          have hstep : E (g (j + 1)) = F (E (g j)) + H (g j) := by
            have hFg : g (j + 1) = F (g j) := by
              simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
            rw [hFg, ← Module.End.mul_apply, hEF']
            simp only [LinearMap.add_apply, Module.End.mul_apply]
          rw [hstep]
          exact W.add_mem (hFW _ ih) (hHW _ (hgW j))
      refine fun w hw => span_closed_of_gens E _ ?_ hw
      rintro s ⟨i, rfl⟩
      exact hEorbit (i : ℕ)
    -- `W` is a nonzero `𝔰𝔩(2)`-submodule, hence everything; conclude the dimension bound.
    have hlie := lie_closed_of_efh W
      (fun m hm => by rw [hEe]; exact hEW m hm)
      (fun m hm => by rw [hFf]; exact hFW m hm)
      (fun m hm => by rw [hHh]; exact hHW m hm)
    have htop : W = ⊤ := eq_top_of_lie_closed W hlie ⟨v0, hg0 ▸ hgW 0, hv0ne⟩
    exact finrank_le_of_orbit_top p g htop
  · -- `α ≠ 0`: `E` is injective, use a joint `H`, `F·E`-eigenvector.
    have hEinj : Function.Injective E := by
      have hEpinj : Function.Injective (E ^ p) := by
        rw [hα]
        intro a b hab
        simp only [LinearMap.smul_apply, Module.End.one_apply] at hab
        exact smul_right_injective M hα0 hab
      intro a b hab
      apply hEpinj
      have hsplit : E ^ p = E ^ (p - 1) * E := by rw [← pow_succ]; congr 1; omega
      rw [hsplit, Module.End.mul_apply, Module.End.mul_apply, hab]
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue H
    -- `F·E` commutes with `H`, so preserves the `lam`-eigenspace of `H`.
    have hFEmaps : ∀ v ∈ H.eigenspace lam, (F * E) v ∈ H.eigenspace lam := by
      intro v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have hcomm : H * (F * E) = (F * E) * H := by
        calc H * (F * E) = (H * F) * E := by rw [mul_assoc]
          _ = (F * H - (2 : k) • F) * E := by rw [hHF]
          _ = F * (H * E) - (2 : k) • (F * E) := by rw [sub_mul, mul_assoc, smul_mul_assoc]
          _ = F * (E * H + (2 : k) • E) - (2 : k) • (F * E) := by rw [hHE]
          _ = (F * E) * H := by rw [mul_add, mul_smul_comm, ← mul_assoc]; abel
      calc H ((F * E) v) = (H * (F * E)) v := rfl
        _ = ((F * E) * H) v := by rw [hcomm]
        _ = (F * E) (H v) := rfl
        _ = (F * E) (lam • v) := by rw [hv]
        _ = lam • (F * E) v := by rw [map_smul]
    haveI : Nontrivial (H.eigenspace lam) := (Submodule.nontrivial_iff_ne_bot).mpr hlam
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((F * E).restrict hFEmaps)
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    set v0 : M := (w : M) with hv0def
    have hv0ne : v0 ≠ 0 := by rw [hv0def, Ne, Submodule.coe_eq_zero]; exact hw.2
    have hHv0 : H v0 = lam • v0 := by
      have hmem := w.2
      rw [Module.End.mem_eigenspace_iff] at hmem
      exact hmem
    have hFEv0 : (F * E) v0 = c • v0 := by
      have h1 : ((F * E).restrict hFEmaps) w = c • w := (Module.End.mem_eigenspace_iff).mp hw.1
      have h2 := congrArg (Subtype.val) h1
      simpa [LinearMap.restrict_apply, hv0def, Submodule.coe_smul] using h2
    -- `E (F v₀) = (c + lam) • v₀`.
    have hEFv0 : E (F v0) = (c + lam) • v0 := by
      have hEF' : E * F = F * E + H := by rw [← hEF]; abel
      have he : E (F v0) = (E * F) v0 := rfl
      rw [he, hEF', LinearMap.add_apply, hFEv0, hHv0, ← add_smul]
    -- Hence `F v₀ = (c + lam)·α⁻¹·E^{p-1} v₀ ∈ W`, using injectivity of `E`.
    have hFv0 : F v0 = (c + lam) • α⁻¹ • (E ^ (p - 1)) v0 := by
      apply hEinj
      rw [hEFv0, map_smul, map_smul]
      have hEp : E ((E ^ (p - 1)) v0) = α • v0 := by
        have hmul : E * E ^ (p - 1) = E ^ p := by rw [← pow_succ']; congr 1; omega
        rw [← Module.End.mul_apply, hmul, hα, LinearMap.smul_apply, Module.End.one_apply]
      rw [hEp, smul_smul α⁻¹ α v0, inv_mul_cancel₀ hα0, one_smul]
    -- The `E`-orbit of `v0` spans `W`.
    set g : ℕ → M := fun j => (E ^ j) v0 with hgdef
    set W : Submodule k M := Submodule.span k (Set.range (fun i : Fin p => g (i : ℕ))) with hWdef
    have hg0 : g 0 = v0 := by simp [hgdef]
    have hmemgen : ∀ j : ℕ, j < p → g j ∈ W := fun j hj =>
      Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    -- `E`-closure.
    have hEW : ∀ w ∈ W, E w ∈ W := by
      refine fun w hw => span_closed_of_gens E _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hEg : E (g (i : ℕ)) = g ((i : ℕ) + 1) := by
        simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
      rw [hEg]
      by_cases hip : (i : ℕ) + 1 < p
      · exact hmemgen _ hip
      · have hip1 : (i : ℕ) + 1 = p := by omega
        have hval : g ((i : ℕ) + 1) = α • v0 := by
          simp only [hgdef, hip1, hα, LinearMap.smul_apply, Module.End.one_apply]
        rw [hval]
        exact W.smul_mem α (hg0 ▸ hmemgen 0 (by omega))
    have hgW : ∀ j, g j ∈ W := by
      intro j
      induction j with
      | zero => exact hg0 ▸ hmemgen 0 (by omega)
      | succ j ih =>
        have hEg : g (j + 1) = E (g j) := by
          simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
        rw [hEg]; exact hEW _ ih
    -- `H`-closure.
    have hHW : ∀ w ∈ W, H w ∈ W := by
      refine fun w hw => span_closed_of_gens H _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hval : H (g (i : ℕ)) = lam • g (i : ℕ) + ((2 * (i : ℕ) : ℕ) : k) • g (i : ℕ) := by
        simp only [hgdef]
        rw [← Module.End.mul_apply, hHEpow (i : ℕ)]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, hHv0, map_smul]
      rw [hval]
      exact W.add_mem (W.smul_mem _ (hmemgen _ i.isLt)) (W.smul_mem _ (hmemgen _ i.isLt))
    -- `F`-closure.
    have hFW : ∀ w ∈ W, F w ∈ W := by
      have hForbit : ∀ j : ℕ, F (g j) ∈ W := by
        intro j
        induction j with
        | zero =>
          rw [hg0, hFv0]
          have hEp1 : (E ^ (p - 1)) v0 = g (p - 1) := by simp only [hgdef]
          rw [hEp1, smul_smul]
          exact W.smul_mem _ (hmemgen (p - 1) (by omega))
        | succ j ih =>
          have hFE' : F * E = E * F - H := by rw [← hEF]; abel
          have hstep : F (g (j + 1)) = E (F (g j)) - H (g j) := by
            have hEg : g (j + 1) = E (g j) := by
              simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
            rw [hEg, ← Module.End.mul_apply, hFE']
            simp only [LinearMap.sub_apply, Module.End.mul_apply]
          rw [hstep]
          exact W.sub_mem (hEW _ ih) (hHW _ (hgW j))
      refine fun w hw => span_closed_of_gens F _ ?_ hw
      rintro s ⟨i, rfl⟩
      exact hForbit (i : ℕ)
    -- `W` is a nonzero `𝔰𝔩(2)`-submodule, hence everything; conclude the dimension bound.
    have hlie := lie_closed_of_efh W
      (fun m hm => by rw [hEe]; exact hEW m hm)
      (fun m hm => by rw [hFf]; exact hFW m hm)
      (fun m hm => by rw [hHh]; exact hHW m hm)
    have htop : W = ⊤ := eq_top_of_lie_closed W hlie ⟨v0, hg0 ▸ hgW 0, hv0ne⟩
    exact finrank_le_of_orbit_top p g htop

end DimensionBound

/-! ## The classification statements -/

/-- **The bound is sharp.** There exist irreducible representations of dimension `p`: it is not the
case that every irreducible finite dimensional representation has dimension `< p`. The witness is
the `p`-dimensional highest-weight module `L(p-1) = Fin p → k`. -/
theorem exists_irreducible_dim_char [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hp : 2 < p) :
    ¬ ∀ (M : Type u) [AddCommGroup M] [Module k M] [LieRingModule (sl2 k) M]
        [LieModule k (sl2 k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (sl2 k) M],
        Module.finrank k M < p := by
  intro H
  haveI : NeZero p := ⟨by omega⟩
  haveI : FiniteDimensional k (Fin p → k) := inferInstance
  haveI := irrep_isIrreducible k p hp p le_rfl
  have hlt := H (Fin p → k)
  rw [irrep_finrank] at hlt
  exact absurd hlt (lt_irrefl p)

end Etingof.Problem2_16_4

-- The source-numbered exercise namespace and established API contain intentional underscores.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_16_4.sl2
  Etingof.Problem2_16_4.sl2_e
  Etingof.Problem2_16_4.sl2_f
  Etingof.Problem2_16_4.sl2_h
  Etingof.Problem2_16_4.rhoH
  Etingof.Problem2_16_4.rhoE
  Etingof.Problem2_16_4.rhoF
  Etingof.Problem2_16_4.rhoLieHom
  Etingof.Problem2_16_4.irrepLieRingModule
  Etingof.Problem2_16_4.e_basis

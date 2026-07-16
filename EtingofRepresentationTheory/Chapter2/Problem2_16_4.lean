import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Problem 2.16.4: Irreducible representations of `𝔰𝔩(2)` in characteristic `p > 2`

Over an algebraically closed field `k` of characteristic `p > 2`, the irreducible finite
dimensional representations of `𝔰𝔩(2, k)` are constrained very differently from characteristic
`0` (where they are the `(n+1)`-dimensional modules `L(n)`, `n ≥ 0`, of unbounded dimension).

The central feature of the characteristic-`p` classification is the **dimension bound**: every
irreducible representation of `𝔰𝔩(2, k)` has dimension **at most `p`**, and this bound is
achieved. (The fine classification parametrizes the irreducibles by a highest weight `λ ∈ k`
together with, for the non-restricted ones, extra data; that full parametrization requires
highest-weight-module infrastructure and is deferred. Here we record the sharp dimension bound,
which is the crisp universally-true part of the answer.)

We realize `𝔰𝔩(2, k)` as Mathlib's `LieAlgebra.SpecialLinear.sl (Fin 2) k`.

The **sharpness** half — the existence of a `p`-dimensional irreducible — is proved here by
constructing the highest-weight module `L(p-1)`. The construction is a verbatim port of the
sorry-free characteristic-`0` construction in `Chapter2/Sl2Irrep.lean` to an arbitrary field:
carrier `Fin p → k`, with the same diagonal/raising/lowering formulas. The bracket relations
are ring identities valid over any commutative ring; the only characteristic-`p`-specific work
is the three nonzero-scalar facts (`natCast_inj_lt`, `natCast_ne_zero_of_lt`) that drive the
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
      show ∑ i : Fin 2, X.val i i = _; rw [Fin.sum_univ_two]
    rw [h4] at h3; exact h3
  have : X.val 1 1 = 0 - X.val 0 0 := by rw [← h2]; ring
  simp at this; exact this

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
      show (⟨(k' : ℕ) - 1, by omega⟩ : Fin d).val = (k' : ℕ) - 1 from rfl,
      show 0 < (k' : ℕ) + 1 from by omega,
      show (k' : ℕ) + 1 - 1 = (k' : ℕ) from by omega,
      show (k' : ℕ) - 1 + 1 < d from by omega,
      show (k' : ℕ) - 1 + 1 = (k' : ℕ) from by omega,
      show (k' : ℕ) < d from k'.isLt, dite_true,
      hfin_k k'.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k' : ℕ) from by omega)]
    push_cast; ring
  · -- k+1 < d, k = 0
    have hk0 : (k' : ℕ) = 0 := by omega
    simp only [he, hf, k'.isLt, dite_true, dite_false, mul_zero, sub_zero,
      show (⟨(k' : ℕ) + 1, he⟩ : Fin d).val = (k' : ℕ) + 1 from rfl,
      show 0 < (k' : ℕ) + 1 from by omega,
      show (k' : ℕ) + 1 - 1 = (k' : ℕ) from by omega,
      show (k' : ℕ) < d from k'.isLt, dite_true,
      hfin_k k'.isLt]
    simp [hk0]
  · -- k+1 ≥ d (k = d-1), k > 0
    simp only [he, hf, k'.isLt, dite_true, dite_false, mul_zero, zero_sub,
      show (⟨(k' : ℕ) - 1, by omega⟩ : Fin d).val = (k' : ℕ) - 1 from rfl,
      show (k' : ℕ) - 1 + 1 < d from by omega,
      show (k' : ℕ) - 1 + 1 = (k' : ℕ) from by omega,
      show (k' : ℕ) < d from k'.isLt, dite_true,
      hfin_k k'.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (k' : ℕ) from by omega)]
    have hkd1 : (k' : ℕ) + 1 = d := by omega
    push_cast [Nat.cast_sub (show 1 ≤ d from by omega), ← hkd1]; ring
  · -- k+1 ≥ d, k = 0 ⟹ d ≤ 1
    have hk0 : (k' : ℕ) = 0 := by omega
    have hd1 : d = 1 := by omega
    simp only [he, hf, dite_false, mul_zero, zero_sub, neg_zero]
    subst hd1; simp [hk0]

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
    simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero,
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
  push_neg at hN
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
        push_neg at hn1
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
        push_neg at hk
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

/-! ## The classification statements -/

/-- **Dimension bound.** Over an algebraically closed field of characteristic `p > 2`, every
irreducible finite dimensional representation of `𝔰𝔩(2)` has dimension at most `p`. -/
theorem finrank_irreducible_le_char [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hp : 2 < p)
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (sl2 k) M] [LieModule k (sl2 k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (sl2 k) M] :
    Module.finrank k M ≤ p :=
  sorry

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

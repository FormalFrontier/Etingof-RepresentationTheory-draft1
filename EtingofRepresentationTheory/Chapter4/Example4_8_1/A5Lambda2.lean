import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Reps

/-!
# Example 4.8.1 — `A₅`: the exterior square `Λ²(ℂ⁴)` and the integer character rows

Split out of `Example4_8_1.lean` for CI memory (issue #5852); see there for the umbrella.
Contains the antisymmetric subrepresentation `Λ²(ℂ⁴)` of `repC4 ⊗ repC4` with its character
formula, and the bridge from the integer rows of `tblA5` to the tabulated `Q5` values.
-/

namespace Etingof.Example4_8_1

open Q5

namespace A5

open Equiv CategoryTheory

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
/-! #### The exterior square `Λ²(ℂ⁴)` (genuine 6-dimensional representation)

`Λ²(ℂ⁴)` is realised as the antisymmetric subrepresentation of `repC4 ⊗ repC4`: the range of
the antisymmetriser `a = ½·(1 − β)`, where `β` is the swap of the two tensor factors.  `a` is a
projection that commutes with the diagonal `A₅`-action, so `range a` is `A₅`-invariant.  Its
character is `χ_{Λ²}(g) = ½·(χ_V(g)² − χ_V(g²))`, computed from the **swap-trace identity**
`trace(β ∘ (ρg ⊗ ρg)) = trace(ρg ∘ ρg) = χ_V(g²)`.  This 6-dimensional representation is the
carrier on which the central element `Σ_{c} ρ(c)` (a 5-cycle class sum) splits into the two
3-dimensional icosahedral representations `ℂ³₊`, `ℂ³₋`.  Character at the five class reps:
`(6, 0, -2, 1, 1)` (since `Λ²ℂ⁴ ≅ ℂ³₊ ⊕ ℂ³₋` and `φ + φ' = 1`). -/

open scoped TensorProduct

/-- Carrier of `repC4`: the sum-zero subspace of `Fin 5 → ℂ` (4-dimensional). -/
abbrev W4 : Submodule ℂ (Fin 5 → ℂ) := (S4.stdSubM (G := G) (α := Fin 5)).toSubmodule

/-- The underlying representation of `repC4` (deleted natural permutation rep on `Fin 5`). -/
def rhoV : Representation ℂ G W4 := (S4.stdSubM (G := G) (α := Fin 5)).toRepresentation

lemma trace_rhoV (g : G) : LinearMap.trace ℂ W4 (rhoV g) = repC4.character g := by
  rw [repC4, S4.stdRepM, FDRep.character, FDRep.of_ρ', rhoV]

/-- Trace of an endomorphism via a basis: `trace f = ∑ i, b.repr (f (b i)) i`. -/
private lemma trace_eq_sum_repr_diagW
    {M : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℂ M f = ∑ i, b.repr (f (b i)) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b f]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]

/-- **Swap-trace identity.** On `W ⊗ W` (finite-dimensional `W`), the trace of
`swap ∘ (A ⊗ B)` equals `trace (A ∘ B)`.  (Specialised copy of the Chapter 5 lemma
`Etingof.…FrobeniusSchurRealType.trace_comm_comp_map`, which Chapter 4 cannot import.) -/
private lemma trace_comm_comp_mapW
    {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] (A B : W →ₗ[ℂ] W) :
    LinearMap.trace ℂ (W ⊗[ℂ] W)
        ((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B)
      = LinearMap.trace ℂ W (A ∘ₗ B) := by
  classical
  set b := Module.finBasis ℂ W with hb
  rw [trace_eq_sum_repr_diagW (b.tensorProduct b)
        ((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B),
      Fintype.sum_prod_type]
  have hLHS : ∀ i j, (b.tensorProduct b).repr
        ((((TensorProduct.comm ℂ W W).toLinearMap ∘ₗ TensorProduct.map A B))
          ((b.tensorProduct b) (i, j))) (i, j)
        = b.repr (A (b i)) j * b.repr (B (b j)) i := by
    intro i j
    rw [Module.Basis.tensorProduct_apply]
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.comm_tmul, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
  simp_rw [hLHS]
  rw [trace_eq_sum_repr_diagW b (A ∘ₗ B)]
  have hRHS : ∀ i, b.repr ((A ∘ₗ B) (b i)) i
      = ∑ j, b.repr (A (b j)) i * b.repr (B (b i)) j := by
    intro i
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← Module.Basis.sum_repr b (B (b i))]
    rw [map_sum, map_sum, Finset.sum_apply']
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hRHS]
  rw [Finset.sum_comm]

/-- The swap endomorphism `β` of `W4 ⊗ W4`. -/
def beta : Module.End ℂ (W4 ⊗[ℂ] W4) := (TensorProduct.comm ℂ W4 W4).toLinearMap

/-- The antisymmetriser `a = ½·(1 − β)`, a projection onto the antisymmetric tensors. -/
def asym : Module.End ℂ (W4 ⊗[ℂ] W4) := (2⁻¹ : ℂ) • (1 - beta)

lemma beta_mul_beta : beta * beta = 1 := by
  rw [Module.End.mul_eq_comp, beta, TensorProduct.comm_comp_comm]; rfl

lemma asym_idem : IsIdempotentElem asym := by
  have hbb : (1 - beta) * (1 - beta) = 1 - beta - beta + beta * beta := by
    rw [sub_mul, mul_sub, mul_sub]; simp only [one_mul, mul_one]; abel
  rw [IsIdempotentElem, asym, smul_mul_smul_comm, hbb, beta_mul_beta]
  rw [show (1 : Module.End ℂ (W4 ⊗[ℂ] W4)) - beta - beta + 1 = (2 : ℂ) • (1 - beta) by module]
  rw [smul_smul, show (2⁻¹ * 2⁻¹ * 2 : ℂ) = 2⁻¹ by norm_num]

/-- `β` commutes with the diagonal action `ρg ⊗ ρg`. -/
lemma beta_comm (g : G) :
    beta * (rhoV.tprod rhoV) g = (rhoV.tprod rhoV) g * beta := by
  rw [Representation.tprod_apply, beta]
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul]

/-- `a` commutes with the diagonal action `ρg ⊗ ρg`. -/
lemma asym_comm (g : G) :
    asym * (rhoV.tprod rhoV) g = (rhoV.tprod rhoV) g * asym := by
  rw [asym, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, beta_comm]

/-- `Λ²(ℂ⁴)` as a subrepresentation of `repC4 ⊗ repC4`: the antisymmetric tensors. -/
def lam2Sub : Subrepresentation (rhoV.tprod rhoV) where
  toSubmodule := LinearMap.range asym
  apply_mem_toSubmodule g := by
    intro v hv
    rw [LinearMap.IsIdempotentElem.mem_range_iff asym_idem] at hv ⊢
    calc asym ((rhoV.tprod rhoV) g v)
        = (asym * (rhoV.tprod rhoV) g) v := rfl
      _ = ((rhoV.tprod rhoV) g * asym) v := by rw [asym_comm]
      _ = (rhoV.tprod rhoV) g (asym v) := rfl
      _ = (rhoV.tprod rhoV) g v := by rw [hv]

/-- `Λ²(ℂ⁴)`, the genuine 6-dimensional exterior-square representation of `A₅`. -/
def lam2 : FDRep ℂ G := FDRep.of lam2Sub.toRepresentation

/-- **Character of `Λ²(ℂ⁴)`**: `χ_{Λ²}(g) = ½·(χ_V(g)² − χ_V(g²))`. -/
lemma lam2_char_formula (g : G) :
    lam2.character g = (2⁻¹ : ℂ) * (repC4.character g ^ 2 - repC4.character (g * g)) := by
  classical
  -- the diagonal action and its restriction to the two β-eigenspaces
  set T := (rhoV.tprod rhoV) g with hT
  set N : Fin 2 → Submodule ℂ (W4 ⊗[ℂ] W4) := ![LinearMap.range asym, LinearMap.ker asym] with hN
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (zero_ne_one) huniv).mpr
      (LinearMap.IsIdempotentElem.isCompl asym_idem)
  -- `β = -1` on `range a`, `β = +1` on `ker a`
  have hbeta_range : ∀ x ∈ LinearMap.range asym, beta x = -x := by
    intro x hx
    rw [LinearMap.IsIdempotentElem.mem_range_iff asym_idem, asym, LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.one_apply] at hx
    -- hx : 2⁻¹ • (x - beta x) = x
    have h2 : x - beta x = (2 : ℂ) • x := by
      have h := congrArg (fun z : W4 ⊗[ℂ] W4 => (2 : ℂ) • z) hx
      simp only [smul_smul] at h
      rwa [show (2 : ℂ) * 2⁻¹ = 1 by norm_num, one_smul] at h
    have hb : beta x = x - (2 : ℂ) • x := by rw [eq_sub_iff_add_eq, ← h2]; abel
    rw [hb]; module
  have hbeta_ker : ∀ x ∈ LinearMap.ker asym, beta x = x := by
    intro x hx
    rw [LinearMap.mem_ker, asym, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply] at hx
    -- hx : 2⁻¹ • (x - beta x) = 0
    rw [smul_eq_zero] at hx
    rcases hx with h | h
    · norm_num at h
    · rw [sub_eq_zero] at h; exact h.symm
  -- maps-to for `T` and for `β ∘ T`
  have hfT : ∀ i, Set.MapsTo T (N i) (N i) := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · exact fun x hx => lam2Sub.apply_mem_toSubmodule g hx
    · intro x hx
      have hxk : asym x = 0 := (LinearMap.mem_ker (f := asym)).mp hx
      have hzero : asym (T x) = 0 := by
        rw [hT]
        calc asym ((rhoV.tprod rhoV) g x)
              = (asym * (rhoV.tprod rhoV) g) x := rfl
            _ = ((rhoV.tprod rhoV) g * asym) x := by rw [asym_comm]
            _ = (rhoV.tprod rhoV) g (asym x) := rfl
            _ = 0 := by rw [hxk, map_zero]
      exact (LinearMap.mem_ker (f := asym)).mpr hzero
  have hbetaT : (TensorProduct.comm ℂ W4 W4).toLinearMap ∘ₗ TensorProduct.map (rhoV g) (rhoV g)
      = beta ∘ₗ T := by rw [beta, hT, Representation.tprod_apply]
  have hfbT : ∀ i, Set.MapsTo (beta ∘ₗ T) (N i) (N i) := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro x hx
      have hbx : (beta ∘ₗ T) x = -(T x) := by
        rw [LinearMap.comp_apply, hbeta_range (T x) (hfT 0 hx)]
      rw [SetLike.mem_coe, hbx]
      exact neg_mem (hfT 0 hx)
    · intro x hx
      have hbx : (beta ∘ₗ T) x = T x := by
        rw [LinearMap.comp_apply, hbeta_ker (T x) (hfT 1 hx)]
      rw [SetLike.mem_coe, hbx]
      exact hfT 1 hx
  -- the two trace decompositions
  have htrT := LinearMap.trace_eq_sum_trace_restrict hInternal hfT
  have htrbT := LinearMap.trace_eq_sum_trace_restrict hInternal hfbT
  rw [Fin.sum_univ_two] at htrT htrbT
  -- restriction of `β ∘ T` on `range a` is `-(T restrict)`, on `ker a` is `T restrict`
  have hres0 : (beta ∘ₗ T).restrict (hfbT 0) = -(T.restrict (hfT 0)) := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    have hx : (x : W4 ⊗[ℂ] W4) ∈ N 0 := x.2
    change (beta ∘ₗ T) (x : W4 ⊗[ℂ] W4) = -(T (x : W4 ⊗[ℂ] W4))
    rw [LinearMap.comp_apply, hbeta_range (T x) (hfT 0 hx)]
  have hres1 : (beta ∘ₗ T).restrict (hfbT 1) = T.restrict (hfT 1) := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    have hx : (x : W4 ⊗[ℂ] W4) ∈ N 1 := x.2
    change (beta ∘ₗ T) (x : W4 ⊗[ℂ] W4) = T (x : W4 ⊗[ℂ] W4)
    rw [LinearMap.comp_apply, hbeta_ker (T x) (hfT 1 hx)]
  have htr_b0 : LinearMap.trace ℂ ↥(N 0) ((beta ∘ₗ T).restrict (hfbT 0))
      = -(LinearMap.trace ℂ ↥(N 0) (T.restrict (hfT 0))) := by
    rw [hres0]; exact map_neg (LinearMap.trace ℂ ↥(N 0)) (T.restrict (hfT 0))
  have htr_b1 : LinearMap.trace ℂ ↥(N 1) ((beta ∘ₗ T).restrict (hfbT 1))
      = LinearMap.trace ℂ ↥(N 1) (T.restrict (hfT 1)) := by rw [hres1]
  rw [htr_b0, htr_b1] at htrbT
  -- identify `trace T = χ_V(g)²` and `trace (β∘T) = χ_V(g²)`
  have hTtrace : LinearMap.trace ℂ (W4 ⊗[ℂ] W4) T = repC4.character g ^ 2 := by
    rw [hT, Representation.tprod_apply, LinearMap.trace_tensorProduct', trace_rhoV, sq]
  have hbTtrace : LinearMap.trace ℂ (W4 ⊗[ℂ] W4) (beta ∘ₗ T) = repC4.character (g * g) := by
    rw [← hbetaT, trace_comm_comp_mapW, ← Module.End.mul_eq_comp, ← map_mul, trace_rhoV]
  -- `lam2.character g = trace_{range a}(T restrict)`
  have hlam2 : lam2.character g = LinearMap.trace ℂ (N 0) (T.restrict (hfT 0)) := rfl
  -- solve: trace T = A + K, trace(β∘T) = -A + K ⟹ A = ½(trace T - trace(β∘T))
  rw [hTtrace] at htrT
  rw [hbTtrace] at htrbT
  rw [hlam2]
  -- htrT : χ² = A + K ; htrbT : χ(g²) = -A + K
  linear_combination (-2⁻¹ : ℂ) * htrT + (2⁻¹ : ℂ) * htrbT

/-- **Character of `Λ²(ℂ⁴)` at the five class representatives is `(6, 0, -2, 1, 1)`.**
Together with `Λ²ℂ⁴ ≅ ℂ³₊ ⊕ ℂ³₋`, this is the character `(3,0,-1,φ,φ') + (3,0,-1,φ',φ)`
(the golden-ratio entries cancel in the sum, leaving `1` since `φ + φ' = 1`). -/
lemma lam2_character (j : Fin 5) :
    lam2.character (classRepA5 j) = (![6, 0, -2, 1, 1] j : ℂ) := by
  have hf : ∀ k, S4.fixCardM (G := G) (α := Fin 5) (classRepA5 k) = ![5, 2, 1, 0, 0] k := by decide
  have hsq : ∀ k, S4.fixCardM (G := G) (α := Fin 5) (classRepA5 k * classRepA5 k)
      = ![5, 2, 5, 0, 0] k := by decide
  rw [lam2_char_formula, repC4_char, repC4_char, hf j, hsq j]
  fin_cases j <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **`Λ²(ℂ⁴)` is multiplicity-free: `dim_ℂ End_G(Λ²(ℂ⁴)) = 2`.**

By `FDRep.scalar_product_char_eq_finrank_equivariant`, the dimension of the space of
`A₅`-equivariant endomorphisms of `Λ²(ℂ⁴)` equals the character scalar product
`⟨χ_{Λ²}, χ_{Λ²}⟩ = ⅟60 · ∑_{g} χ_{Λ²}(g)·χ_{Λ²}(g⁻¹)`.  Writing `χ_{Λ²}(g) = ½·P(g)` with the
**integer** `P(g) = (fix₅(g) − 1)² − (fix₅(g²) − 1)` (from `lam2_char_formula` and `repC4_char`;
the character is real, `χ(g⁻¹) = χ(g)`), the sum is `¼·∑_g P(g)² = ¼·480 = 120`, evaluated by an
honest `decide` over the 60 elements of `A₅` (no `native_decide`).  Hence `120/60 = 2`.

Consequently `Λ²(ℂ⁴)` decomposes as a direct sum of **two distinct** irreducible constituents —
these are precisely the two 3-dimensional icosahedral representations `ℂ³₊`, `ℂ³₋`.  Because the
endomorphism algebra is only 2-dimensional, the three endomorphisms `1, Z, Z²` (for the central
`Z = Zamb` of Phase B) are linearly dependent, which is the linchpin for the minimal polynomial
`Z² − 20·Z − 400 = 0` splitting `Λ²(ℂ⁴)` into the two golden-ratio eigenspaces. -/
lemma lam2_hom_finrank : Module.finrank ℂ (lam2 ⟶ lam2) = 2 := by
  haveI : Invertible (Fintype.card G : ℂ) := by
    have h60 : Fintype.card G = 60 := by rw [← Nat.card_eq_fintype_card, card_G]
    rw [h60]; exact invertibleOfNonzero (by norm_num)
  have key := FDRep.scalar_product_char_eq_finrank_equivariant lam2 lam2
  -- Each squared character term is `¼·P(g)²` with `P(g)` the integer defined above.
  have hterm : ∀ g : G, lam2.character g * lam2.character g⁻¹
      = (4⁻¹ : ℂ) * ((((((S4.fixCardM (G := G) (α := Fin 5) g : ℤ) - 1) ^ 2
          - ((S4.fixCardM (G := G) (α := Fin 5) (g * g) : ℤ) - 1)) ^ 2 : ℤ) : ℂ)) := by
    intro g
    rw [lam2_char_formula, lam2_char_formula]
    simp only [repC4_char, S4.fixCardM_inv]
    rw [show g⁻¹ * g⁻¹ = (g * g)⁻¹ from by group, S4.fixCardM_inv]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Finset.mul_sum, ← Int.cast_sum] at key
  have hZ : ∑ g : G, ((((S4.fixCardM (G := G) (α := Fin 5) g : ℤ) - 1) ^ 2
      - ((S4.fixCardM (G := G) (α := Fin 5) (g * g) : ℤ) - 1)) ^ 2) = 480 := by decide
  rw [hZ] at key
  have h60 : Fintype.card G = 60 := by rw [← Nat.card_eq_fintype_card, card_G]
  -- `key : ⅟(card G) • (¼ · 480 : ℂ) = ↑(finrank ℂ (lam2 ⟶ lam2))`; the LHS is `2`.
  rw [invOf_eq_inv, smul_eq_mul, h60] at key
  have hval : ((60 : ℕ) : ℂ)⁻¹ * ((4⁻¹ : ℂ) * ((480 : ℤ) : ℂ)) = (2 : ℂ) := by
    push_cast; norm_num
  rw [hval] at key
  exact_mod_cast key.symm

/-! #### Integer-character helper rows: `ℂ` (row 0), `ℂ⁴` (row 3), `ℂ⁵` (row 5)

These three representations have rational (indeed integer) characters, so their character rows
are packaged in the integer helper table `tblA5` and bridged to `chiA5` via `chiA5_eq_tblA5`.
The full five-representation API (including the golden-ratio rows `ℂ³₊`, `ℂ³₋`) is assembled
below, after the golden-ratio characters are available. -/

/-- The integer character table for the three rational rows realised here (`ℂ`, `ℂ⁴`, `ℂ⁵`). -/
def tblA5 : Fin 3 → Fin 5 → ℤ :=
  ![![1,  1,  1,  1,  1],
    ![4,  1,  0, -1, -1],
    ![5, -1,  1,  0,  0]]

/-- The rows of `chiA5` realised by the three rational (integer-character) rows: `ℂ` is row 0,
`ℂ⁴` is row 3, `ℂ⁵` is row 4.  Bridges the integer helper table `tblA5` to `chiA5`. -/
def rowA5int : Fin 3 → Fin 5 := ![0, 3, 4]

lemma repTriv_character (j : Fin 5) : repTriv.character (classRepA5 j) = (tblA5 0 j : ℂ) := by
  rw [repTriv_char]
  fin_cases j <;>
    norm_num [tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma repC4_character (j : Fin 5) : repC4.character (classRepA5 j) = (tblA5 1 j : ℂ) := by
  have hf : ∀ k, S4.fixCardM (G := G) (α := Fin 5) (classRepA5 k) = ![5, 2, 1, 0, 0] k := by decide
  rw [repC4_char, hf j]
  fin_cases j <;>
    norm_num [tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` of the fixed-point counts of the conjugation action; no `native_decide`
lemma repC5_character (j : Fin 5) : repC5.character (classRepA5 j) = (tblA5 2 j : ℂ) := by
  have hf : ∀ k, S4.fixCardM (G := G) (α := Fin 6) (classRepA5 k) = ![6, 0, 2, 1, 1] k := by decide
  rw [repC5_char, hf j]
  fin_cases j <;>
    norm_num [tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-! #### Bridge to the tabulated `Q5` values of `chiA5` -/

/-- Rows `0, 3, 4` of `chiA5` are rational and equal the integer rows of `tblA5`. -/
lemma chiA5_eq_tblA5 (i : Fin 3) (j : Fin 5) :
    Q5toC (chiA5 (rowA5int i) j) = (tblA5 i j : ℂ) := by
  have him : (chiA5 (rowA5int i) j).im = 0 := by fin_cases i <;> fin_cases j <;> decide
  have hre : (chiA5 (rowA5int i) j).re = ((tblA5 i j : ℤ) : ℚ) := by
    fin_cases i <;> fin_cases j <;> decide
  rw [Q5toC, him, hre]; push_cast; ring


end

end A5

end Etingof.Example4_8_1

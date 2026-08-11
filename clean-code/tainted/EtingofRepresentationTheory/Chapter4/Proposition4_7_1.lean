import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Proposition 4.7.1: Orthogonality of Matrix Elements

Let V, W be nonisomorphic irreducible representations of G with orthonormal bases.
Define matrix elements t^V_{ij}(g) = ⟨v_i, ρ_V(g) v_j⟩.

(i) Matrix elements of nonisomorphic irreducible representations are orthogonal:
  (t^V_{ij}, t^W_{kl}) = 0 for V ≇ W.

(ii) (t^V_{ij}, t^V_{i'j'}) = δ_{ii'} δ_{jj'} / dim(V).

Thus the matrix elements of all irreducible representations form an orthogonal basis of the
space of functions F(G, ℂ) (Peter–Weyl for finite groups). That last sentence is the
content of the `Etingof.MatrixCoefficients` section below: `MatrixCoefficients.basis`
is the `Module.Basis` itself, and `Etingof.Proposition4_7_1_orthogonal_basis` is the
statement-level packaging.

## The pairing

Etingof states the orthogonality with respect to the Hermitian form
`(f, h) = |G|⁻¹ Σ_x f(x) conj(h(x))` on `F(G, ℂ)`. Parts (i) and (ii) below are proved for
a general algebraically closed `k`, so they are phrased with the bilinear convolution
pairing `⟪f, h⟫ = |G|⁻¹ Σ_g f(g) h(g⁻¹)` (`MatrixCoefficients.pairing`) instead. Over `ℂ`,
with the `v_i` an orthonormal basis for a positive-definite invariant Hermitian form, the
matrix of `ρ(g)` is unitary, so `t_{qp}(g⁻¹) = conj (t_{pq}(g))` and the two agree on
matrix coefficients up to transposing the index pair. The bilinear form is the one that
makes sense over an arbitrary `k`, and it is nondegenerate, which is all the basis
statement needs.

## Mathlib correspondence

This extends the character orthogonality (Theorem 4.5.1) to matrix elements.
Not directly in Mathlib.
-/

open FDRep CategoryTheory Representation

universe u

section SchurAverage

variable {k G : Type u} [Field k] [Group G] [Fintype G]
  [Invertible (Fintype.card G : k)]

/-- The averaged map T_f = ⅟|G| • Σ_g ρ_V(g) ∘ f ∘ ρ_W(g⁻¹) for a linear map f : W → V.
This is the projection of f into the space of G-equivariant maps Hom_G(W, V). -/
noncomputable def averagedLinHom (V W : FDRep k G) (f : (↑W : Type u) →ₗ[k] ↑V) :
    (↑W : Type u) →ₗ[k] ↑V :=
  ⅟(Fintype.card G : k) • ∑ g : G, (V.ρ g).comp (f.comp (W.ρ g⁻¹))

/-- averagedLinHom equals the averageMap on the linHom representation. -/
theorem averagedLinHom_eq_averageMap (V W : FDRep k G) (f : (↑W : Type u) →ₗ[k] ↑V) :
    averagedLinHom V W f = Representation.averageMap (Representation.linHom W.ρ V.ρ) f := by
  simp only [averagedLinHom, Representation.averageMap, GroupAlgebra.average,
    map_smul, map_sum]
  congr 1; ext g : 1
  simp [Representation.linHom_apply]

/-- The averaged map lies in the invariant subspace. -/
theorem averagedLinHom_mem_invariants (V W : FDRep k G)
    (f : (↑W : Type u) →ₗ[k] ↑V) :
    averagedLinHom V W f ∈ (Representation.linHom W.ρ V.ρ).invariants := by
  rw [averagedLinHom_eq_averageMap]
  exact Representation.averageMap_invariant _ _

/-- For non-isomorphic simple representations, the averaged map is zero. -/
theorem averagedLinHom_eq_zero [IsAlgClosed k]
    (V W : FDRep k G) [Simple V] [Simple W]
    (hVW : IsEmpty (V ≅ W))
    (f : (↑W : Type u) →ₗ[k] ↑V) :
    averagedLinHom V W f = 0 := by
  have hmem := averagedLinHom_mem_invariants V W f
  have hbot : (Representation.linHom W.ρ V.ρ).invariants = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    rw [LinearEquiv.finrank_eq
      (Representation.linHom.invariantsEquivFDRepHom W V)]
    exact CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso k
      fun i => hVW.false i.symm
  rw [hbot] at hmem
  exact hmem

/-- The sum ⅟|G| • Σ_g (M_V(g))_{ij} * (M_W(g⁻¹))_{pq} equals the (i,q) entry of
the averaged map T with the elementary map f sending basis vector p to basis vector j. -/
private theorem sum_eq_averagedLinHom_entry
    (V W : FDRep k G)
    {nV nW : ℕ}
    (bV : Module.Basis (Fin nV) k ↑V) (bW : Module.Basis (Fin nW) k ↑W)
    (i j : Fin nV) (p q : Fin nW) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix bV bV (V.ρ g)) i j *
      (LinearMap.toMatrix bW bW (W.ρ g⁻¹)) p q =
    (bV.repr (averagedLinHom V W ((bW.coord p).smulRight (bV j)) (bW q))) i := by
  set f : (↑W : Type u) →ₗ[k] (↑V : Type u) := (bW.coord p).smulRight (bV j)
  simp_rw [LinearMap.toMatrix_apply]
  have step : ∀ g : G,
      (bV.repr (V.ρ g (bV j))) i * (bW.repr (W.ρ g⁻¹ (bW q))) p =
      (bV.repr ((V.ρ g).comp (f.comp (W.ρ g⁻¹)) (bW q))) i := by
    intro g
    simp [f, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      LinearMap.comp_apply, map_smul, mul_comm]
  simp_rw [step]
  symm
  simp only [averagedLinHom, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, map_smul, map_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply]

end SchurAverage

/-- Matrix element orthogonality, part (i): for nonisomorphic irreducible representations
V, W, the inner product of any pair of matrix coefficients is zero.
(1/|G|) Σ_g (ρ_V(g))_{ij} (ρ_W(g⁻¹))_{pq} = 0 when V ≇ W.
(Etingof Proposition 4.7.1(i)) -/
theorem Etingof.Proposition4_7_1_i
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V W : FDRep k G) [Simple V] [Simple W]
    (hVW : IsEmpty (V ≅ W))
    {nV nW : ℕ}
    (bV : Module.Basis (Fin nV) k V) (bW : Module.Basis (Fin nW) k W)
    (i j : Fin nV) (p q : Fin nW) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix bV bV (V.ρ g)) i j *
      (LinearMap.toMatrix bW bW (W.ρ g⁻¹)) p q = 0 := by
  rw [sum_eq_averagedLinHom_entry V W bV bW i j p q]
  rw [averagedLinHom_eq_zero V W hVW]
  simp

/-- Matrix element orthogonality, part (ii): for an irreducible representation V,
(1/|G|) Σ_g (ρ(g))_{ij} (ρ(g⁻¹))_{pq} = δ_{iq} δ_{jp} / dim(V).
(Etingof Proposition 4.7.1(ii)) -/
theorem Etingof.Proposition4_7_1_ii
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) [Simple V]
    [Invertible (Module.finrank k (↑V : Type u) : k)]
    {n : ℕ}
    (b : Module.Basis (Fin n) k V)
    (i j p q : Fin n) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix b b (V.ρ g)) i j *
      (LinearMap.toMatrix b b (V.ρ g⁻¹)) p q =
    if i = q ∧ j = p then (⅟(Module.finrank k (↑V : Type u) : k) : k) else 0 := by
  set f : (↑V : Type u) →ₗ[k] (↑V : Type u) := (b.coord p).smulRight (b j)
  -- Step 1: Reduce to the averaged map entry
  rw [sum_eq_averagedLinHom_entry V V b b i j p q]
  -- Step 2: The invariant space of linHom V.ρ V.ρ is 1-dimensional
  have hmem := averagedLinHom_mem_invariants V V f
  have h1dim : Module.finrank k (Representation.linHom V.ρ V.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one k V
  -- LinearMap.id is in invariants (it commutes with all ρ(g))
  have hid_mem : LinearMap.id ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (V.ρ g * V.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  -- id ≠ 0 in the invariant space (since trace(id) = dim V ≠ 0)
  have hdim_ne : (Module.finrank k (↑V : Type u) : k) ≠ 0 :=
    isUnit_of_invertible _ |>.ne_zero
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro h
    have : (Module.finrank k (↑V : Type u) : k) = 0 := by
      rw [← LinearMap.trace_id (R := k) (M := (↑V : Type u)), h, map_zero]
    exact hdim_ne this
  -- Step 3: Every element of the 1-dim space is a scalar multiple of id
  obtain ⟨c, hc⟩ := ((finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) hid_ne).mp h1dim)
    ⟨averagedLinHom V V f, hmem⟩
  -- hc : c • ⟨id, ...⟩ = ⟨averagedLinHom V V f, ...⟩
  have hT_eq : averagedLinHom V V f = c • LinearMap.id := by
    have := congr_arg Subtype.val hc
    simpa using this.symm
  -- Step 4: Compute c via trace
  -- First, trace(T) = trace(f) by cyclic property
  have htrace_T : LinearMap.trace k ↑V (averagedLinHom V V f) =
      LinearMap.trace k ↑V f := by
    simp only [averagedLinHom, map_smul, map_sum]
    have trace_conj : ∀ g : G,
        LinearMap.trace k ↑V ((V.ρ g).comp (f.comp (V.ρ g⁻¹))) =
        LinearMap.trace k ↑V f := by
      intro g
      have : (V.ρ g).comp (f.comp (V.ρ g⁻¹)) = V.ρ g * f * V.ρ g⁻¹ := rfl
      rw [this, LinearMap.trace_mul_cycle]
      rw [show V.ρ g⁻¹ * V.ρ g * f = f from by
        rw [← map_mul, inv_mul_cancel, map_one, one_mul]]
    simp_rw [trace_conj, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, smul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]
  -- trace(f) = δ_{jp} (trace of rank-1 map)
  have htrace_f : LinearMap.trace k ↑V f = if j = p then 1 else 0 := by
    simp only [f, LinearMap.trace_smulRight, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
  -- trace(c • id) = c * dim(V) = trace(f) = δ_{jp}
  have hc_val : c = if j = p then ⅟(Module.finrank k (↑V : Type u) : k) else 0 := by
    have htr : (Module.finrank k (↑V : Type u) : k) * c =
        if j = p then 1 else 0 := by
      have : LinearMap.trace k ↑V (c • LinearMap.id) =
          if j = p then 1 else 0 := by
        rw [← hT_eq, htrace_T, htrace_f]
      rw [map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm] at this
      exact this
    split_ifs with hjp
    · rw [if_pos hjp] at htr
      rw [eq_comm]
      exact invOf_eq_right_inv htr
    · rw [if_neg hjp] at htr
      exact (mul_eq_zero.mp htr).resolve_left hdim_ne
  -- Step 5: Extract the matrix entry
  rw [hT_eq]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, hc_val]
  split_ifs <;> simp_all

/-!
## The matrix coefficients as a basis of `F(G, k)`

Etingof's concluding sentence — "matrix elements of irreducible representations of `G` form
an orthogonal basis of `F(G, ℂ)`" — is assembled here. Orthogonality (parts (i) and (ii)
above) gives linear independence; the sum-of-squares formula of Theorem 4.1.1 gives that
the number of matrix coefficients is exactly `|G| = dim_k F(G, k)`, which upgrades linear
independence to a basis.
-/

namespace Etingof.MatrixCoefficients

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]

section Pairing

variable [Invertible (Fintype.card G : k)]

/-- The convolution pairing `⟪f, h⟫ = |G|⁻¹ Σ_g f(g) h(g⁻¹)` on `F(G, k) = G → k`.

This is the bilinear stand-in for Etingof's Hermitian form `|G|⁻¹ Σ_x f(x) conj(h(x))`; see
the module docstring for why the two agree on matrix coefficients over `ℂ`. -/
noncomputable def pairing (f h : G → k) : k :=
  ⅟(Fintype.card G : k) • ∑ g : G, f g * h g⁻¹

omit [IsAlgClosed k] in
/-- `pairing` is symmetric: reindexing the sum by `g ↦ g⁻¹` swaps the two arguments. -/
theorem pairing_comm (f h : G → k) : pairing f h = pairing h f := by
  unfold pairing
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp [mul_comm]

/-- `pairing` as a linear functional in its first argument. -/
noncomputable def pairingRight (h : G → k) : (G → k) →ₗ[k] k where
  toFun f := pairing f h
  map_add' f₁ f₂ := by
    simp only [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c f := by
    simp only [pairing, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      ← Finset.mul_sum]
    ring

omit [IsAlgClosed k] in
@[simp]
theorem pairingRight_apply (f h : G → k) : pairingRight h f = pairing f h := rfl

end Pairing

variable {n : ℕ} {d : Fin n → ℕ}

/-- The index set for the matrix coefficients of a family `V` of representations equipped
with bases of sizes `d i`: a block index `i` together with a row and a column. -/
abbrev Index (n : ℕ) (d : Fin n → ℕ) : Type := Σ i : Fin n, Fin (d i) × Fin (d i)

/-- The matrix coefficient `t^{V i}_{p q}(g) = (ρ_{V i}(g))_{p q}`, read off in the basis
`b i`. -/
noncomputable def coeff (V : Fin n → FDRep k G) (b : ∀ i, Module.Basis (Fin (d i)) k (V i))
    (e : Index n d) : G → k :=
  fun g => LinearMap.toMatrix (b e.1) (b e.1) ((V e.1).ρ g) e.2.1 e.2.2

variable {V : Fin n → FDRep k G} {b : ∀ i, Module.Basis (Fin (d i)) k (V i)}

omit [IsAlgClosed k] [Fintype G] in
/-- `d i` is the dimension of `V i`, since `b i` is a basis indexed by `Fin (d i)`. -/
theorem finrank_eq (b : ∀ i, Module.Basis (Fin (d i)) k (V i)) (i : Fin n) :
    Module.finrank k (V i) = d i := by
  rw [Module.finrank_eq_card_basis (b i), Fintype.card_fin]

section Orthogonality

variable [Invertible (Fintype.card G : k)]

/-- **Cross-block orthogonality** (Proposition 4.7.1(i)): matrix coefficients belonging to
non-isomorphic irreducibles pair to zero. -/
theorem pairing_coeff_of_ne (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    {i i' : Fin n} (hii : i ≠ i') (p' q' : Fin (d i')) (p q : Fin (d i)) :
    pairing (coeff V b ⟨i', p', q'⟩) (coeff V b ⟨i, q, p⟩) = 0 := by
  haveI := hV i; haveI := hV i'
  have hVW : IsEmpty ((V i') ≅ (V i)) :=
    not_nonempty_iff.mp fun h => hii (hinj i i' ⟨h.some.symm⟩)
  exact Etingof.Proposition4_7_1_i (V i') (V i) hVW (b i') (b i) p' q' q p

/-- **Within-block orthogonality** (Proposition 4.7.1(ii)): `⟪t_{p'q'}, t_{qp}⟫` is
`δ_{p'p} δ_{q'q} / dim V`. -/
theorem pairing_coeff_self (hV : ∀ i, Simple (V i)) {i : Fin n} (hd : ((d i : k)) ≠ 0)
    (p' q' p q : Fin (d i)) :
    pairing (coeff V b ⟨i, p', q'⟩) (coeff V b ⟨i, q, p⟩) =
      if p' = p ∧ q' = q then ((d i : k))⁻¹ else 0 := by
  haveI := hV i
  have hfr : ((Module.finrank k (V i) : k)) = (d i : k) := by rw [finrank_eq b i]
  haveI : Invertible ((Module.finrank k (V i) : k)) :=
    invertibleOfNonzero (by rw [hfr]; exact hd)
  have hinv : (⅟(Module.finrank k (V i) : k) : k) = ((d i : k))⁻¹ :=
    invOf_eq_right_inv (by rw [hfr]; exact mul_inv_cancel₀ hd)
  have hunfold : pairing (coeff V b ⟨i, p', q'⟩) (coeff V b ⟨i, q, p⟩) =
      ⅟(Fintype.card G : k) • ∑ g : G,
        (LinearMap.toMatrix (b i) (b i) ((V i).ρ g)) p' q' *
        (LinearMap.toMatrix (b i) (b i) ((V i).ρ g⁻¹)) q p := rfl
  rw [hunfold, Etingof.Proposition4_7_1_ii (V i) (b i) p' q' q p, hinv]

end Orthogonality

section Basis

variable [Invertible (Fintype.card G : k)]

/-- The matrix coefficients of a family of pairwise non-isomorphic irreducibles are
linearly independent in `F(G, k)`.

This is exactly Proposition 4.7.1(i)+(ii): pairing a vanishing linear combination against
the transposed coefficient `t_{q₀p₀}` kills every term except the one indexed by
`⟨i₀, p₀, q₀⟩`, whose coefficient survives multiplied by the nonzero scalar
`(dim V i₀)⁻¹`. -/
theorem linearIndependent_coeff (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hd : ∀ i, ((d i : k)) ≠ 0) :
    LinearIndependent k (coeff V b) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro c hc ⟨i₀, p₀, q₀⟩
  -- Pair the vanishing combination against the transposed coefficient `t_{q₀ p₀}`.
  have h0 := congrArg (pairingRight (k := k) (coeff V b ⟨i₀, q₀, p₀⟩)) hc
  rw [map_sum, map_zero] at h0
  simp only [map_smul, smul_eq_mul, pairingRight_apply] at h0
  -- Split the sum over the sigma type into a sum over blocks.
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma] at h0
  -- Blocks other than `i₀` contribute nothing.
  rw [Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ i₀) h)] at h0
  · -- Inside block `i₀`, only the `(p₀, q₀)` term survives.
    rw [← Finset.univ_product_univ, Finset.sum_product] at h0
    rw [Finset.sum_eq_single p₀ (fun p _ hp => ?_) (fun h => absurd (Finset.mem_univ p₀) h)] at h0
    · rw [Finset.sum_eq_single q₀ (fun q _ hq => ?_) (fun h => absurd (Finset.mem_univ q₀) h)] at h0
      · rw [pairing_coeff_self hV (hd i₀) p₀ q₀ p₀ q₀, if_pos ⟨rfl, rfl⟩] at h0
        exact (mul_eq_zero.mp h0).resolve_right (inv_ne_zero (hd i₀))
      · rw [pairing_coeff_self hV (hd i₀) p₀ q p₀ q₀, if_neg (by simp [hq]), mul_zero]
    · refine Finset.sum_eq_zero fun q _ => ?_
      rw [pairing_coeff_self hV (hd i₀) p q p₀ q₀, if_neg (by simp [hp]), mul_zero]
  · refine Finset.sum_eq_zero fun pq _ => ?_
    obtain ⟨p, q⟩ := pq
    rw [pairing_coeff_of_ne hV hinj (Ne.symm hi) p q p₀ q₀, mul_zero]

/-- The number of matrix coefficients of a *complete* family of pairwise non-isomorphic
irreducibles is `|G|`, by the sum-of-squares formula of Theorem 4.1.1. -/
theorem card_index (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (b : ∀ i, Module.Basis (Fin (d i)) k (V i)) :
    Fintype.card (Index n d) = Module.finrank k (G → k) := by
  haveI : NeZero (Nat.card G : k) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact (isUnit_of_invertible _).ne_zero⟩
  rw [Module.finrank_fintype_fun_eq_card, ← sum_finrank_sq_eq_card_of_complete V hV hinj hsurj]
  simp only [Index, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  exact Finset.sum_congr rfl fun i _ => by rw [finrank_eq b i, sq]

/-- **Proposition 4.7.1, concluding statement.** The matrix coefficients of a complete set
of pairwise non-isomorphic irreducible representations of `G` form a basis of `F(G, k)`.

Orthogonality of this basis is `pairing_coeff_of_ne` and `pairing_coeff_self` (transported
along `coe_basis`); the two together are Etingof's "matrix elements of irreducible
representations of `G` form an orthogonal basis of `F(G, ℂ)`", packaged as
`Etingof.Proposition4_7_1_orthogonal_basis`. -/
noncomputable def basis (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (hd : ∀ i, ((d i : k)) ≠ 0) :
    Module.Basis (Index n d) k (G → k) :=
  basisOfLinearIndependentOfCardEqFinrank' (coeff V b)
    (linearIndependent_coeff hV hinj hd) (card_index hV hinj hsurj b)

@[simp]
theorem coe_basis (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (hd : ∀ i, ((d i : k)) ≠ 0) :
    ⇑(basis (b := b) hV hinj hsurj hd) = coeff V b :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

end Basis

end Etingof.MatrixCoefficients

/-- **Proposition 4.7.1, final statement.** For a finite group `G` over an algebraically
closed field `k` in which `|G|` is invertible and every irreducible dimension is nonzero,
the matrix elements of a complete set of pairwise non-isomorphic irreducible
representations form an *orthogonal* basis of `F(G, k) = G → k`, orthogonal with respect
to the convolution pairing `⟪f, h⟫ = |G|⁻¹ Σ_g f(g) h(g⁻¹)`.

The basis is indexed by triples `⟨i, p, q⟩` (an irreducible `V i` together with a matrix
position), the basis vector at `⟨i, p, q⟩` is `g ↦ (ρ_{V i}(g))_{p q}`, and

`⟪t^{V i'}_{p' q'}, t^{V i}_{q p}⟫ = δ_{i i'} δ_{p p'} δ_{q q'} / dim (V i)`,

which is precisely `Proposition4_7_1_i` (the `i ≠ i'` case) and `Proposition4_7_1_ii` (the
`i = i'` case). -/
theorem Etingof.Proposition4_7_1_orthogonal_basis
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    {n : ℕ} {d : Fin n → ℕ} (V : Fin n → FDRep k G)
    (b : ∀ i, Module.Basis (Fin (d i)) k (V i))
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (hd : ∀ i, ((d i : k)) ≠ 0) :
    ∃ B : Module.Basis (Σ i : Fin n, Fin (d i) × Fin (d i)) k (G → k),
      (∀ (e : Σ i : Fin n, Fin (d i) × Fin (d i)) (g : G),
        B e g = LinearMap.toMatrix (b e.1) (b e.1) ((V e.1).ρ g) e.2.1 e.2.2) ∧
      (∀ (i i' : Fin n) (p' q' : Fin (d i')) (p q : Fin (d i)),
        Etingof.MatrixCoefficients.pairing (B ⟨i', p', q'⟩) (B ⟨i, q, p⟩) =
          if h : i = i' then
            (if p' = h ▸ p ∧ q' = h ▸ q then ((d i' : k))⁻¹ else 0)
          else 0) := by
  classical
  refine ⟨Etingof.MatrixCoefficients.basis (b := b) hV hinj hsurj hd, fun e g => ?_, ?_⟩
  · rw [Etingof.MatrixCoefficients.coe_basis]; rfl
  · intro i i' p' q' p q
    rw [Etingof.MatrixCoefficients.coe_basis]
    by_cases hii : i = i'
    · subst hii
      rw [dif_pos rfl, Etingof.MatrixCoefficients.pairing_coeff_self hV (hd i) p' q' p q]
    · rw [dif_neg hii,
        Etingof.MatrixCoefficients.pairing_coeff_of_ne hV hinj hii p' q' p q]

/-- **Existence form.** Every finite group `G` over an algebraically closed field `k` of
characteristic zero admits a complete set of pairwise non-isomorphic irreducibles whose
matrix elements form an orthogonal basis of `F(G, k)`. -/
theorem Etingof.Proposition4_7_1_exists_orthogonal_basis
    (k G : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Fintype G] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G) (d : Fin n → ℕ)
      (b : ∀ i, Module.Basis (Fin (d i)) k (V i))
      (B : Module.Basis (Σ i : Fin n, Fin (d i) × Fin (d i)) k (G → k)),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      (∀ (e : Σ i : Fin n, Fin (d i) × Fin (d i)) (g : G),
        B e g = LinearMap.toMatrix (b e.1) (b e.1) ((V e.1).ρ g) e.2.1 e.2.2) ∧
      (∀ (i i' : Fin n) (p' q' : Fin (d i')) (p q : Fin (d i)),
        Etingof.MatrixCoefficients.pairing (B ⟨i', p', q'⟩) (B ⟨i, q, p⟩) =
          if h : i = i' then
            (if p' = h ▸ p ∧ q' = h ▸ q then ((d i' : k))⁻¹ else 0)
          else 0) := by
  classical
  haveI : NeZero (Nat.card G : k) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact (Nat.cast_ne_zero (R := k)).mpr Fintype.card_ne_zero⟩
  -- Take the Wedderburn column representations: their dimensions are the block sizes
  -- `D.d i`, which are positive by `IrrepDecomp.d_pos`.
  let D : IrrepDecomp k G := IrrepDecomp.mk'
  let b : ∀ i, Module.Basis (Fin (D.d i)) k (D.columnFDRep i) := fun i =>
    Module.finBasisOfFinrankEq k _ (D.finrank_columnFDRep i)
  have hd : ∀ i, ((D.d i : k)) ≠ 0 := fun i =>
    (Nat.cast_ne_zero (R := k)).mpr (D.d_pos i).ne
  obtain ⟨B, hB, horth⟩ :=
    Etingof.Proposition4_7_1_orthogonal_basis D.columnFDRep b
      D.columnFDRep_simple D.columnFDRep_injective D.columnFDRep_surjective hd
  exact ⟨D.n, D.columnFDRep, D.d, b, B, D.columnFDRep_simple, D.columnFDRep_injective,
    D.columnFDRep_surjective, hB, horth⟩

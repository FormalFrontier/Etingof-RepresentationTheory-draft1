import Mathlib

/-!
# Problem 4.12.10: Every irreducible occurs in a tensor power of a faithful representation

**Problem 4.12.10.** Let `G` be a finite group and let `V` be a complex representation of
`G` which is faithful, i.e., the corresponding map `G → GL(V)` is injective. Show that any
irreducible representation of `G` occurs inside `SⁿV` (and hence inside `V^{⊗n}`) for some
`n`.

## Formalization

We formalize the "hence inside `V^{⊗n}`" form (the symmetric-power form implies it). The
`n`-th tensor power `⨂[ℂ]^n V` carries the **diagonal representation** `diagTensorPow ρ n`,
sending `g` to `⨂ⁿ (ρ g)`. "The irreducible `W` occurs inside `V^{⊗n}`" is formalized as
the existence of a **nonzero `G`-equivariant linear map** `W → ⨂[ℂ]^n V`; since `W` is
simple, such a map is automatically injective, so `W` is isomorphic to a subrepresentation.
-/

open scoped TensorProduct

set_option linter.unusedFintypeInType false

noncomputable section

variable {k : Type*} [CommRing k] {G : Type*} [Monoid G]
  {V : Type*} [AddCommGroup V] [Module k V]

/-- The diagonal action of `G` on the `n`-th tensor power `⨂[k]^n V`, obtained from a
representation `ρ` on `V` by applying `ρ g` in each tensor factor. -/
def diagTensorPow (ρ : Representation k G V) (n : ℕ) :
    Representation k G (⨂[k]^n V) where
  toFun g := PiTensorProduct.map (fun _ : Fin n => ρ g)
  map_one' := by
    simp only [map_one]
    exact PiTensorProduct.map_id
  map_mul' g h := by
    simp only [map_mul, Module.End.mul_eq_comp]
    rw [← PiTensorProduct.map_comp]

@[simp]
theorem diagTensorPow_apply (ρ : Representation k G V) (n : ℕ) (g : G) :
    diagTensorPow ρ n g = PiTensorProduct.map (fun _ : Fin n => ρ g) := rfl

end

section TracePow

open Module

/-- The trace of the diagonal endomorphism `⨂ⁿ f` (i.e. `PiTensorProduct.map (fun _ => f)`)
on the `n`-th tensor power `⨂[k]^n V` equals `(trace f) ^ n`. -/
theorem trace_piTensorProduct_map_const
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (n : ℕ) (f : V →ₗ[k] V) :
    LinearMap.trace k (⨂[k]^n V) (PiTensorProduct.map (fun _ : Fin n => f))
      = (LinearMap.trace k V f) ^ n := by
  classical
  set D := Module.finrank k V with hD
  let b : Basis (Fin D) k V := Module.finBasis k V
  -- Compute the trace as a sum of diagonal matrix entries in the tensor-product basis.
  have key : LinearMap.trace k (⨂[k]^n V) (PiTensorProduct.map (fun _ : Fin n => f))
      = ∑ s : Fin n → Fin D, ∏ i : Fin n, (LinearMap.toMatrix b b f) (s i) (s i) := by
    rw [LinearMap.trace_eq_matrix_trace k (Basis.piTensorProduct (fun _ : Fin n => b)),
      Matrix.trace]
    apply Finset.sum_congr rfl
    intro s _
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
      PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
    apply Finset.prod_congr rfl
    intro i _
    rw [LinearMap.toMatrix_apply]
  rw [key]
  have htr : LinearMap.trace k V f = ∑ j : Fin D, (LinearMap.toMatrix b b f) j j := by
    rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.diag_apply]
  rw [htr, Finset.sum_pow', Fintype.piFinset_univ]

/-- The character of the diagonal tensor-power representation is the `n`-th power of the
character of `ρ`: `χ_{V^{⊗n}}(g) = χ_V(g) ^ n`. -/
theorem character_diagTensorPow
    {k : Type*} [Field k] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (n : ℕ) (g : G) :
    (diagTensorPow ρ n).character g = (ρ.character g) ^ n := by
  rw [Representation.character, diagTensorPow_apply, trace_piTensorProduct_map_const]
  rfl

end TracePow

/-- If `g` acts with character value equal to `dim V`, then `ρ g` is the identity. Over `ℂ`,
`ρ g` has finite order, hence is unitary for an averaged inner product; its trace equals
`dim V` (a sum of `dim V` complex numbers of modulus `1`) only when every eigenvalue is `1`,
i.e. `ρ g = 1`. -/
theorem ρ_eq_one_of_character_eq_finrank
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G)
    (h : ρ.character g = (Module.finrank ℂ V : ℂ)) :
    ρ g = 1 := by
  sorry

/-- **Problem 4.12.10.** Let `G` be a finite group with a faithful complex representation
`ρ` on `V`, and let `σ` be an irreducible complex representation on `W`. Then `W` occurs
inside `V^{⊗n}` for some `n`: there is a nonzero `G`-equivariant linear map
`W → ⨂[ℂ]^n V`. -/
theorem Etingof.Problem4_12_10 {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Function.Injective ρ)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule) :
    ∃ (n : ℕ) (φ : W →ₗ[ℂ] (⨂[ℂ]^n V)),
      φ ≠ 0 ∧ ∀ g : G, φ ∘ₗ σ g = (diagTensorPow ρ n g) ∘ₗ φ := by
  classical
  -- `Nat.card G` is invertible in `ℂ` (the group is finite and nonempty).
  have hcardℕ : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hcardℕ
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  -- `W` is nontrivial (it underlies a simple module), so `dim W ≠ 0`.
  haveI : Nontrivial W := by
    have : Nontrivial σ.asModule := hσ.nontrivial
    exact this
  have hWpos : (Module.finrank ℂ W : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (M := W)).ne'
  set d : ℂ := (Module.finrank ℂ V : ℂ) with hd
  -- Reduce to producing an `n` with a nonzero intertwiner `W → ⨂ⁿ V`.
  suffices hex : ∃ n, 0 < Module.finrank ℂ (Representation.IntertwiningMap σ (diagTensorPow ρ n)) by
    obtain ⟨n, hn⟩ := hex
    haveI : Nontrivial (Representation.IntertwiningMap σ (diagTensorPow ρ n)) :=
      Module.nontrivial_of_finrank_pos hn
    obtain ⟨T, hT⟩ := exists_ne (0 : Representation.IntertwiningMap σ (diagTensorPow ρ n))
    refine ⟨n, T.toLinearMap, ?_, fun g => T.isIntertwining' g⟩
    intro hzero
    exact hT (Representation.IntertwiningMap.ext (by rw [hzero]; rfl))
  -- Suppose no such `n` exists: then every multiplicity is `0`.
  by_contra hex
  rw [not_exists] at hex
  have hmult0 : ∀ n, Module.finrank ℂ (Representation.IntertwiningMap σ (diagTensorPow ρ n)) = 0 :=
    fun n => Nat.le_zero.mp (not_lt.mp (hex n))
  -- Multiplicity formula ⇒ the twisted power sum of characters vanishes for every `n`.
  have hsum : ∀ n, ∑ g : G, (ρ.character g) ^ n * σ.character g⁻¹ = 0 := by
    intro n
    have hmf := Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ (diagTensorPow ρ n)
    rw [hmult0 n, Nat.cast_zero] at hmf
    simp only [character_diagTensorPow] at hmf
    rcases mul_eq_zero.mp hmf with h | h
    · exact absurd (inv_eq_zero.mp h) hcard
    · exact h
  -- For any polynomial `p`, the `p`-weighted character sum vanishes.
  have hpoly : ∀ p : Polynomial ℂ, ∑ g : G, p.eval (ρ.character g) * σ.character g⁻¹ = 0 := by
    intro p
    simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hsum k, mul_zero]
  -- The polynomial `∏_{μ ≠ d} (X - μ)` over the distinct character values.
  set S : Finset ℂ := (Finset.univ.image ρ.character).erase d with hS
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
    have hne : μ ≠ d := (Finset.mem_erase.mp hμ).1
    exact sub_ne_zero.mpr fun hc => hne hc.symm
  -- Evaluate the weighted sum: only `g = 1` survives (faithfulness).
  have hval := hpoly p
  rw [Finset.sum_eq_single (1 : G)] at hval
  · -- `hval : p.eval (χ 1) * σ.character 1⁻¹ = 0`; both characters at `1` are dimensions.
    rw [inv_one, Representation.char_one, Representation.char_one, ← hd] at hval
    exact (mul_ne_zero hpd_ne hWpos) hval
  · -- Terms with `b ≠ 1` vanish because `χ b ≠ d`.
    intro b _ hb
    have hbd : ρ.character b ≠ d := by
      intro hbd
      exact hb (hρ (by rw [ρ_eq_one_of_character_eq_finrank ρ b (by rw [hbd, hd]), map_one]))
    rw [hp_eval, Finset.prod_eq_zero (i := ρ.character b), zero_mul]
    · exact Finset.mem_erase.mpr ⟨hbd, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
    · exact sub_self _
  · intro h; exact absurd (Finset.mem_univ _) h

import Mathlib

/-!
# Lemma 5.7.2: Virtual Representation to Irreducible Criterion

If `V` is a virtual representation with `(χ_V, χ_V) = 1` and `χ_V(1) > 0`,
then `V` is (the class of) an irreducible representation.

The book's proof: write `V = Σ nᵢVᵢ` over the irreducibles `Vᵢ`. By orthonormality
of irreducible characters, `(χ_V, χ_V) = Σ nᵢ²`, so `Σ nᵢ² = 1`, meaning that exactly
one `nᵢ = ±1` and the rest vanish. Since `χ_V(1) = Σ nᵢ dim(Vᵢ) > 0`, the surviving
coefficient must be `+1`, so `χ_V` is the character of the single irreducible `Vᵢ`.

## Formalization

We model the virtual representation by a finite family of pairwise non-isomorphic
simple representations `W : ι → FDRep ℂ G` together with integer coefficients
`n : ι → ℤ`. Its virtual character is `χ_V(g) = Σ i, nᵢ · χ_{W i}(g)`, the inner
product is `(χ_V, χ_V) = ⅟|G| · Σ_g χ_V(g) · χ_V(g⁻¹)` (the standard bilinear pairing
of characters, using `χ(g⁻¹)` for the conjugate as elsewhere in this project), and
`χ_V(1) = Σ i, nᵢ · dim(W i)`.

The conclusion "`V` is the class of an irreducible representation" is rendered as:
exactly one coefficient equals `1` and all others vanish, i.e. `χ_V = χ_{W i₀}` for a
single irreducible `W i₀`.

## Mathlib correspondence

Uses `FDRep.character`, `FDRep.char_orthonormal` (orthonormality of irreducible
characters), and `FDRep.char_one` (`χ(1) = dim`).
-/

open scoped Classical in
/-- A virtual representation with self inner product `1` and positive dimension at the
identity is (the class of) an irreducible representation: exactly one coefficient is `1`
and the rest are `0`. (Etingof Lemma 5.7.2) -/
theorem Etingof.Lemma5_7_2
    {G : Type} [Group G] [Fintype G] [Invertible (Fintype.card G : ℂ)]
    {ι : Type} [Fintype ι]
    (W : ι → FDRep ℂ G) [∀ i, CategoryTheory.Simple (W i)]
    (hdistinct : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (n : ι → ℤ)
    (hnorm : ⅟(Fintype.card G : ℂ) •
        ∑ g : G, (∑ i, (n i : ℂ) * (W i).character g) *
                 (∑ j, (n j : ℂ) * (W j).character g⁻¹) = 1)
    (hpos : 0 < ∑ i, n i * (Module.finrank ℂ (W i) : ℤ)) :
    ∃ i₀, n i₀ = 1 ∧ ∀ i, i ≠ i₀ → n i = 0 := by
  -- Each irreducible has positive dimension.
  have hdpos : ∀ i, 0 < Module.finrank ℂ (W i) := by
    intro i
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ (W i)) with hfr0 | hposi
    · exfalso
      haveI : Subsingleton (W i) := Module.finrank_zero_iff.mp hfr0
      have hzero : ∀ g : G, (W i).character g = 0 := fun g => by
        rw [FDRep.character, Subsingleton.elim ((W i).ρ g) 0, map_zero]
      have h1 := FDRep.char_orthonormal (W i) (W i)
      rw [if_pos ⟨CategoryTheory.Iso.refl _⟩] at h1
      simp only [hzero, zero_mul, Finset.sum_const_zero, smul_zero] at h1
      exact one_ne_zero h1.symm
    · exact hposi
  -- Orthonormality of the family: `⅟|G| · Σ_g χ_i(g) χ_j(g⁻¹) = δ_{ij}`.
  have horth : ∀ i j, ⅟(Fintype.card G : ℂ) •
      ∑ g : G, (W i).character g * (W j).character g⁻¹ = if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [FDRep.char_orthonormal (W i) (W j)]
    have hiff : Nonempty (W i ≅ W j) ↔ i = j :=
      ⟨hdistinct i j, fun h => ⟨h ▸ CategoryTheory.Iso.refl (W i)⟩⟩
    simp [hiff]
  -- Expand the inner product to `Σ i, nᵢ²`.
  have hexpand : ⅟(Fintype.card G : ℂ) •
      ∑ g : G, (∑ i, (n i : ℂ) * (W i).character g) *
               (∑ j, (n j : ℂ) * (W j).character g⁻¹) = ∑ i, (n i : ℂ) ^ 2 := by
    -- Distribute the products inside the sum over `g`.
    have hAB : ∀ g : G,
        (∑ i, (n i : ℂ) * (W i).character g) * (∑ j, (n j : ℂ) * (W j).character g⁻¹)
        = ∑ i, ∑ j, (n i : ℂ) * (n j) *
            ((W i).character g * (W j).character g⁻¹) := by
      intro g
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    -- Reorder the triple sum `g, i, j` to `i, j, g`.
    have reorder : ∀ (T : G → ι → ι → ℂ),
        (∑ g : G, ∑ i, ∑ j, T g i j) = ∑ i, ∑ j, ∑ g : G, T g i j := by
      intro T
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
    calc ⅟(Fintype.card G : ℂ) •
            ∑ g : G, (∑ i, (n i : ℂ) * (W i).character g) *
                     (∑ j, (n j : ℂ) * (W j).character g⁻¹)
        = ⅟(Fintype.card G : ℂ) • ∑ g : G, ∑ i, ∑ j,
            (n i : ℂ) * (n j) * ((W i).character g * (W j).character g⁻¹) := by
          rw [Finset.sum_congr rfl (fun g _ => hAB g)]
      _ = ⅟(Fintype.card G : ℂ) • ∑ i, ∑ j,
            (n i : ℂ) * (n j) * ∑ g : G, ((W i).character g * (W j).character g⁻¹) := by
          rw [reorder]
          refine congrArg _ (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
            (fun j _ => ?_)))
          rw [← Finset.mul_sum]
      _ = ∑ i, ∑ j, (n i : ℂ) * (n j) *
            (⅟(Fintype.card G : ℂ) • ∑ g : G, ((W i).character g * (W j).character g⁻¹)) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [smul_eq_mul, smul_eq_mul]; ring
      _ = ∑ i, ∑ j, (n i : ℂ) * (n j) * (if i = j then (1 : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [horth i j]
      _ = ∑ i, (n i : ℂ) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [mul_ite, mul_one, mul_zero]
          rw [Fintype.sum_ite_eq i (fun j => (n i : ℂ) * (n j))]
          ring
  -- Combine with the hypothesis: `Σ i, nᵢ² = 1` over ℂ, hence over ℤ.
  have hcomplex : ∑ i, (n i : ℂ) ^ 2 = 1 := by rw [← hexpand]; exact hnorm
  have hZ : ∑ i, (n i) ^ 2 = 1 := by
    have hc : ((∑ i, (n i) ^ 2 : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast; exact hcomplex
    exact_mod_cast hc
  -- Some coefficient is nonzero.
  have hne : ∃ i₀, (n i₀) ^ 2 ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : ∑ i, (n i) ^ 2 = 0 := Finset.sum_eq_zero (fun i _ => h i)
    rw [h0] at hZ; exact zero_ne_one hZ
  obtain ⟨i₀, hi0⟩ := hne
  have hi0pos : 0 < (n i₀) ^ 2 := (sq_nonneg _).lt_of_ne (Ne.symm hi0)
  -- Split the sum at `i₀`.
  have hsplit : (n i₀) ^ 2 + ∑ i ∈ Finset.univ.erase i₀, (n i) ^ 2 = 1 := by
    rw [Finset.add_sum_erase Finset.univ (fun i => (n i) ^ 2) (Finset.mem_univ i₀)]; exact hZ
  have hrest_nonneg : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, (n i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hni0sq : (n i₀) ^ 2 = 1 := by omega
  have hrest_zero : ∑ i ∈ Finset.univ.erase i₀, (n i) ^ 2 = 0 := by omega
  have hzero_rest : ∀ i ∈ Finset.univ.erase i₀, (n i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hrest_zero
  have hn_rest : ∀ i, i ≠ i₀ → n i = 0 := by
    intro i hi
    have hsq := hzero_rest i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    exact (pow_eq_zero_iff (two_ne_zero)).mp hsq
  -- The surviving coefficient is `±1`.
  have hpm : n i₀ = 1 ∨ n i₀ = -1 := by
    rw [sq] at hni0sq; exact mul_self_eq_one_iff.mp hni0sq
  -- The dimension sum reduces to the surviving term.
  have hdimsum : ∑ i, n i * (Module.finrank ℂ (W i) : ℤ)
      = n i₀ * (Module.finrank ℂ (W i₀) : ℤ) := by
    rw [← Finset.add_sum_erase Finset.univ (fun i => n i * (Module.finrank ℂ (W i) : ℤ))
      (Finset.mem_univ i₀)]
    have hz : ∑ i ∈ Finset.univ.erase i₀, n i * (Module.finrank ℂ (W i) : ℤ) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [hn_rest i (Finset.mem_erase.mp hi).1, zero_mul]
    rw [hz, add_zero]
  have hdpos₀ : 0 < (Module.finrank ℂ (W i₀) : ℤ) := by exact_mod_cast hdpos i₀
  have hprodpos : 0 < n i₀ * (Module.finrank ℂ (W i₀) : ℤ) := hdimsum ▸ hpos
  -- Positivity forces the surviving coefficient to be `+1`.
  rcases hpm with h1 | hm1
  · exact ⟨i₀, h1, hn_rest⟩
  · exfalso
    rw [hm1] at hprodpos
    nlinarith [hprodpos, hdpos₀]

import EtingofRepresentationTheory.Chapter3.Theorem3_2_2

/-!
# Theorem 3.5.4 (finiteness half): finitely many irreducibles, bounded by `dim A`

Theorem 3.5.4 (`Etingof.structure_mod_radical`) formalizes the isomorphism clause of the
book statement, but takes the finiteness of the family of irreducibles as a hypothesis
(`[Fintype ι]` plus a completeness assumption). This file discharges the two ingredients the
book uses to prove finiteness (Theorem 3.5.4, first two paragraphs):

* `Etingof.simple_finiteDimensional`: every irreducible representation is finite dimensional.
  Book: for nonzero `v ∈ V`, `Av ⊆ V` is a finite dimensional subrepresentation, and as `V`
  is irreducible with `Av ≠ 0`, `V = Av` is finite dimensional.

* `Etingof.card_irreducibles_le_finrank`: any finite family of pairwise nonisomorphic finite
  dimensional irreducibles has cardinality at most `dim A`. Book: by Theorem 3.2.2 the map
  `⊕ᵢ ρᵢ : A → ⊕ᵢ End Vᵢ` is surjective, so `r ≤ ∑ᵢ dim End Vᵢ ≤ dim A`.

Together these say `A` has only finitely many (at most `dim A`) irreducibles up to isomorphism.
-/

open Module

universe u v

/-- Every irreducible representation of a finite dimensional algebra is finite dimensional.

Book (Theorem 3.5.4, first paragraph): for any nonzero `v ∈ V`, the subrepresentation
`A • v ⊆ V` is finite dimensional (a quotient of `A`); as `V` is irreducible and `A • v ≠ 0`,
`V = A • v`, hence `V` is finite dimensional. Etingof Theorem 3.5.4. -/
theorem Etingof.simple_finiteDimensional (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [IsSimpleModule A V] :
    FiniteDimensional k V := by
  -- Pick a nonzero vector `v₀`; `V` is nontrivial because it is simple.
  haveI : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  -- `A • v₀ = span A {v₀}` is a nonzero submodule of the simple module `V`, hence `⊤`.
  have hspan : Submodule.span A {v₀} = ⊤ := by
    refine (eq_bot_or_eq_top (Submodule.span A {v₀})).resolve_left ?_
    rw [Submodule.span_singleton_eq_bot]
    exact hv₀
  -- Thus `a ↦ a • v₀ : A →ₗ[A] V` is surjective; restricting scalars to `k` keeps it surjective.
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton A V v₀) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]
    exact hspan
  -- `V` is a `k`-linear quotient of the finite dimensional `A`, hence finite dimensional.
  exact Module.Finite.of_surjective
    ((LinearMap.toSpanSingleton A V v₀).restrictScalars k) hsurj

set_option linter.unusedFintypeInType false in
/-- A finite dimensional algebra over an algebraically closed field has at most `dim A`
pairwise nonisomorphic finite dimensional irreducible representations.

Book (Theorem 3.5.4, second paragraph): by Theorem 3.2.2 the combined representation map
`⊕ᵢ ρᵢ : A → ⊕ᵢ End Vᵢ` is surjective, so
`r = card ι ≤ ∑ᵢ dim End Vᵢ = ∑ᵢ (dim Vᵢ)² ≤ dim A` (each `dim Vᵢ ≥ 1`).
Consequently `A` has only finitely many irreducibles up to isomorphism (not more than `dim A`).
Etingof Theorem 3.5.4. -/
theorem Etingof.card_irreducibles_le_finrank (k : Type*) (A : Type*) (ι : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A] [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    Fintype.card ι ≤ Module.finrank k A := by
  -- SMulCommClass needed for `Algebra.lsmul`.
  haveI : ∀ i, SMulCommClass A k (V i) := fun i =>
    { smul_comm := fun a c v => smul_algebra_smul_comm c a v }
  -- The combined representation algebra homomorphism `A → ∏ᵢ End Vᵢ`.
  let φ : A →ₐ[k] (∀ i, Module.End k (V i)) :=
    Pi.algHom k (fun i => Module.End k (V i)) (fun i => Algebra.lsmul k k (V i))
  -- It is surjective by the density theorem (Theorem 3.2.2 (ii)).
  have hφ_surj : Function.Surjective φ :=
    Etingof.density_theorem_part2 k A ι V h_noniso
  -- Surjectivity forces `dim (∏ᵢ End Vᵢ) ≤ dim A`.
  have hle : Module.finrank k (∀ i, Module.End k (V i)) ≤ Module.finrank k A :=
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hφ_surj
  -- `dim (∏ᵢ End Vᵢ) = ∑ᵢ dim (End Vᵢ)`.
  have hpi : Module.finrank k (∀ i, Module.End k (V i))
      = ∑ i, Module.finrank k (Module.End k (V i)) :=
    Module.finrank_pi_fintype k
  -- Each summand `dim (End Vᵢ) = (dim Vᵢ)² ≥ 1` since `Vᵢ` is nonzero (simple).
  have hone : ∀ i, 1 ≤ Module.finrank k (Module.End k (V i)) := by
    intro i
    have hpos : 0 < Module.finrank k (V i) := by
      have : Nontrivial (V i) := IsSimpleModule.nontrivial A (V i)
      exact Module.finrank_pos
    calc 1 = 1 * 1 := (mul_one 1).symm
      _ ≤ Module.finrank k (V i) * Module.finrank k (V i) := Nat.mul_le_mul hpos hpos
      _ = Module.finrank k (Module.End k (V i)) :=
          (Module.finrank_linearMap (R := k) (S := k) (M := V i) (N := V i)).symm
  -- `card ι = ∑ᵢ 1 ≤ ∑ᵢ dim (End Vᵢ) = dim (∏ᵢ End Vᵢ) ≤ dim A`.
  calc Fintype.card ι = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i, Module.finrank k (Module.End k (V i)) := Finset.sum_le_sum fun i _ => hone i
    _ = Module.finrank k (∀ i, Module.End k (V i)) := hpi.symm
    _ ≤ Module.finrank k A := hle

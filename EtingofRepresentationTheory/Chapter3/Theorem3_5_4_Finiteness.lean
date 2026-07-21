import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import EtingofRepresentationTheory.Chapter3.Theorem3_2_2

/-!
# Theorem 3.5.4: the finiteness clause

`Etingof.structure_mod_radical` (in `Theorem3_5_4.lean`) formalizes the *isomorphism*
clause of Theorem 3.5.4, taking the finite index type `ι` and completeness of the family
`V : ι → …` as hypotheses. This file discharges the book's *finiteness* argument (first two
paragraphs of the proof), which is what makes those hypotheses legitimate:

* `Etingof.finiteDimensional_of_isSimpleModule` — every irreducible representation of a
  finite dimensional algebra is finite dimensional. (Book: `Av ⊆ V` is a finite dimensional
  subrepresentation, and by irreducibility `V = Av`.)
* `Etingof.card_irreducibles_le_finrank` — any family of pairwise non-isomorphic
  irreducible representations has at most `dim A` members. (Book: the density map
  `⊕ᵢ ρᵢ : A → ⊕ᵢ End(Vᵢ)` is surjective, so `r ≤ ∑ᵢ dim End(Vᵢ) ≤ dim A`.)

Together these say the `[Fintype ι]` input to `structure_mod_radical` is derivable rather
than assumed: there are only finitely many (at most `dim A`) irreducibles up to isomorphism,
and each is finite dimensional. This file is additive; it does not modify
`structure_mod_radical`.
-/

open Module

/-- Every irreducible representation of a finite dimensional algebra is finite dimensional.

Book proof (Theorem 3.5.4, first paragraph): for any nonzero `v ∈ V`, the subrepresentation
`A • v` is finite dimensional (it is the image of the finite dimensional space `A` under the
`k`-linear map `a ↦ a • v`), and by irreducibility `A • v = V`, so `V` is finite dimensional.
Etingof Theorem 3.5.4 (finiteness, part 1). -/
theorem Etingof.finiteDimensional_of_isSimpleModule
    (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [IsSimpleModule A V] :
    FiniteDimensional k V := by
  -- A simple module is nontrivial, so it has a nonzero element.
  haveI : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- The `k`-linear map `a ↦ a • v : A → V`.
  let g : A →ₗ[k] V :=
    { toFun := fun a => a • v
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun r a => by simp only [RingHom.id_apply]; exact smul_assoc r a v }
  -- `A • v` (the range of `g` as an `A`-submodule) is the whole of `V` by irreducibility.
  have hv_mem : v ∈ Submodule.span A {v} := Submodule.mem_span_singleton_self v
  have hv_top : Submodule.span A {v} = ⊤ := by
    rcases eq_bot_or_eq_top (Submodule.span A {v}) with h | h
    · rw [h, Submodule.mem_bot] at hv_mem; exact absurd hv_mem hv
    · exact h
  -- Hence `g` is surjective, and `V` is a quotient of the finite dimensional space `A`.
  have hg : Function.Surjective g := by
    intro w
    have hw : w ∈ Submodule.span A {v} := by rw [hv_top]; exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨a, ha⟩ := hw
    exact ⟨a, ha⟩
  exact Module.Finite.of_surjective g hg

/-- Any family of pairwise non-isomorphic irreducible representations of a finite dimensional
algebra over an algebraically closed field has at most `dim A` members.

Book proof (Theorem 3.5.4, second paragraph): each `Vᵢ` is finite dimensional
(`finiteDimensional_of_isSimpleModule`), and by the density theorem (Theorem 3.2.2) the map
`⊕ᵢ ρᵢ : A → ∏ᵢ End(Vᵢ)` is surjective, so
`card ι = ∑ᵢ 1 ≤ ∑ᵢ dim End(Vᵢ) = dim (∏ᵢ End Vᵢ) ≤ dim A`.
This is the finiteness clause: there are at most `dim A` irreducibles up to isomorphism.
Etingof Theorem 3.5.4 (finiteness, part 2). -/
theorem Etingof.card_irreducibles_le_finrank
    (k : Type*) (A : Type*) [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [FiniteDimensional k A]
    (ι : Type*) [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    Fintype.card ι ≤ Module.finrank k A := by
  classical
  -- Each irreducible is finite dimensional (book, first paragraph).
  haveI : ∀ i, FiniteDimensional k (V i) := fun i =>
    Etingof.finiteDimensional_of_isSimpleModule k A (V i)
  -- `SMulCommClass` is needed to form `Algebra.lsmul`.
  haveI : ∀ i, SMulCommClass A k (V i) := fun i =>
    { smul_comm := fun a c v => smul_algebra_smul_comm c a v }
  -- The combined density map, surjective by Theorem 3.2.2.
  let φ : A →ₐ[k] (∀ i, Module.End k (V i)) :=
    Pi.algHom k (fun i => Module.End k (V i)) (fun i => Algebra.lsmul k k (V i))
  have hφ_surj : Function.Surjective φ :=
    Etingof.density_theorem_part2 k A ι V h_noniso
  -- A surjective `k`-linear map cannot increase `finrank`.
  have hle : Module.finrank k (∀ i, Module.End k (V i)) ≤ Module.finrank k A :=
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hφ_surj
  -- `card ι ≤ dim (∏ᵢ End Vᵢ)` since each `End Vᵢ` has dimension `(dim Vᵢ)² ≥ 1`.
  have hcard : Fintype.card ι ≤ Module.finrank k (∀ i, Module.End k (V i)) := by
    rw [Module.finrank_pi_fintype]
    haveI : ∀ i, Nontrivial (V i) := fun i => IsSimpleModule.nontrivial A (V i)
    calc Fintype.card ι = ∑ _i : ι, 1 := by simp
      _ ≤ ∑ i, Module.finrank k (Module.End k (V i)) := by
          apply Finset.sum_le_sum
          intro i _
          have hEnd : Module.finrank k (Module.End k (V i))
              = Module.finrank k (V i) * Module.finrank k (V i) :=
            Module.finrank_linearMap k k (V i) (V i)
          have hpos : 0 < Module.finrank k (V i) := Module.finrank_pos
          rw [hEnd]
          exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact le_trans hcard hle

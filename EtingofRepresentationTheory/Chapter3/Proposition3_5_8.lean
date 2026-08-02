import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import EtingofRepresentationTheory.Chapter3.Theorem3_5_4
import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import EtingofRepresentationTheory.Chapter3.Definition3_5_7

/-!
# Proposition 3.5.8: Equivalent Characterizations of Semisimple Algebras

For a finite dimensional algebra `A` over an algebraically closed field `k`, the following are
equivalent:

(1) `A` is semisimple (`Rad(A) = 0`).
(2) `∑ᵢ (dim Vᵢ)² = dim A`, where the `Vᵢ` are the irreducible representations of `A`.
(3) `A ≅ ⊕ᵢ Mat_{dᵢ}(k)` for some `dᵢ`.
(4) Any finite dimensional representation of `A` is completely reducible.
(5) `A` is a completely reducible representation of `A`.

The proof follows Etingof: `(1) ⇔ (2)` by the dimension count
`dim A - dim Rad(A) = ∑ᵢ (dim Vᵢ)²` coming from Theorem 3.5.4 (`A / Rad(A) ≅ ⊕ᵢ End Vᵢ`);
`(1) ⇒ (3)` by Wedderburn–Artin over an algebraically closed field; `(3) ⇒ (4)` because a
finite product of matrix algebras is semisimple, so all its modules are; `(4) ⇒ (5)` by
specializing to `A` itself; and `(5) ⇒ (1)` using the Artinian-ring equivalence between
`IsSemisimpleRing A` and vanishing of the radical.
-/

open Module

universe u

/-- Equivalent characterizations of semisimple algebras, stated relative to a complete set
`V : ι → Type` of pairwise nonisomorphic irreducible representations (the same data as in
Theorem 3.5.4). Etingof Proposition 3.5.8. -/
theorem Etingof.semisimple_algebra_equiv (k : Type*) (A : Type u)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (ι : Type*) [Fintype ι]
    (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (h_complete : ∀ (W : Type u) [AddCommGroup W] [Module k W] [Module A W]
      [IsScalarTower k A W] [FiniteDimensional k W] [IsSimpleModule A W],
      ∃ i, Nonempty (W ≃ₗ[A] V i)) :
    [ -- (1) A is semisimple
      Etingof.IsSemisimpleAlgebra k A,
      -- (2) ∑ᵢ (dim Vᵢ)² = dim A
      ∑ i, finrank k (V i) ^ 2 = finrank k A,
      -- (3) A ≅ ⊕ᵢ Mat_{dᵢ}(k)
      ∃ (n : ℕ) (d : Fin n → ℕ), (∀ j, NeZero (d j)) ∧
        Nonempty (A ≃ₐ[k] Π j, Matrix (Fin (d j)) (Fin (d j)) k),
      -- (4) every finite dimensional representation of A is completely reducible
      ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
        [FiniteDimensional k M], IsSemisimpleModule A M,
      -- (5) A is a completely reducible representation of A
      IsSemisimpleModule A A ].TFAE := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- Theorem 3.5.4: `A / Rad(A) ≅ ⊕ᵢ End_k(Vᵢ)`, so `dim(A/Rad) = ∑ᵢ (dim Vᵢ)²`.
  have key : finrank k (A ⧸ Etingof.Radical A) = ∑ i, finrank k (V i) ^ 2 := by
    obtain ⟨e⟩ := Etingof.structure_mod_radical k A ι V h_noniso h_complete
    calc finrank k (A ⧸ Etingof.Radical A)
        = finrank k (∀ i, End k (V i)) := e.toLinearEquiv.finrank_eq
      _ = ∑ i, finrank k (End k (V i)) := finrank_pi_fintype k
      _ = ∑ i, finrank k (V i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sq, ← finrank_linearMap (R := k) (S := k) (M := V i) (N := V i)]
  -- `dim(A/Rad) + dim Rad = dim A`, with `Rad` viewed as a `k`-submodule.
  have bridge : finrank k (A ⧸ Etingof.Radical A)
      + finrank k ((Etingof.Radical A).restrictScalars k) = finrank k A := by
    have h := Submodule.finrank_quotient_add_finrank ((Etingof.Radical A).restrictScalars k)
    rwa [(Submodule.Quotient.restrictScalarsEquiv k (Etingof.Radical A)).finrank_eq] at h
  have semisimple_bridge := Etingof.isSemisimpleAlgebra_iff_isSemisimpleRing k A
  tfae_have 1 → 2 := by
    intro h1
    -- semisimple ⇒ Rad = ⊥ ⇒ its `k`-dimension is 0 ⇒ `dim A = ∑ᵢ (dim Vᵢ)²`.
    have h1' : Etingof.Radical A = ⊥ := h1
    have : ((Etingof.Radical A).restrictScalars k) = ⊥ := by
      rw [h1', Submodule.restrictScalars_bot]
    rw [← bridge, this, finrank_bot, add_zero, key]
  tfae_have 2 → 1 := by
    intro h2
    -- `dim A = ∑ᵢ (dim Vᵢ)²` ⇒ `dim Rad = 0` ⇒ `Rad = ⊥` ⇒ semisimple.
    have hr : finrank k ((Etingof.Radical A).restrictScalars k) = 0 := by
      have := bridge
      rw [key, ← h2] at this
      omega
    have hrad : Etingof.Radical A = ⊥ := by
      rw [← Submodule.restrictScalars_eq_bot_iff (S := k)]
      exact Submodule.finrank_eq_zero.mp hr
    exact hrad
  tfae_have 1 → 3 := by
    intro h1
    haveI : IsSemisimpleRing A := h1.isSemisimpleRing
    exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k A
  tfae_have 3 → 1 := by
    rintro ⟨n, d, _, ⟨e⟩⟩
    exact semisimple_bridge.mpr e.toRingEquiv.symm.isSemisimpleRing
  tfae_have 1 → 4 := by
    intro h1 M _ _ _ _ _
    haveI : IsSemisimpleRing A := h1.isSemisimpleRing
    exact IsSemisimpleRing.isSemisimpleModule
  tfae_have 4 → 5 := fun h4 => h4 A
  tfae_have 5 → 1 := by
    intro h5
    exact Etingof.isSemisimpleAlgebra_of_isSemisimpleRing k A h5
  tfae_finish

/-! ## The zero algebra (footnote to Proposition 3.5.8)

The footnote records the degenerate case `A = 0`: the zero algebra is semisimple, although it
is not simple; every representation of it is zero, so it has no irreducible or indecomposable
representations; and it is, nevertheless, the (empty) direct sum of matrix algebras. We state
these for an arbitrary subsingleton ring `A`, the zero ring being the canonical example.

These are the `n = 0` boundary of the Wedderburn picture: condition (3) of
`Etingof.semisimple_algebra_equiv` reads `A ≅ Π (j : Fin n), Matrix (Fin (d j)) (Fin (d j)) k`,
whose `∃ n : ℕ` already permits `n = 0`, i.e. the empty product. -/

/-- A zero/subsingleton ring is semisimple (Mathlib's low-priority instance, restated for
reference). Footnote to Etingof Proposition 3.5.8. -/
theorem Etingof.subsingleton_isSemisimpleRing (A : Type*) [Ring A] [Subsingleton A] :
    IsSemisimpleRing A :=
  inferInstance

/-- The zero/subsingleton algebra is semisimple in the book's radical-vanishing sense. -/
theorem Etingof.subsingleton_isSemisimpleAlgebra (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Subsingleton A] :
    Etingof.IsSemisimpleAlgebra k A :=
  Etingof.isSemisimpleAlgebra_of_isSemisimpleRing k A (subsingleton_isSemisimpleRing A)

/-- A zero/subsingleton ring is **not** simple: simplicity forces nontriviality, contradicting
`Subsingleton`. Footnote to Etingof Proposition 3.5.8. -/
theorem Etingof.subsingleton_not_isSimpleRing (A : Type*) [Ring A] [Subsingleton A] :
    ¬ IsSimpleRing A := by
  intro h
  haveI := h
  exact false_of_nontrivial_of_subsingleton A

/-- Every unital representation of a zero/subsingleton ring is zero (a subsingleton module).
Footnote to Etingof Proposition 3.5.8. -/
theorem Etingof.subsingleton_module_of_subsingleton (A : Type*) [Ring A] [Subsingleton A]
    (M : Type*) [AddCommGroup M] [Module A M] : Subsingleton M :=
  Module.subsingleton A M

/-- A zero/subsingleton ring has no irreducible representations: an `IsSimpleModule` is
nontrivial, but every module here is subsingleton. Footnote to Etingof Proposition 3.5.8. -/
theorem Etingof.subsingleton_not_isSimpleModule (A : Type*) [Ring A] [Subsingleton A]
    (M : Type*) [AddCommGroup M] [Module A M] : ¬ IsSimpleModule A M := by
  intro h
  haveI := Module.subsingleton A M
  haveI := IsSimpleModule.nontrivial A M
  exact false_of_nontrivial_of_subsingleton M

/-- A zero/subsingleton ring has no indecomposable representations: an indecomposable module is
nontrivial, but every module here is subsingleton. Footnote to Etingof Proposition 3.5.8. -/
theorem Etingof.subsingleton_not_isIndecomposable (A : Type*) [Ring A] [Subsingleton A]
    (M : Type*) [AddCommGroup M] [Module A M] : ¬ Etingof.IsIndecomposable A M := by
  intro h
  haveI := h.1
  haveI := Module.subsingleton A M
  exact false_of_nontrivial_of_subsingleton M

/-- The zero/subsingleton algebra is the empty direct sum of matrix algebras: the concrete
`n = 0` case of condition (3) of `Etingof.semisimple_algebra_equiv`. Footnote to Etingof
Proposition 3.5.8. -/
theorem Etingof.subsingleton_algEquiv_pi_matrix (k : Type*) (A : Type*)
    [Field k] [Ring A] [Subsingleton A] [Algebra k A] :
    Nonempty (A ≃ₐ[k] Π (_ : Fin 0), Matrix (Fin 0) (Fin 0) k) :=
  ⟨{ toFun := fun _ => 0
     invFun := fun _ => 0
     left_inv := fun _ => Subsingleton.elim _ _
     right_inv := fun _ => Subsingleton.elim _ _
     map_mul' := fun _ _ => Subsingleton.elim _ _
     map_add' := fun _ _ => Subsingleton.elim _ _
     commutes' := fun _ => Subsingleton.elim _ _ }⟩

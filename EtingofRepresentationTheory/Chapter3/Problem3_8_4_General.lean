import Mathlib
import EtingofRepresentationTheory.Chapter3.Problem3_8_4_Finite
import EtingofRepresentationTheory.Chapter3.Problem3_8_4_Functoriality
import EtingofRepresentationTheory.Chapter3.Problem3_8_4_Descent

/-!
# Problem 3.8.4, the general-`L` scalar-extension theorems

This file assembles the **general field extension** case of both Problem 3.8.4(i) (base-change
isomorphism descends) and (ii) (the Noether-Deuring theorem) from the finite-extension cases
(`Problem3_8_4_Finite.lean`), the pushforward functoriality (`Problem3_8_4_Functoriality.lean`)
and the descent to a finitely generated subalgebra (`Problem3_8_4_Descent.lean`).

The reduction of an arbitrary extension `L / K` to a finite one follows the same Zariski
specialization used for part (i):

1. **Descent.** A split injection `⟨i, p⟩` of the base changes over `L ⊗[K] A` already lives over
   a finitely generated `K`-subalgebra `R ⊆ L`
   (`Descent.exists_fg_subalgebra_baseChange_directSummand`).
2. **Zariski's lemma.** `R` is `Algebra.FiniteType K`; choosing a maximal ideal `m`, the residue
   field `κ = R ⧸ m` is *finite* over `K` (`finite_of_finite_type_of_isJacobsonRing`, a field being
   a Jacobson ring).
3. **Pushforward.** Push the split injection forward along `R →ₐ[K] κ`
   (`Functoriality.nonempty_baseChange_directSummand`) to a split injection over `κ ⊗[K] A`.
4. **Finite case.** Apply `directSummand_of_baseChange_directSummand_finite` over the finite
   extension `κ / K`.
-/

open scoped TensorProduct

namespace Etingof.Problem3_8_4

variable {K A V W L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [Field L] [Algebra K L]

/-- **Problem 3.8.4(i).** If the base changes `L ⊗[K] V` and `L ⊗[K] W` are isomorphic as
`L ⊗[K] A`-modules, then `V` and `W` are already isomorphic as `A`-modules, for an arbitrary
field extension `L / K`.

Reduce to a finitely generated `K`-subalgebra `R ⊆ L` (`Descent`), specialize to a residue field
`κ = R ⧸ m` finite over `K` (Zariski's lemma), push the isomorphism forward along `R →ₐ[K] κ`
(`Functoriality.nonempty_baseChange_iso`), and finish with the finite-extension case
`iso_of_baseChange_iso_finite`. -/
theorem iso_of_baseChange_iso
    [FiniteDimensional K V] [FiniteDimensional K W]
    (h : Nonempty ((L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W))) :
    Nonempty (V ≃ₗ[A] W) := by
  obtain ⟨e⟩ := h
  -- 1. Descend the isomorphism to a finitely generated `K`-subalgebra `R ⊆ L`.
  obtain ⟨R, hFG, hiso⟩ := Descent.exists_fg_subalgebra_baseChange_iso e
  haveI : Algebra.FiniteType K ↥R := (Subalgebra.fg_iff_finiteType R).mp hFG
  -- 2. Choose a maximal ideal; the residue field `κ` is finite over `K` (Zariski's lemma).
  obtain ⟨m, _hm⟩ := Ideal.exists_maximal ↥R
  letI : Field (↥R ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (↥R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (↥R ⧸ m)
  -- 3. Push the isomorphism forward along `R →ₐ[K] κ`.
  have hiso' := Functoriality.nonempty_baseChange_iso (Ideal.Quotient.mkₐ K m) hiso
  -- 4. Apply the finite-extension case over the finite extension `κ / K`.
  exact iso_of_baseChange_iso_finite hiso'

/-- **Problem 3.8.4(ii), the Noether-Deuring theorem.** If `L ⊗[K] V` is a direct summand of
`L ⊗[K] W` as `L ⊗[K] A`-modules (a split injection `p ∘ i = id`), then `V` is a direct summand
of `W` as `A`-modules, for an arbitrary field extension `L / K`.

Reduce to a finitely generated `K`-subalgebra `R ⊆ L` (`Descent`), specialize to a residue field
`κ = R ⧸ m` finite over `K` (Zariski's lemma), push the split injection forward along `R →ₐ[K] κ`
(`Functoriality.nonempty_baseChange_directSummand`), and finish with the finite-extension case
`directSummand_of_baseChange_directSummand_finite`. -/
theorem directSummand_of_baseChange_directSummand
    [FiniteDimensional K V] [FiniteDimensional K W]
    (h : ∃ (i : (L ⊗[K] V) →ₗ[L ⊗[K] A] (L ⊗[K] W))
           (p : (L ⊗[K] W) →ₗ[L ⊗[K] A] (L ⊗[K] V)), p.comp i = LinearMap.id) :
    ∃ (i : V →ₗ[A] W) (p : W →ₗ[A] V), p.comp i = LinearMap.id := by
  obtain ⟨i, p, hpi⟩ := h
  -- 1. Descend the split injection to a finitely generated `K`-subalgebra `R ⊆ L`.
  obtain ⟨R, hFG, i', p', hpi'⟩ := Descent.exists_fg_subalgebra_baseChange_directSummand i p hpi
  haveI : Algebra.FiniteType K ↥R := (Subalgebra.fg_iff_finiteType R).mp hFG
  -- 2. Choose a maximal ideal; the residue field `κ` is finite over `K` (Zariski's lemma).
  obtain ⟨m, _hm⟩ := Ideal.exists_maximal ↥R
  letI : Field (↥R ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (↥R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (↥R ⧸ m)
  -- 3. Push the split injection forward along `R →ₐ[K] κ`.
  obtain ⟨i'', p'', hpi''⟩ :=
    Functoriality.nonempty_baseChange_directSummand (Ideal.Quotient.mkₐ K m) ⟨i', p', hpi'⟩
  -- 4. Apply the finite-extension case over the finite extension `κ / K`.
  exact directSummand_of_baseChange_directSummand_finite ⟨i'', p'', hpi''⟩

end Etingof.Problem3_8_4

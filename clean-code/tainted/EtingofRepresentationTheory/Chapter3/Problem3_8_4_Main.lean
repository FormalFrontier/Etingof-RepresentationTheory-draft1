import EtingofRepresentationTheory.Chapter3.Problem3_8_4_Finite
import EtingofRepresentationTheory.Chapter3.Problem3_8_4_Descent

/-!
# Problem 3.8.4(i): the general-`L` isomorphism descent

This file discharges the general-`L` statement of Problem 3.8.4(i), `iso_of_baseChange_iso`,
whose base-change module structure is built in `Problem3_8_4.lean`. It sits above the whole
`Problem3_8_4_*` import DAG (it consumes the finite-extension case `Problem3_8_4_Finite.lean` and
the descent step `Problem3_8_4_Descent.lean`), so it lives in its own file rather than in the base
module file, which those two import. The companion part (ii) (`directSummand_of_baseChange_directSummand`,
the Noether-Deuring theorem) lives in `Problem3_8_4_General.lean`.

## The Zariski-specialization argument (book's hint)

Part (i) follows the book's "reduce to finitely generated, then to a finite extension" route:

1. **Descend to a finitely generated subalgebra.** An `L ⊗[K] A`-linear isomorphism (resp.
   split injection) already lives over a finitely generated `K`-subalgebra `R ⊆ L`
   (`Etingof.Problem3_8_4.Descent.exists_fg_subalgebra_baseChange_iso`). Since `R` is finitely
   generated, `↥R` is a finite-type `K`-algebra.
2. **Specialize to a residue field.** Choose a maximal ideal `m ◁ ↥R`; the residue field
   `κ = ↥R ⧸ m` is a field, finitely generated as a `K`-algebra, hence **finite over `K`** by
   Zariski's lemma (`finite_of_finite_type_of_isJacobsonRing`, a field being a Jacobson ring).
3. **Push forward to `κ`.** The base-change functoriality
   (`Etingof.Problem3_8_4.Functoriality.nonempty_baseChange_iso`) pushes the `↥R ⊗[K] A`-iso
   forward along the quotient `↥R →ₐ[K] κ` to a `κ ⊗[K] A`-iso with `[FiniteDimensional K κ]`.
4. **Apply the finite case.** `Etingof.Problem3_8_4.iso_of_baseChange_iso_finite` then yields
   `V ≃ₗ[A] W`.
-/

open scoped TensorProduct

namespace Etingof.Problem3_8_4

variable {K A V W L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [Field L] [Algebra K L]

/-- **Problem 3.8.4(i).** If the base changes `L ⊗[K] V` and `L ⊗[K] W` are isomorphic as
`L ⊗[K] A`-modules, then `V` and `W` are already isomorphic as `A`-modules.

Proof (book): descend the isomorphism to a finitely generated `K`-subalgebra `R ⊆ L`
(`Descent.exists_fg_subalgebra_baseChange_iso`); specialize at a maximal ideal of `↥R` to a
residue field `κ`, which is finite over `K` by Zariski's lemma; push the isomorphism forward to
`κ` (`Functoriality.nonempty_baseChange_iso`); and finish with the finite-extension case
`iso_of_baseChange_iso_finite`. -/
theorem iso_of_baseChange_iso [FiniteDimensional K V] [FiniteDimensional K W]
    (h : Nonempty ((L ⊗[K] V) ≃ₗ[L ⊗[K] A] (L ⊗[K] W))) :
    Nonempty (V ≃ₗ[A] W) := by
  obtain ⟨e⟩ := h
  obtain ⟨R, hRfg, hR⟩ := Descent.exists_fg_subalgebra_baseChange_iso e
  haveI : Algebra.FiniteType K ↥R := (Subalgebra.fg_iff_finiteType R).mp hRfg
  obtain ⟨m, hm⟩ := Ideal.exists_maximal ↥R
  letI : Field (↥R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (↥R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m)
      (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (↥R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (↥R ⧸ m)
  have hκ := Functoriality.nonempty_baseChange_iso (V := V) (W := W)
    (Ideal.Quotient.mkₐ K m) hR
  exact iso_of_baseChange_iso_finite hκ

end Etingof.Problem3_8_4

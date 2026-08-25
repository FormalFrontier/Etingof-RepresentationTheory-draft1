import EtingofRepresentationTheory.Chapter6.Definition6_4_7
import EtingofRepresentationTheory.Chapter6.Lemma6_4_6
import EtingofRepresentationTheory.Chapter6.Theorem6_5_2

/-!
# Remark 6.4.4: Finiteness of the full root set

> There can be only finitely many roots, since all of them have to lie in some ball.

Theorem 6.5.2(a) (`Etingof.Theorem_6_5_2a_finiteness`) already bounds the *positive*
roots inside a finite ball. This file assembles the full statement of Remark 6.4.4:
the entire root set (positive **and** negative roots) is finite.

The two ingredients are:

* the negation symmetry of roots — `x` is a root iff `-x` is a root, since the Cartan
  quadratic form is even in `x` (`Etingof.IsRoot.neg`);
* Lemma 6.4.6 (`Etingof.Lemma_6_4_6`): every root is either positive (all coordinates
  `≥ 0`) or negative (all coordinates `≤ 0`).

Together these show every root is either a positive root or the negation of a positive
root, so the root set embeds in the union of the finite positive-root set with its image
under negation.
-/

namespace Etingof

/-- The root set is symmetric under negation: if `x` is a root, so is `-x`.
The Cartan quadratic form `B(x, x) = xᵀ(2·Id - adj)x` is even, so `B(-x, -x) = B(x, x)`.
(Etingof Definition 6.4.3) -/
theorem IsRoot.neg {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ} {x : Fin n → ℤ}
    (hx : Etingof.IsRoot n adj x) : Etingof.IsRoot n adj (-x) := by
  refine ⟨neg_ne_zero.mpr hx.1, ?_⟩
  rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  exact hx.2

/-- **Remark 6.4.4.** For a Dynkin diagram there are only finitely many roots.

The full root set is contained in the union of the finite set of positive roots
(`Etingof.Theorem_6_5_2a_finiteness`) with its image under negation: by Lemma 6.4.6
every root is either positive or negative, and every negative root is the negation of a
positive root (`Etingof.IsRoot.neg`).
(Etingof Remark 6.4.4) -/
theorem Remark_6_4_4_roots_finite
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : Etingof.IsDynkinDiagram n adj) :
    Set.Finite {x : Fin n → ℤ | Etingof.IsRoot n adj x} := by
  -- Positive roots are finite (Theorem 6.5.2(a)); so is their image under negation.
  have hpos : Set.Finite {d : Fin n → ℤ | Etingof.IsPositiveRoot n adj d} :=
    Etingof.Theorem_6_5_2a_finiteness hDynkin
  refine (hpos.union (hpos.image (fun d => -d))).subset ?_
  intro x hx
  have hxr : Etingof.IsRoot n adj x := hx
  rcases Etingof.Lemma_6_4_6 n adj hDynkin x hxr with hp | hn
  · -- x is a positive root
    exact Or.inl ⟨hxr, hp⟩
  · -- x is a negative root: -x is a positive root and x = -(-x)
    refine Or.inr ⟨-x, ⟨hxr.neg, fun i => ?_⟩, neg_neg x⟩
    simpa using neg_nonneg.mpr (hn i)

end Etingof

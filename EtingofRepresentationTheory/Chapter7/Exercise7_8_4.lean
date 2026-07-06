import Mathlib

/-!
# Exercise 7.8.4: Exact sequences of vector spaces split

**Exercise 7.8.4.** Show that any exact sequence of vector spaces is isomorphic to a
direct sum of complexes of the form
`0 → V → V → 0`,
where `V` stands at the places `i` and `i + 1` and the map `V → V` is the identity (in
particular, any short exact sequence of vector spaces is split). Is this true in the
category of abelian groups?

## Formalization

Being isomorphic to a direct sum of contractible complexes `0 → V →^{id} V → 0` is
equivalent to the complex being **contractible**, i.e. the identity map is
null-homotopic. We state the headline claim `Exercise7_8_4` as: for every acyclic
cochain complex of `k`-vector spaces, the identity morphism is homotopic to `0`.

We also record the "in particular" consequence `Exercise7_8_4_split` (short exact
sequences of vector spaces split) and the answer to the final question,
`Exercise7_8_4_not_abelianGroups`: over `ℤ` this fails — there is a short exact
sequence of abelian groups (e.g. `0 → ℤ →^{·2} ℤ → ℤ/2 → 0`) that does not split.
-/

open CategoryTheory

/-- Exercise 7.8.4 (main claim): every acyclic (exact) cochain complex of vector spaces
over a field `k` is contractible — its identity morphism is null-homotopic — which is
equivalent to being isomorphic to a direct sum of contractible complexes
`0 → V →^{id} V → 0`. -/
theorem Etingof.Exercise7_8_4 {k : Type*} [Field k]
    (K : CochainComplex (ModuleCat.{0} k) ℤ) (hK : K.Acyclic) :
    Nonempty (Homotopy (𝟙 K) 0) := by
  sorry

/-- Exercise 7.8.4 (in particular): any short exact sequence of `k`-vector spaces is
split. -/
theorem Etingof.Exercise7_8_4_split {k : Type*} [Field k]
    (S : ShortComplex (ModuleCat.{0} k)) (hS : S.ShortExact) :
    Nonempty S.Splitting := by
  sorry

/-- Exercise 7.8.4 (final question): the statement is **not** true in the category of
abelian groups — there is a short exact sequence of abelian groups that does not split.
-/
theorem Etingof.Exercise7_8_4_not_abelianGroups :
    ∃ S : ShortComplex (ModuleCat.{0} ℤ), S.ShortExact ∧ IsEmpty S.Splitting := by
  sorry

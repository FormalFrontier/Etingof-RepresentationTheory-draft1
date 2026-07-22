import EtingofRepresentationTheory.Chapter9.Theorem9_6_4

/-!
# Problem 9.6.5: Morita equivalence via the quasi-inverse tensor functor

Etingof Problem 9.6.5 gives the second half of the proof of the Morita equivalence
Theorem 9.6.4. Let `𝒞` be a finite abelian category over a field `k`, let `P` be a
projective generator, and let `B = (End P)ᵒᵖ`, so that `F = Hom(P, -) : 𝒞 → B\text{-fmod}`
is the functor of Theorem 9.6.4 (here `Etingof.IsProgenerator.preadditiveCoyonedaObjFG`).

The problem constructs the **quasi-inverse** `G : B\text{-fmod} → 𝒞`, `G(X) := P ⊗_B X`,
where `P ⊗_B X` is the cokernel of `ψ = a_P ⊗ Id - Id ⊗ a_X : P ⊗ B ⊗ X → P ⊗ X`, and asks:

* **(i)** `F ∘ G ≅ Id` on `B\text{-fmod}`: for every `X`, `X ≅ Hom(P, P ⊗_B X)` naturally
  (needs only that `P` is a nonzero projective object).
* **(ii)** for every `X ∈ 𝒞`, construct a natural morphism `ξ : P ⊗_B Hom(P, X) → X` and
  show it is surjective.
* **(iii)** `G ∘ F ≅ Id` on `𝒞`: applying `F` to the short exact sequence
  `0 → K → P ⊗_B Hom(P, X) → X → 0` (third map `ξ`) and using (i) forces `K = 0`, so `ξ`
  is an isomorphism. Hence `F` and `G` are quasi-inverse and are equivalences of categories.

## Statement-pass note

`F` is `hp.preadditiveCoyonedaObjFG : 𝒞 ⥤ FGModuleCat (End P)ᵐᵒᵖ` (Theorem 9.6.4) and
`B\text{-fmod}` is `FGModuleCat (End P)ᵐᵒᵖ`. We render the whole problem as the existence of
the quasi-inverse functor `G` together with the natural transformation `ξ`, bundling its three
parts:

* the natural isomorphism `G ⋙ F ≅ 𝟭` is part **(i)** (`F ∘ G ≅ Id`);
* `ξ : F ⋙ G ⟶ 𝟭 𝒞` is the natural morphism of part **(ii)**, whose components
  `ξ.app X : (P ⊗_B Hom(P, X)) → X` are epimorphisms (`Epi`, the categorical rendering of
  "surjective");
* `IsIso ξ` is the conclusion of part **(iii)** (`ξ` an isomorphism, i.e. `G ∘ F ≅ Id`).

Together these say exactly that `G` is quasi-inverse to `F`. The construction of `G` as the
tensor functor `P ⊗_B -` and all proofs are deferred (`sorry`). The hypotheses match the
book's "finite abelian category over a field `k` with a projective generator `P`", as in
`Etingof.Theorem_9_6_4`.
-/

universe u v w

open CategoryTheory

namespace Etingof.Problem965

/-- **Problem 9.6.5 (Morita equivalence via the quasi-inverse tensor functor).**

For a projective generator `P` of a finite abelian category `𝒞` over a field `k`, the functor
`F = Hom(P, -) = hp.preadditiveCoyonedaObjFG` admits a quasi-inverse `G` (the tensor functor
`X ↦ P ⊗_B X`, `B = (End P)ᵒᵖ`) together with a natural morphism `ξ : F ⋙ G ⟶ 𝟭 𝒞` such that

* **(i)** `G ⋙ F ≅ 𝟭` on `B\text{-fmod}` (`F ∘ G ≅ Id`);
* **(ii)** each component `ξ.app X : (P ⊗_B Hom(P, X)) → X` is an epimorphism (surjective);
* **(iii)** `ξ` is an isomorphism (`G ∘ F ≅ Id`).

Hence `F` and `G` are quasi-inverse equivalences of categories. (Etingof Problem 9.6.5) -/
theorem exists_quasiInverse_tensor_functor
    {k : Type w} [Field k] {C : Type u} [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] [Linear k C]
    [Etingof.IsFiniteAbelianCategoryOverField k C]
    {P : C} [hp : Etingof.IsProgenerator P] :
    ∃ (G : FGModuleCat.{v} (End P)ᵐᵒᵖ ⥤ C)
      (ξ : hp.preadditiveCoyonedaObjFG ⋙ G ⟶ 𝟭 C),
      -- (i) F ∘ G ≅ Id on B-fmod
      Nonempty (G ⋙ hp.preadditiveCoyonedaObjFG ≅ 𝟭 (FGModuleCat.{v} (End P)ᵐᵒᵖ)) ∧
      -- (ii) ξ_X : P ⊗_B Hom(P, X) → X is surjective for every X
      (∀ X : C, Epi (ξ.app X)) ∧
      -- (iii) ξ is an isomorphism, so G ∘ F ≅ Id on 𝒞
      IsIso ξ := by
  sorry

end Etingof.Problem965

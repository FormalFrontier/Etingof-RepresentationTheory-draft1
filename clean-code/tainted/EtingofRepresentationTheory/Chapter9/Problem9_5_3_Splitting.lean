import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Problem 9.5.3 (ii), step 3: `Ext¹`-vanishing forces a short exact sequence to split

This is a self-contained piece of homological algebra used in the block decomposition of
Problem 9.5.3(ii). The extension group `Ext¹(C, A)` classifies extensions of `C` by `A`; when
that group is trivial the only extension is the split one, so any short exact sequence
`0 → A → B → C → 0` with `Subsingleton (Ext¹ C A)` splits and `B ≅ A ⊞ C`.

## Proof strategy

Apply the short exact sequence to the contravariant `Ext` long exact sequence with target
`A`:
`Ext C A 0 → Ext B A 0 → Ext A A 0 →[·∘extClass] Ext C A 1`.
The connecting map `Ext A A 0 → Ext C A 1` sends the identity class `mk₀ (𝟙 A)` to
`extClass ∘ (𝟙 A) = extClass`, which is `0` because `Ext¹(C, A)` is subsingleton. Exactness at
`Ext A A 0` then produces a preimage `x₂ ∈ Ext B A 0` of `mk₀ (𝟙 A)` under precomposition with
`f`. Realizing `x₂` as a morphism `r : B ⟶ A` via the degree-`0` bijection
`Ext B A 0 ≃ (B ⟶ A)` gives `f ≫ r = 𝟙 A`, i.e. a retraction of `f`. A retraction of `f` in an
abelian (hence balanced) category yields a splitting of the short complex
(`ShortComplex.Splitting.ofExactOfRetraction`), whose induced isomorphism is `B ≅ A ⊞ C`.

## Mathlib correspondence

`Abelian.Ext` is the derived `Ext` from `Mathlib.Algebra.Category.ModuleCat.Ext.HasExt`; the long
exact sequences come from `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences` and the
splitting machinery from `Mathlib.Algebra.Homology.ShortComplex.Exact`.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof

variable {R : Type u} [Ring R] [Small.{v} R]

/-- A short exact sequence `0 → A → B → C → 0` of `R`-modules with `Ext¹(C, A)` trivial splits:
there is an isomorphism `B ≅ A ⊞ C`. -/
theorem shortExact_splits_of_ext_subsingleton
    {A B C : ModuleCat.{v} R} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
    (hSES : (ShortComplex.mk f g w).ShortExact)
    (hExt : Subsingleton (Abelian.Ext C A 1)) :
    Nonempty (B ≅ A ⊞ C) := by
  haveI := hExt
  -- Exactness of the contravariant `Ext` sequence at `Ext A A 0` gives a preimage of the
  -- identity class under precomposition with `f`, because the connecting map lands in the
  -- trivial group `Ext¹(C, A)`.
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hSES A
    (Abelian.Ext.mk₀ (𝟙 A)) (show (1 : ℕ) + 0 = 1 from rfl) (Subsingleton.elim _ 0)
  -- Realize `x₂ : Ext B A 0` as a retraction `r : B ⟶ A` with `f ≫ r = 𝟙 A`.
  have hfr : f ≫ Abelian.Ext.homEquiv₀ x₂ = 𝟙 A := by
    apply (Abelian.Ext.mk₀_bijective A A).injective
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_homEquiv₀_apply]
    exact hx₂
  -- A retraction of `f` splits the short complex; read off the biproduct isomorphism.
  exact ⟨(ShortComplex.Splitting.ofExactOfRetraction _ hSES.exact
    (Abelian.Ext.homEquiv₀ x₂) hfr hSES.epi_g).isoBinaryBiproduct⟩

end Etingof

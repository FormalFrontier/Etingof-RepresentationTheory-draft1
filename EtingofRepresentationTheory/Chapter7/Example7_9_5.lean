import Mathlib.RepresentationTheory.Maschke
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.SimpleModule.Basic
import EtingofRepresentationTheory.Chapter7.Definition7_9_4

/-!
# Example 7.9.5: Representations of Finite Groups are Semisimple

The category of representations of a finite group G over a field of characteristic
not dividing |G| (or characteristic 0) is semisimple.

## Mathlib correspondence

This is Maschke's theorem. Mathlib has `IsSemisimpleModule` and related results
in `Mathlib.RepresentationTheory.Maschke`.

We provide three statements, in increasing fidelity to the book:

* `Etingof.maschke_semisimple`: the group algebra `k[G]` is a semisimple ring;
* `Etingof.isSemisimpleCategory_moduleCat`: the bridge from a semisimple ring `R`
  to the categorical statement of Definition 7.9.4 — the module category `ModuleCat R`
  is a semisimple abelian category (every short exact sequence splits);
* `Etingof.maschke_isSemisimpleCategory`: the book's statement — the category of
  representations of `G`, i.e. the category of `k[G]`-modules, is semisimple in the
  sense of Definition 7.9.4.
-/

open CategoryTheory

/-- The category of representations of a finite group G over a field of
characteristic not dividing |G| is semisimple: the group algebra k[G] is a
semisimple ring. (Etingof Example 7.9.5)

This is Maschke's theorem, corresponding to Theorem 4.1.1(i). -/
theorem Etingof.maschke_semisimple
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    (h : IsUnit (Fintype.card G : k)) :
    IsSemisimpleRing (MonoidAlgebra k G) := by
  classical
  haveI : NeZero (Nat.card G : k) := by
    rw [neZero_iff]
    rw [Fintype.card_eq_nat_card] at h
    exact h.ne_zero
  infer_instance

/-- Bridge from a semisimple ring to the categorical notion of Definition 7.9.4:
the module category over a semisimple ring is a semisimple abelian category, i.e.
every short exact sequence of modules splits.

This is the content of "the group ring is semisimple ⟹ the category of modules is
semisimple": over a semisimple ring every module is a semisimple module, so the
range of any monomorphism is a direct summand, providing a retraction that splits
the sequence. -/
theorem Etingof.isSemisimpleCategory_moduleCat
    (R : Type*) [Ring R] [IsSemisimpleRing R] :
    Etingof.IsSemisimpleCategory (ModuleCat R) := by
  intro S hS
  -- `S.f` is a monomorphism, so its underlying linear map is injective.
  have hf : Function.Injective S.f.hom :=
    LinearMap.ker_eq_bot.mp ((ModuleCat.mono_iff_ker_eq_bot S.f).mp hS.mono_f)
  -- `S.X₂` is a semisimple module over `R`, so the range of `S.f` has a complement.
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range S.f.hom)
  -- Projection onto the range along the complement, transported back to `S.X₁`,
  -- is a linear retraction of `S.f`.
  let r : S.X₂ ⟶ S.X₁ := ModuleCat.ofHom (LinearMap.linearProjOfIsCompl q S.f.hom hf hq)
  have f_r : S.f ≫ r = 𝟙 S.X₁ := by
    apply ModuleCat.hom_ext
    ext x
    simp [r]
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction S hS.exact r f_r hS.epi_g⟩

/-- Example 7.9.5: the category of representations of a finite group `G` over a field
`k` whose characteristic does not divide `|G|` is semisimple in the sense of
Definition 7.9.4 — every short exact sequence splits.

Representations of `G` over `k` are exactly `k[G]`-modules, so the representation
category is `ModuleCat (MonoidAlgebra k G)`. By Maschke's theorem the group algebra
is a semisimple ring, and `Etingof.isSemisimpleCategory_moduleCat` then gives the
categorical statement. -/
theorem Etingof.maschke_isSemisimpleCategory
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    (h : IsUnit (Fintype.card G : k)) :
    Etingof.IsSemisimpleCategory (ModuleCat (MonoidAlgebra k G)) :=
  haveI : IsSemisimpleRing (MonoidAlgebra k G) := Etingof.maschke_semisimple k G h
  Etingof.isSemisimpleCategory_moduleCat _

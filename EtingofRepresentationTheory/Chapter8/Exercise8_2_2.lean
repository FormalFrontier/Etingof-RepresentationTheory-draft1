import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import EtingofRepresentationTheory.Chapter8.Definition8_2_1

/-!
# Exercise 8.2.2: Every module has a projective resolution

Show that any module has a projective resolution (for example, one consisting of free modules).

## Formalization notes

We phrase this for the category `ModuleCat A` of left `A`-modules over a ring `A`. A projective
resolution is `CategoryTheory.ProjectiveResolution` (Definition 8.2.1 in this development,
`Etingof.ProjectiveResolution`).

The plain existence statement `Exercise_8_2_2` asserts that every module admits a projective
resolution, following at once from Mathlib's `ProjectiveResolution.of`.

The book's parenthetical "for example, one consisting of free modules" is the substantive
content: the standard construction repeatedly covers a module by the *free* module on its
underlying set. Mathlib's generic `ProjectiveResolution.of` only records that each term is
projective — the chosen projective covers pass through the opaque `EnoughProjectives` interface
(`Classical.choice`), so their terms are *not* provably free.

We therefore build the free resolution by hand. `FreeResolutionBuilder` re-runs the abstract
`ProjectiveResolution.of` construction, but parameterised by an *explicit* choice of projective
cover `over X ↠ X` for each object; this exposes every term of the resolution as `over (…)`.
Instantiating `over` with the free module `M ↦ (M →₀ A)` then yields, for every `A`-module `M`,
a projective resolution all of whose terms are free (`Exercise_8_2_2_free`).
-/

namespace Etingof

open CategoryTheory Category Limits Projective

universe v u

/-- **Exercise 8.2.2.** Every left `A`-module has a projective resolution. -/
theorem Exercise_8_2_2 (A : Type u) [Ring A] (M : ModuleCat.{u} A) :
    Nonempty (Etingof.ProjectiveResolution M) :=
  ⟨ProjectiveResolution.of M⟩

/-!
## A resolution builder with an explicit choice of projective cover

Everything here mirrors `CategoryTheory.ProjectiveResolution.of`, with the abstract
`Projective.over`/`Projective.π` replaced by user-supplied data `over`/`π`. Because the objects of
the resolution are then literally `over (…)`, any structural property of `over` (here: freeness)
is inherited by every term.
-/
namespace FreeResolutionBuilder

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (over : C → C) (π : (X : C) → over X ⟶ X)

/-- The differential out of the chosen cover of `kernel f`, landing in the source of `f`. -/
@[reducible] noncomputable def d {X Y : C} (f : X ⟶ Y) : over (kernel f) ⟶ X :=
  π (kernel f) ≫ kernel.ι f

lemma d_comp {X Y : C} (f : X ⟶ Y) : d over π f ≫ f = 0 := by
  simp [d]

/-- The chosen cover of `kernel f` together with `d` is exact at the source of `f`
(the analogue of `CategoryTheory.exact_d_f`). -/
theorem exact_d_f [∀ X, Epi (π X)] {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (d over π f) f (d_comp over π f)).Exact := by
  let α : ShortComplex.mk (d over π f) f (d_comp over π f) ⟶
      ShortComplex.mk (kernel.ι f) f (by simp) :=
    { τ₁ := π _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_f_is_kernel
  apply kernelIsKernel

/-- The underlying chain complex of the resolution built from `over`/`π`. -/
noncomputable def ofComplex (Z : C) : ChainComplex C ℕ :=
  ChainComplex.mk' (over Z) (over (kernel (π Z))) (d over π (π Z))
    (fun f => ⟨over (kernel f), d over π f, d_comp over π f⟩)

lemma ofComplex_d_1_0 (Z : C) : (ofComplex over π Z).d 1 0 = d over π (π Z) := by
  simp [ofComplex]

lemma ofComplex_exactAt_succ [∀ X, Epi (π X)] (Z : C) (n : ℕ) :
    (ofComplex over π Z).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofComplex,
    ChainComplex.mk', ChainComplex.mk, ChainComplex.of_d]
  match n with
  | 0 => apply exact_d_f
  | n + 1 => apply exact_d_f

lemma projective_ofComplex_X [∀ X, Projective (over X)] (Z : C) (n : ℕ) :
    Projective ((ofComplex over π Z).X n) := by
  obtain (_ | _ | _ | n) := n <;> exact (inferInstance : Projective (over _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The projective resolution built from the explicit covers `over`/`π`. -/
noncomputable def of [∀ X, Projective (over X)] [∀ X, Epi (π X)] (Z : C) :
    ProjectiveResolution Z where
  complex := ofComplex over π Z
  projective := projective_ofComplex_X over π Z
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨π Z, by
    rw [ofComplex_d_1_0, assoc, kernel.condition, comp_zero]⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨exact_d_f over π (π Z), by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [ofComplex]) (by simp)
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt']
      · apply ofComplex_exactAt_succ
      · apply ChainComplex.exactAt_succ_single_obj⟩

/-- Every term of `FreeResolutionBuilder.of` is one of the chosen covers `over (…)`. -/
lemma of_complex_X [∀ X, Projective (over X)] [∀ X, Epi (π X)] (Z : C) (n : ℕ) :
    ∃ Y : C, (of over π Z).complex.X n = over Y := by
  obtain (_ | _ | _ | n) := n
  · exact ⟨Z, rfl⟩
  · exact ⟨kernel (π Z), rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end FreeResolutionBuilder

/-!
## The free resolution over an arbitrary ring
-/
namespace FreeResolution

variable {A : Type u} [Ring A]

/-- The free `A`-module on the underlying set of `M`, as the chosen projective cover. -/
noncomputable def freeOver (M : ModuleCat.{u} A) : ModuleCat.{u} A := ModuleCat.of A (M →₀ A)

/-- The standard basis of `freeOver M`, indexed by the underlying set of `M`. -/
noncomputable def freeBasis (M : ModuleCat.{u} A) : Module.Basis M A (freeOver M) :=
  Finsupp.basisSingleOne

instance freeOver_free (M : ModuleCat.{u} A) : Module.Free A (freeOver M) :=
  Module.Free.of_basis (freeBasis M)

instance freeOver_projective (M : ModuleCat.{u} A) : Projective (freeOver M) :=
  ModuleCat.projective_of_free (freeBasis M)

/-- The canonical epimorphism `freeOver M ↠ M`, sending the generator `single m 1` to `m`. -/
noncomputable def freeπ (M : ModuleCat.{u} A) : freeOver M ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination A id)

instance freeπ_epi (M : ModuleCat.{u} A) : Epi (freeπ M) := by
  rw [ModuleCat.epi_iff_surjective]
  intro m
  refine ⟨Finsupp.single m 1, ?_⟩
  change (Finsupp.linearCombination A id) (Finsupp.single m 1) = m
  rw [Finsupp.linearCombination_single, one_smul, id_eq]

/-- The free resolution of an `A`-module `M`: a projective resolution all of whose terms are
free. -/
noncomputable def resolution (M : ModuleCat.{u} A) : Etingof.ProjectiveResolution M :=
  FreeResolutionBuilder.of freeOver freeπ M

instance resolution_free (M : ModuleCat.{u} A) (n : ℕ) :
    Module.Free A ((resolution M).complex.X n) := by
  obtain ⟨Y, hY⟩ := FreeResolutionBuilder.of_complex_X freeOver freeπ M n
  rw [resolution, hY]
  infer_instance

end FreeResolution

/-- **Exercise 8.2.2, free form.** Every left `A`-module admits a projective resolution all of
whose terms are free `A`-modules — the construction the book suggests ("for example, one
consisting of free modules"). -/
theorem Exercise_8_2_2_free (A : Type u) [Ring A] (M : ModuleCat.{u} A) :
    ∃ P : Etingof.ProjectiveResolution M, ∀ n, Module.Free A (P.complex.X n) :=
  ⟨FreeResolution.resolution M, fun n => FreeResolution.resolution_free M n⟩

end Etingof

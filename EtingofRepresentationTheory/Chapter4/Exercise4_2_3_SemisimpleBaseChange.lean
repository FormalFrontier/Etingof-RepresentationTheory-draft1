import Mathlib
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3

/-!
# Base change of a semisimple algebra can only increase the number of simple modules

This file supplies the **mathematical crux** of the separability-free base-change
monotonicity `#(simple k[G]) ≤ #(simple K[G])` (parent #6127 / #6098). Because we reduce
to the semisimple quotient `k[G]/rad` first, we never need semisimplicity of `K ⊗_k M`
for a general module `M` (which fails for an inseparable `K/k`). Only base change of the
already-semisimple algebra is needed, and *that* count inequality holds with **no
separability hypothesis**:

```
Nat.card (SimpleModuleClasses A) ≤ Nat.card (SimpleModuleClasses (K ⊗[k] A))
```

for a finite-dimensional **semisimple** `k`-algebra `A` and any field extension `K ⊇ k`.

## Route (no separability required)

By Artin–Wedderburn, `A ≅ ∏ i, Matrix (Fin (d i)) (Fin (d i)) (D i)` for division rings
`D i`, so `#(simple A) = |ι|` (one simple per matrix factor). Base change distributes:
`K ⊗ A ≅ ∏ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗ D i)`, and each `K ⊗ D i` is a nonzero
finite-dimensional `K`-algebra, hence has at least one simple module. So
`#(simple (K ⊗ A)) = Σ i, #(simple (K ⊗ D i)) ≥ |ι| = #(simple A)`.

The count is assembled from four reusable building blocks:

* `simpleModuleClassesCongr` — transport iso-classes of simple modules across an
  equivalence of module categories (proved here).
* `simpleModuleClassesPiEquiv` — the simple modules of a finite product of rings are the
  disjoint union of the simple modules of the factors (deferred; see the sub-issue).
* `simpleModuleClassesMatrixEquiv` — Morita: a matrix ring has the same simple count as
  its base ring (proved here from `ModuleCat.matrixEquivalence`).
* `nonempty_simpleModuleClasses` / `subsingleton_simpleModuleClasses_divisionRing` —
  existence and uniqueness of simple modules over nonzero finite-dimensional algebras and
  over division rings (proved here).
-/

open CategoryTheory

open scoped TensorProduct

namespace Etingof

universe u

attribute [local instance] CategoryTheory.isIsomorphicSetoid

/-- **Transport of simple iso-classes.** An equivalence of module categories
`E : ModuleCat R ≌ ModuleCat S` induces a bijection between the isomorphism classes of
simple `R`-modules and simple `S`-modules: it restricts to an equivalence of the full
subcategories of simple objects (`simpleProp_iff_of_equivalence`), which descends to
iso-classes by `isoClassesEquivOfEquivalence`. -/
noncomputable def simpleModuleClassesCongr {R S : Type u} [Ring R] [Ring S]
    (E : ModuleCat.{u} R ≌ ModuleCat.{u} S) :
    SimpleModuleClasses.{u} R ≃ SimpleModuleClasses.{u} S :=
  isoClassesEquivOfEquivalence
    (Equivalence.congrFullSubcategory E
      (P := simpleProp (ModuleCat.{u} R)) (Q := simpleProp (ModuleCat.{u} S))
      (funext fun X => propext (simpleProp_iff_of_equivalence E X)))

/-- **Transport of simple iso-classes along a ring isomorphism.** A ring isomorphism
`f : R ≃+* S` induces a bijection of iso-classes of simple modules, via restriction of scalars. -/
noncomputable def simpleModuleClassesCongrRingEquiv {R S : Type u} [Ring R] [Ring S]
    (f : R ≃+* S) : SimpleModuleClasses.{u} R ≃ SimpleModuleClasses.{u} S :=
  simpleModuleClassesCongr (ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm)

/-- **Morita invariance of the simple count for matrix rings.** A matrix ring
`Matrix (Fin m) (Fin m) R` (with `m ≠ 0`) has the same number of iso-classes of simple modules
as `R`, via `ModuleCat.matrixEquivalence`. -/
noncomputable def simpleModuleClassesMatrixEquiv {R : Type u} [Ring R] (m : ℕ) [NeZero m] :
    SimpleModuleClasses.{u} (Matrix (Fin m) (Fin m) R) ≃ SimpleModuleClasses.{u} R :=
  (simpleModuleClassesCongr
    (ModuleCat.matrixEquivalence R (⟨0, Nat.pos_of_neZero m⟩ : Fin m))).symm

/-- **Existence of a simple module.** A nonzero finite-dimensional algebra over a field has
at least one iso-class of simple modules: it is Artinian, so the regular module has a simple
submodule. -/
theorem nonempty_simpleModuleClasses (k : Type u) {B : Type u} [Field k] [Ring B]
    [Nontrivial B] [Algebra k B] [Module.Finite k B] :
    Nonempty (SimpleModuleClasses.{u} B) := by
  haveI : IsArtinianRing B := isArtinian_of_tower k inferInstance
  haveI : IsAtomic (Submodule B B) := isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf
  obtain ⟨m, hm⟩ : ∃ m : Submodule B B, IsSimpleModule B m := by
    simpa only [isSimpleModule_iff_isAtom] using IsAtomic.exists_atom (Submodule B B)
  haveI := hm
  haveI : Simple (ModuleCat.of B (m : Type u)) := inferInstance
  exact ⟨Quotient.mk _ ⟨ModuleCat.of B (m : Type u), this⟩⟩

/-- **Uniqueness of the simple module over a division ring.** Every simple module over a
division ring `D` is isomorphic to `D ⧸ ⊥` (the only maximal left ideal is `⊥`), so there is at
most one iso-class. -/
theorem subsingleton_simpleModuleClasses_divisionRing (D : Type u) [DivisionRing D] :
    Subsingleton (SimpleModuleClasses.{u} D) := by
  -- A simple `D`-module is `≃ₗ D ⧸ I` for a maximal `I`; over a division ring `I = ⊥`.
  have key : ∀ (M : Type u) [AddCommGroup M] [Module D M] [IsSimpleModule D M],
      Nonempty (M ≃ₗ[D] (D ⧸ (⊥ : Ideal D))) := by
    intro M _ _ _
    obtain ⟨I, hmax, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := D) (M := M)).mp ‹_›
    have hI : I = ⊥ := (IsSimpleOrder.eq_bot_or_eq_top I).resolve_right hmax.ne_top
    exact ⟨hI ▸ e⟩
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | _ P =>
  induction b using Quotient.inductionOn with
  | _ Q =>
  haveI : Simple P.obj := P.property
  haveI : Simple Q.obj := Q.property
  haveI : IsSimpleModule D (P.obj : ModuleCat.{u} D) := inferInstance
  haveI : IsSimpleModule D (Q.obj : ModuleCat.{u} D) := inferInstance
  obtain ⟨eP⟩ := key (P.obj : ModuleCat.{u} D)
  obtain ⟨eQ⟩ := key (Q.obj : ModuleCat.{u} D)
  exact Quotient.sound
    ⟨(simpleProp (ModuleCat.{u} D)).fullyFaithfulι.preimageIso (eP.trans eQ.symm).toModuleIso⟩

/-- **Simple modules of a finite product of rings (deferred; sub-issue).** The simple modules of a
finite product `∏ i, R i` are exactly the simple modules of the individual factors (pulled back
along the projections): a simple `∏ R i`-module is annihilated by all but one factor's identity
idempotent, so it is a simple module over that factor. Hence the counts add. -/
theorem natCard_simpleModuleClasses_pi {n : ℕ} (R : Fin n → Type u) [∀ i, Ring (R i)] :
    Nat.card (SimpleModuleClasses.{u} (∀ i, R i))
      = ∑ i, Nat.card (SimpleModuleClasses.{u} (R i)) := by
  sorry

/-- **Base change of the Wedderburn product (deferred; sub-issue).** For a field extension `K ⊇ k`,
base change carries a `k`-algebra isomorphism `A ≃ₐ[k] ∏ i, Matrix (Fin (d i)) (Fin (d i)) (D i)`
to a `K`-algebra isomorphism `K ⊗ A ≃ₐ[K] ∏ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗ D i)`, by
distributing `K ⊗ -` over the finite product and over each matrix ring. -/
theorem nonempty_baseChange_pi_matrix_algEquiv (k K : Type u) [Field k] [Field K] [Algebra k K]
    {n : ℕ} (D : Fin n → Type u) [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)]
    (d : Fin n → ℕ) {A : Type u} [Ring A] [Algebra k A]
    (e : A ≃ₐ[k] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))) :
    Nonempty (K ⊗[k] A ≃ₐ[K] (∀ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) := by
  sorry

/-- **Base change of a semisimple algebra can only increase the number of simple modules.**
For a finite-dimensional **semisimple** `k`-algebra `A` and any field extension `K ⊇ k`,
`#(simple A) ≤ #(simple (K ⊗[k] A))`. Separability-free: no hypothesis on `K/k`.

Proof: by Artin–Wedderburn `A ≃ₐ[k] ∏ i, Matrix (Fin (d i)) (Fin (d i)) (D i)`, so
`#(simple A) = ∑ i, #(simple (Matrix … (D i))) = ∑ i, #(simple (D i)) = ∑ i, 1 = n`
(matrix Morita invariance and uniqueness of the simple module over a division ring). Base change
distributes to `K ⊗ A ≃ₐ[K] ∏ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗ D i)`, so
`#(simple (K ⊗ A)) = ∑ i, #(simple (K ⊗ D i)) ≥ ∑ i, 1 = n`, each `K ⊗ D i` being a nonzero
finite-dimensional `K`-algebra. -/
theorem natCard_simpleModuleClasses_le_baseChange_of_isSemisimpleRing
    (k K : Type u) {A : Type u} [Field k] [Field K] [Algebra k K]
    [Ring A] [Algebra k A] [Module.Finite k A] [IsSemisimpleRing A] :
    Nat.card (SimpleModuleClasses.{u} A)
      ≤ Nat.card (SimpleModuleClasses.{u} (K ⊗[k] A)) := by
  classical
  obtain ⟨n, D, d, _, _, hDfin, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite (R₀ := k) (R := A)
  -- Each division factor `D i` has exactly one simple module; each `K ⊗ D i` has at least one.
  have hDone : ∀ i, Nat.card (SimpleModuleClasses.{u} (D i)) = 1 := by
    intro i
    haveI := hDfin i
    have hne : Nonempty (SimpleModuleClasses.{u} (D i)) := nonempty_simpleModuleClasses k
    have hss : Subsingleton (SimpleModuleClasses.{u} (D i)) :=
      subsingleton_simpleModuleClasses_divisionRing (D i)
    exact Nat.card_eq_one_iff_unique.mpr ⟨hss, hne⟩
  -- LHS count: `#(simple A) = n`.
  have hL : Nat.card (SimpleModuleClasses.{u} A) = n := by
    rw [Nat.card_congr (simpleModuleClassesCongrRingEquiv (e.toRingEquiv)),
      natCard_simpleModuleClasses_pi]
    have : ∀ i, Nat.card
        (SimpleModuleClasses.{u} (Matrix (Fin (d i)) (Fin (d i)) (D i))) = 1 := by
      intro i
      haveI : NeZero (d i) := hd i
      rw [Nat.card_congr (simpleModuleClassesMatrixEquiv (R := D i) (d i)), hDone i]
    simp [this]
  -- RHS count: `#(simple (K ⊗ A)) = ∑ i, #(simple (K ⊗ D i)) ≥ n`.
  obtain ⟨f⟩ := nonempty_baseChange_pi_matrix_algEquiv k K D d e
  rw [Nat.card_congr (simpleModuleClassesCongrRingEquiv (f.toRingEquiv)),
    natCard_simpleModuleClasses_pi, hL]
  -- `1 ≤ #(simple (K ⊗ D i))` for each factor, so `∑ i, … ≥ ∑ i, 1 = n`.
  have key : ∀ i, 1 ≤ Nat.card
      (SimpleModuleClasses.{u} (Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) := by
    intro i
    haveI : NeZero (d i) := hd i
    haveI := hDfin i
    haveI : Module.Finite K (K ⊗[k] D i) := inferInstance
    rw [Nat.card_congr (simpleModuleClassesMatrixEquiv (R := K ⊗[k] D i) (d i))]
    have hne : Nonempty (SimpleModuleClasses.{u} (K ⊗[k] D i)) :=
      nonempty_simpleModuleClasses K
    haveI : Finite (SimpleModuleClasses.{u} (K ⊗[k] D i)) :=
      finite_simpleModuleClasses K
    exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨hne, inferInstance⟩)
  have hsum : ∑ _i : Fin n, 1 ≤ ∑ i, Nat.card
      (SimpleModuleClasses.{u} (Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) :=
    Finset.sum_le_sum fun i _ => key i
  simpa using hsum

end Etingof

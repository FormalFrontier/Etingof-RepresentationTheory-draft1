import Mathlib
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Exercise 4.2.3: enumeration of simple `K[G]`-modules in the modular case

Over an algebraically closed field `K` (with **no** `NeZero (Nat.card G : K)` hypothesis, so the
modular case is allowed) this file builds the standard family of simple `K[G]`-modules coming from
the Wedderburn decomposition of the *semisimple quotient* `A = K[G] ⧸ rad(K[G])`.

The semisimple, non-modular enumeration lives in
`Infrastructure/IrreducibleEnumeration.lean` (`IrrepDecomp`), but that development bundles an
algebra **isomorphism** `k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k`, which does not exist
modularly (the radical is nonzero). Here we replace the isomorphism by a **surjective** algebra
hom `π : K[G] →ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) K` — the composite of the quotient map
`K[G] ↠ A` with the Wedderburn isomorphism of `A`. Only surjectivity of `π` is used by the
column-representation machinery, so the enumeration survives.

## Main constructions

* `SplitData K G` — bundles `n`, the block sizes `d`, and the surjective `π`.
* `SplitData.of` — constructs the data from `A = K[G] ⧸ rad` semisimple + Wedderburn.
* `SplitData.blockHom` — projection `K[G] →ₐ[K] Matrix (Fin (D.d i)) (Fin (D.d i)) K` to block `i`
  (surjective).
* `SplitData.Std D i := Fin (D.d i) → K` — the `i`-th standard module, a simple, finite-dimensional
  `K[G]`-module with `IsScalarTower K (MonoidAlgebra K G) (D.Std i)`.

The enumeration (`Std` pairwise non-isomorphic and exhaustive) and the resulting count
`Nat.card (SimpleModuleClasses K[G]) = n` are stated here and proved in the follow-up.

## References

- Etingof, *Introduction to Representation Theory*, §4.
- `Infrastructure/IrreducibleEnumeration.lean` (`IrrepDecomp`, the `NeZero`-gated analog).
- Mathlib: `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`.
-/

open CategoryTheory

namespace Etingof.SplitSimples

universe u v

variable (K : Type u) (G : Type v) [Field K] [IsAlgClosed K] [Group G] [Fintype G]

/-- Bundled data for the modular Wedderburn enumeration of `K[G]`: the number of blocks `n`, the
block sizes `d`, and a **surjective** algebra hom
`π : K[G] →ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) K`, obtained as
`(K[G] ↠ K[G]/rad) ≫ (Wedderburn iso of the semisimple quotient)`. -/
structure SplitData where
  /-- Number of Wedderburn blocks of the semisimple quotient `K[G] ⧸ rad`. -/
  n : ℕ
  /-- Block sizes. -/
  d : Fin n → ℕ
  /-- Each block is nonempty. -/
  d_pos : ∀ i, NeZero (d i)
  /-- The surjective structure hom `K[G] ↠ Π i, Matrix (Fin (d i)) (Fin (d i)) K`. -/
  π : MonoidAlgebra K G →ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) K
  /-- `π` is surjective (composite of a surjective quotient map with an isomorphism). -/
  π_surj : Function.Surjective π

variable {K G}

/-- Construct the split data from the Wedderburn decomposition of the semisimple quotient
`A = K[G] ⧸ rad(K[G])`. Over an algebraically closed field, `A` is a finite product of matrix
algebras; precomposing with the quotient map yields the surjective structure hom `π`. -/
noncomputable def SplitData.of : SplitData K G := by
  classical
  haveI : Module.Finite K (MonoidAlgebra K G) :=
    Module.Finite.of_basis (Finsupp.basisSingleOne (ι := G) (R := K))
  haveI : IsArtinianRing (MonoidAlgebra K G) := IsArtinianRing.of_finite K (MonoidAlgebra K G)
  haveI : IsSemiprimaryRing (MonoidAlgebra K G) := inferInstance
  set J := Ring.jacobson (MonoidAlgebra K G) with hJ
  haveI : IsSemisimpleRing (MonoidAlgebra K G ⧸ J) := IsSemiprimaryRing.isSemisimpleRing
  haveI : Module.Finite K (MonoidAlgebra K G ⧸ J) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ K J).toLinearMap (Ideal.Quotient.mkₐ_surjective K J)
  have hwed := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K (MonoidAlgebra K G ⧸ J)
  choose n d hd hn using hwed
  refine
    { n := n
      d := d
      d_pos := hd
      π := ((hn.some).toAlgHom).comp (Ideal.Quotient.mkₐ K J)
      π_surj := ?_ }
  intro x
  obtain ⟨y, hy⟩ := EquivLike.surjective hn.some x
  obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective K J y
  exact ⟨z, by rw [AlgHom.comp_apply, hz]; exact hy⟩

/-- The projection `K[G] →ₐ[K] Matrix (Fin (D.d i)) (Fin (D.d i)) K` onto the `i`-th block. -/
noncomputable def SplitData.blockHom (D : SplitData K G) (i : Fin D.n) :
    MonoidAlgebra K G →ₐ[K] Matrix (Fin (D.d i)) (Fin (D.d i)) K :=
  (Pi.evalAlgHom K (fun i => Matrix (Fin (D.d i)) (Fin (D.d i)) K) i).comp D.π

/-- Each block projection is surjective (composite of the surjective `π` with an evaluation). -/
lemma SplitData.blockHom_surjective (D : SplitData K G) (i : Fin D.n) :
    Function.Surjective (D.blockHom i) := by
  intro M
  obtain ⟨a, ha⟩ := D.π_surj (Pi.single i M)
  refine ⟨a, ?_⟩
  simp only [SplitData.blockHom, AlgHom.comp_apply, ha, Pi.evalAlgHom_apply, Pi.single_eq_same]

/-! ### Standard modules -/

/-- The `i`-th standard module `Fin (D.d i) → K`, made a `K[G]`-module via `blockHom i`. -/
def SplitData.Std (D : SplitData K G) (i : Fin D.n) : Type u := Fin (D.d i) → K

namespace SplitData

instance (D : SplitData K G) (i : Fin D.n) : AddCommGroup (D.Std i) :=
  inferInstanceAs (AddCommGroup (Fin (D.d i) → K))

instance (D : SplitData K G) (i : Fin D.n) : Module K (D.Std i) :=
  inferInstanceAs (Module K (Fin (D.d i) → K))

instance (D : SplitData K G) (i : Fin D.n) :
    Module (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (D.Std i) :=
  inferInstanceAs (Module (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (Fin (D.d i) → K))

instance (D : SplitData K G) (i : Fin D.n) :
    IsScalarTower K (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (D.Std i) :=
  inferInstanceAs (IsScalarTower K (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (Fin (D.d i) → K))

instance (D : SplitData K G) (i : Fin D.n) : Module.Finite K (D.Std i) :=
  inferInstanceAs (Module.Finite K (Fin (D.d i) → K))

/-- The `K[G]`-action on the `i`-th standard module, factoring through `blockHom i`. -/
noncomputable instance instModuleMonoidAlgebraStd (D : SplitData K G) (i : Fin D.n) :
    Module (MonoidAlgebra K G) (D.Std i) :=
  Module.compHom (D.Std i) (D.blockHom i).toRingHom

/-- The `K`-action and the `K[G]`-action on a standard module are compatible: the structure hom
`blockHom i` is `K`-linear. -/
instance (D : SplitData K G) (i : Fin D.n) :
    IsScalarTower K (MonoidAlgebra K G) (D.Std i) where
  smul_assoc c x m := by
    show (D.blockHom i).toRingHom (c • x) • m = c • ((D.blockHom i).toRingHom x • m)
    have hlin : (D.blockHom i).toRingHom (c • x) = c • (D.blockHom i).toRingHom x := by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul]
    rw [hlin, smul_assoc]

/-- Each standard module is a simple `K[G]`-module: it is the simple `Matrix`-module `Fin (D.d i) →
K`, restricted along the surjective block projection `blockHom i`. -/
theorem isSimpleModule_Std (D : SplitData K G) (i : Fin D.n) :
    IsSimpleModule (MonoidAlgebra K G) (D.Std i) := by
  haveI := D.d_pos i
  haveI : IsSimpleModule (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (D.Std i) :=
    inferInstanceAs (IsSimpleModule (Matrix (Fin (D.d i)) (Fin (D.d i)) K) (Fin (D.d i) → K))
  exact IsSimpleModule.compHom (D.blockHom i).toRingHom (D.blockHom_surjective i)

/-! ### Enumeration and count (deferred)

The three remaining facts — the standard modules are pairwise non-isomorphic, they exhaust the
simple `K[G]`-modules, and the resulting count `Nat.card (SimpleModuleClasses K[G]) = n` — mirror
`IrrepDecomp.columnFDRep_injective` / `columnFDRep_surjective` / `n_eq_card_simples` from
`Infrastructure/IrreducibleEnumeration.lean`, with the algebra isomorphism replaced by the
surjection `π` (only surjectivity is used in that machinery). They are stated here and proved in
the follow-up sub-issue. -/

/-- **Deliverable 3 (pairwise non-isomorphic).** Distinct standard modules are not isomorphic. -/
theorem Std_injective (D : SplitData K G) (i j : Fin D.n)
    (h : Nonempty (D.Std i ≃ₗ[MonoidAlgebra K G] D.Std j)) : i = j := by
  sorry

/-- **Deliverable 3 (exhaustive).** Every simple `K[G]`-module is isomorphic to some standard
module `Std i`. -/
theorem exists_Std_linearEquiv (D : SplitData K G)
    (M : Type u) [AddCommGroup M] [Module (MonoidAlgebra K G) M]
    [IsSimpleModule (MonoidAlgebra K G) M] :
    ∃ i, Nonempty (M ≃ₗ[MonoidAlgebra K G] D.Std i) := by
  sorry

/-- **Deliverable 4 (count).** The number of isomorphism classes of simple `K[G]`-modules equals
the number of Wedderburn blocks `n`. -/
theorem card_simpleModuleClasses (D : SplitData K G) :
    Nat.card (SimpleModuleClasses.{u} (MonoidAlgebra K G)) = D.n := by
  sorry

end SplitData

/-- **Bundled deliverable.** Over an algebraically closed field `K` (modular case allowed), the
simple `K[G]`-modules are enumerated by a finite family of standard modules whose count equals the
number of Wedderburn blocks of `K[G] ⧸ rad`. -/
theorem exists_splitSimples_count (K : Type u) (G : Type v)
    [Field K] [IsAlgClosed K] [Group G] [Fintype G] :
    ∃ (D : SplitData K G), Nat.card (SimpleModuleClasses.{u} (MonoidAlgebra K G)) = D.n :=
  ⟨SplitData.of, SplitData.card_simpleModuleClasses _⟩

end Etingof.SplitSimples

import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Module.Projective
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.LinearAlgebra.Dimension.Constructions
import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import EtingofRepresentationTheory.Chapter2.Problem2_8_6
import EtingofRepresentationTheory.Chapter9.Definition9_3_1
import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import EtingofRepresentationTheory.Chapter9.PathAlgebraStandardResolution
import EtingofRepresentationTheory.Chapter9.PathAlgebraLowerBound
import EtingofRepresentationTheory.Chapter9.HomologicalDimensionReduction
import EtingofRepresentationTheory.Chapter9.HomologicalDimensionRingEquiv
import EtingofRepresentationTheory.Chapter9.HomologicalDimensionUlift

/-!
# Problem 9.4.6: Homological dimension and Cartan matrix of path algebras

Etingof Problem 9.4.6 has two parts.

* **(i)** The path algebra `P_Q` of any quiver `Q` with at least one edge has homological
  dimension `1`. In particular, the free algebra `k⟨x₁, …, xₙ⟩` (the path algebra of the
  one-vertex quiver with `n ≥ 1` loops) has homological dimension `1`.

* **(ii)** For a finite oriented graph `Q` without oriented cycles, the Cartan matrix of the
  path algebra `P_Q` is the *path-counting matrix*: its `(i, j)` entry is the number of
  oriented paths from vertex `i` to vertex `j`.

## Statement-pass note

Part (i) is stated with `Etingof.homologicalDimension` (Definition 9.4.3) applied to
`Etingof.PathAlgebra k Q` (Definition 2.8.4) and to `FreeAlgebra k (Fin n)`. "At least one
edge" is `∃ a b, Nonempty (a ⟶ b)`.

Part (ii) is stated with `Etingof.algebraCartanMatrix` (Definition 9.3.1). The Cartan matrix
is `cᵢⱼ = dim_k Hom_A(Pᵢ, Pⱼ)` for the projective covers `Pᵢ` of the simple modules. For the
path algebra of a finite acyclic quiver the indecomposable projectives are `Pᵢ = A · eᵢ`
(`eᵢ` the trivial-path idempotent), and `Hom_A(Pᵢ, Pⱼ) ≅ eᵢ A eⱼ` is the free `k`-space on
the oriented paths from `i` to `j`. This Hom-space identification (the content that makes the
Cartan matrix count paths) is carried as the hypothesis `hcover`; the conclusion is that the
Cartan matrix equals the path-count matrix `(i, j) ↦ Nat.card (Quiver.Path i j)`. Acyclicity
(`hacyclic`) is what makes each `Quiver.Path i j` finite, so `Nat.card` is the honest count.
Proofs are deferred (`sorry`) per the statement-pass phase.
-/

universe u

open Etingof CategoryTheory Limits

namespace Etingof.Problem946

/-- **Problem 9.4.6 (i), upper bound.** Every left `PathAlgebra k Q`-module has projective
dimension `≤ 1`; equivalently, the path algebra has homological dimension `≤ 1`.

This is the reusable core of Problem 9.4.6 (i): it is the *upper* bound
`homologicalDimension (PathAlgebra k Q) ≤ 1`. Combined with the lower bound
`¬ HasHomologicalDimensionLE (PathAlgebra k Q) 0` (non-semisimplicity once `Q` has an edge),
it yields `homologicalDimension_pathAlgebra_eq_one`.

## Proof strategy (the standard resolution)

Write `A := PathAlgebra k Q`, let `S := Q → k` be the semisimple subalgebra spanned by the
trivial-path idempotents `eᵢ`, and let `V` be the `S`-bimodule spanned by the arrows. For any
left `A`-module `M` the *standard resolution* is the length-`1` projective resolution
```
0 → A ⊗_S (V ⊗_S M) → A ⊗_S M →ᵉ M → 0,
```
where `ε(a ⊗ m) = a · m` is the multiplication map. Both nonzero terms are projective `A`-modules
because they are *induced* from `S`-modules (`A ⊗_S -`), `S` is semisimple (a finite product of
fields), so every `S`-module is projective, and induction along `S → A` preserves projectives
(it is left adjoint to restriction of scalars). Exactness — that `ker ε ≅ A ⊗_S (V ⊗_S M)` via
`a ⊗ v ⊗ m ↦ av ⊗ m - a ⊗ vm` — is the analogue of the Koszul short exact sequence used for the
polynomial case (`Example 9.4.4`).

## Obstruction / why this is genuinely new infrastructure

Unlike the polynomial case, the base extension here is **noncommutative-induced**: the vertex
idempotents `eᵢ` are *not central* in `A`, so `A` is not an `S`-algebra in the commutative sense
and Mathlib's `ModuleCat.extendScalars` (which requires `[CommRing R] [CommRing S]`) does **not**
apply. Building `A ⊗_S -` as a left `A`-module functor left-adjoint to `restrictScalars` along the
non-central inclusion `S → A`, and its projectivity-preservation, is genuine new infrastructure not
in Mathlib. See issue #6420 for the decomposition.

## Assembly

Because `Quiver.{u + 1} Q`, the path algebra `A = PathAlgebra k Q` lives in `Type (u + 1)`, so
`HasHomologicalDimensionLE A 1` (Definition 9.4.3) quantifies over `ModuleCat.{u + 1} A` — exactly
the universe the standard resolution `standardResolution_shortExact` is built at, so no universe
uplift is needed. For each `M` the proof reads off `(standardComplex M).ShortExact`, notes both
nonzero terms are projective (`projective_inducedModule_obj`), and applies dimension shifting
`ShortExact.hasProjectiveDimensionLT_X₃` (as in `hasHomologicalDimensionLE_polynomial`,
`Chapter9/Example9_4_4.lean`). -/
theorem hasHomologicalDimensionLE_pathAlgebra_one
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q] :
    Etingof.HasHomologicalDimensionLE (Etingof.PathAlgebra k Q) 1 := by
  intro M
  -- The standard length-`1` projective resolution `0 → A ⊗_S (V ⊗_S M) → A ⊗_S M → M → 0`.
  have hSES := Etingof.PathAlgebra.standardResolution_shortExact M
  -- Both nonzero terms are projective (induced from the semisimple vertex subalgebra `S = Q → k`).
  haveI hP1 : Projective (Etingof.PathAlgebra.standardComplex M).X₁ :=
    Etingof.PathAlgebra.projective_inducedModule_obj (Etingof.PathAlgebra.VtensObj M)
  haveI hP2 : Projective (Etingof.PathAlgebra.standardComplex M).X₂ :=
    Etingof.PathAlgebra.projective_inducedModule_obj (Etingof.PathAlgebra.restrictObj M)
  -- Dimension shifting on the short exact sequence gives `pd M ≤ 1`.
  exact hSES.hasProjectiveDimensionLT_X₃ 1
    (projective_iff_hasProjectiveDimensionLT_one.mp hP1)
    (hasProjectiveDimensionLT_of_ge _ 1 2 (by omega))

/-- **Problem 9.4.6 (i), path algebra.** The path algebra `P_Q` of a quiver `Q` with at least
one edge has homological dimension `1`. -/
theorem homologicalDimension_pathAlgebra_eq_one
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]
    (hQ : ∃ a b : Q, Nonempty (a ⟶ b)) :
    Etingof.homologicalDimension (Etingof.PathAlgebra k Q) = 1 :=
  Etingof.homologicalDimension_eq_one_of_not_le_zero
    hasHomologicalDimensionLE_pathAlgebra_one
    (not_hasHomologicalDimensionLE_zero_pathAlgebra hQ)

/-! ## The free algebra as a path algebra

We realize `k⟨x₁, …, xₙ⟩` as the path algebra of the one-vertex quiver `Q₀` with `n` loops, giving
a genuine algebra isomorphism `freePathEquiv : FreeAlgebra k (Fin n) ≃ₐ[k] PathAlgebra k Q₀`.

**Universe note.** The two algebras do *not* live in the same universe: `FreeAlgebra k (Fin n)`
is `Type u`, but `PathAlgebra k Q₀` is `Type (u+1)` because `Quiver.Path` lands in `Type (max u v)`
and the standard-resolution machinery of `homologicalDimension_pathAlgebra_eq_one` hard-requires
`Quiver.{u+1} Q₀`. Consequently the same-universe `homologicalDimension_congr` (from #6635) is *not*
enough to conclude `homologicalDimension (FreeAlgebra k (Fin n)) = 1` from the path-algebra result;
that final step additionally uses universe-lift invariance of `homologicalDimension`
(`homologicalDimension_le_ulift`, `Chapter9/HomologicalDimensionUlift.lean`) to lift the free
algebra to `Type (u+1)` before transferring across `freePathEquiv`. -/

/-- Vertex type of the one-vertex "loop" quiver with `n` loops: a single point in `Type u`. -/
def LoopVertex (n : ℕ) : Type u := PUnit.{u + 1}

instance (n : ℕ) : Fintype (LoopVertex.{u} n) := inferInstanceAs (Fintype PUnit)
instance (n : ℕ) : DecidableEq (LoopVertex.{u} n) := inferInstanceAs (DecidableEq PUnit)
instance (n : ℕ) : Unique (LoopVertex.{u} n) := inferInstanceAs (Unique PUnit)

/-- The one-vertex quiver with `n` loops: the hom-type is `ULift.{u+1} (Fin n)`, so that
`Quiver.{u + 1} (LoopVertex n)` holds (as required by `homologicalDimension_pathAlgebra_eq_one`). -/
instance loopQuiver (n : ℕ) : Quiver.{u + 1} (LoopVertex.{u} n) :=
  ⟨fun _ _ => ULift.{u + 1} (Fin n)⟩

/-- The unique vertex of the loop quiver. -/
abbrev LoopVertex.pt (n : ℕ) : LoopVertex.{u} n := PUnit.unit

open Etingof.Problem2_8_6

/-- The `m`-th loop as an arrow `pt ⟶ pt` of the loop quiver. Because the quiver's hom-type is the
constant `ULift (Fin n)`, the endpoints are not inferable from the arrow alone, so they are pinned
here explicitly. -/
def loopArrow (n : ℕ) (m : Fin n) : (LoopVertex.pt n ⟶ LoopVertex.pt n) := ULift.up m

/-- `k⟨x₁, …, xₙ⟩ → P_{Q₀}`: the free-algebra generator `xᵢ` maps to the `i`-th loop. -/
noncomputable def freeToPath (k : Type u) [Field k] (n : ℕ) :
    FreeAlgebra k (Fin n) →ₐ[k] PathAlgebra k (LoopVertex.{u} n) :=
  FreeAlgebra.lift k fun m =>
    arrowGen k (LoopVertex n) (i := LoopVertex.pt n) (j := LoopVertex.pt n) (loopArrow n m)

theorem freeToPath_ι (k : Type u) [Field k] (n : ℕ) (m : Fin n) :
    freeToPath k n (FreeAlgebra.ι k m)
      = arrowGen k (LoopVertex n) (i := LoopVertex.pt n) (j := LoopVertex.pt n) (loopArrow n m) := by
  unfold freeToPath
  rw [FreeAlgebra.lift_ι_apply]

/-- Existence and uniqueness of the algebra map `P_{Q₀} → k⟨x₁, …, xₙ⟩` sending the single vertex
idempotent to `1` and each loop `eᵢ` to the free generator `xᵢ`. All defining relations of the
path algebra hold trivially: the single vertex makes the orthogonality relations vacuous, and the
one vertex idempotent is the unit of the target. -/
theorem pathToFree_exists (k : Type u) [Field k] (n : ℕ) :
    ∃! φ : PathAlgebra k (LoopVertex.{u} n) →ₐ[k] FreeAlgebra k (Fin n),
      (∀ i, φ (vertexIdem k (LoopVertex n) i) = (1 : FreeAlgebra k (Fin n))) ∧
        (∀ (i j : LoopVertex n) (e : i ⟶ j),
          φ (arrowGen k (LoopVertex n) e) = FreeAlgebra.ι k (ULift.down e)) :=
  defining_relations_universal k (LoopVertex n) (FreeAlgebra k (Fin n)) (fun _ => 1)
    (fun _ _ e => FreeAlgebra.ι k (ULift.down e))
    (by rw [Fintype.sum_unique])
    (fun _ => one_mul 1)
    (fun i j h => absurd (Subsingleton.elim i j) h)
    (fun _ _ _ => one_mul _)
    (fun l i _ _ h => absurd (Subsingleton.elim l i) h)
    (fun _ _ _ => mul_one _)
    (fun l _ j _ h => absurd (Subsingleton.elim l j) h)

/-- `P_{Q₀} → k⟨x₁, …, xₙ⟩`: the inverse-to-be of `freeToPath`, sending each loop to `xᵢ`. -/
noncomputable def pathToFree (k : Type u) [Field k] (n : ℕ) :
    PathAlgebra k (LoopVertex.{u} n) →ₐ[k] FreeAlgebra k (Fin n) :=
  (pathToFree_exists k n).choose

theorem pathToFree_vertexIdem (k : Type u) [Field k] (n : ℕ) (i : LoopVertex.{u} n) :
    pathToFree k n (vertexIdem k (LoopVertex n) i) = 1 :=
  (pathToFree_exists k n).choose_spec.1.1 i

theorem pathToFree_arrowGen (k : Type u) [Field k] (n : ℕ) {i j : LoopVertex.{u} n} (e : i ⟶ j) :
    pathToFree k n (arrowGen k (LoopVertex n) e) = FreeAlgebra.ι k (ULift.down e) :=
  (pathToFree_exists k n).choose_spec.1.2 i j e

/-- Every single vertex idempotent equals the unit of `P_{Q₀}` (there is only one vertex). -/
theorem vertexIdem_eq_one (k : Type u) [Field k] (n : ℕ) (a : LoopVertex.{u} n) :
    vertexIdem k (LoopVertex n) a = 1 := by
  have ha : a = (default : LoopVertex n) := Subsingleton.elim _ _
  subst ha
  rw [← Fintype.sum_unique (vertexIdem k (LoopVertex n))]
  exact sum_vertexIdem k (LoopVertex n)

/-- `freeToPath` inverts `pathToFree` on each loop generator. -/
theorem freeToPath_pathToFree_arrowGen (k : Type u) [Field k] (n : ℕ)
    {i j : LoopVertex.{u} n} (e : i ⟶ j) :
    freeToPath k n (pathToFree k n (arrowGen k (LoopVertex n) e))
      = arrowGen k (LoopVertex n) e := by
  obtain rfl : i = LoopVertex.pt n := Subsingleton.elim _ _
  obtain rfl : j = LoopVertex.pt n := Subsingleton.elim _ _
  rw [pathToFree_arrowGen, freeToPath_ι]
  rfl

/-- `freeToPath ∘ pathToFree` fixes every basis path of `P_{Q₀}`. -/
theorem freeToPath_pathToFree_ofPath (k : Type u) [Field k] (n : ℕ)
    {a b : LoopVertex.{u} n} (p : Quiver.Path a b) :
    freeToPath k n (pathToFree k n (PathAlgebra.ofPath (k := k) ⟨a, b, p⟩))
      = PathAlgebra.ofPath (k := k) ⟨a, b, p⟩ := by
  induction p with
  | nil =>
    change freeToPath k n (pathToFree k n (vertexIdem k (LoopVertex n) a))
      = vertexIdem k (LoopVertex n) a
    rw [pathToFree_vertexIdem, map_one, vertexIdem_eq_one]
  | cons q e ih =>
    rw [ofPath_cons, map_mul, map_mul, ih, freeToPath_pathToFree_arrowGen]

theorem freeToPath_comp_pathToFree (k : Type u) [Field k] (n : ℕ) :
    (freeToPath k n).comp (pathToFree k n)
      = AlgHom.id k (PathAlgebra k (LoopVertex.{u} n)) := by
  ext f
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single s c =>
    obtain ⟨a, b, p⟩ := s
    have hsc : (Finsupp.single (⟨a, b, p⟩ : QuiverPathIndex (LoopVertex n)) c
          : PathAlgebra k (LoopVertex n))
        = c • PathAlgebra.ofPath (k := k) (⟨a, b, p⟩ : QuiverPathIndex (LoopVertex n)) := by
      rw [PathAlgebra.ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsc, map_smul, map_smul, freeToPath_pathToFree_ofPath]

theorem pathToFree_comp_freeToPath (k : Type u) [Field k] (n : ℕ) :
    (pathToFree k n).comp (freeToPath k n) = AlgHom.id k (FreeAlgebra k (Fin n)) := by
  apply FreeAlgebra.hom_ext
  funext i
  change pathToFree k n (freeToPath k n (FreeAlgebra.ι k i)) = FreeAlgebra.ι k i
  rw [freeToPath_ι, pathToFree_arrowGen]
  rfl

/-- The algebra isomorphism `k⟨x₁, …, xₙ⟩ ≃ₐ P_{Q₀}` realizing the free algebra as the path
algebra of the one-vertex quiver with `n` loops. -/
noncomputable def freePathEquiv (k : Type u) [Field k] (n : ℕ) :
    FreeAlgebra k (Fin n) ≃ₐ[k] PathAlgebra k (LoopVertex.{u} n) :=
  AlgEquiv.ofAlgHom (freeToPath k n) (pathToFree k n)
    (freeToPath_comp_pathToFree k n) (pathToFree_comp_freeToPath k n)

/-! ## The free algebra is not semisimple (lower bound)

Mirroring the path-algebra lower bound (`Chapter9/PathAlgebraLowerBound.lean`), the **augmentation
module** — the field `k` on which every generator `xᵢ` acts as `0` — is not projective. If it were,
the surjection `A ↠ k`, `p ↦ p • 1`, would split by an `A`-linear section `s`; writing `w = s(1)`,
the relation `xᵢ • 1 = 0` forces `xᵢ · w = 0` in `A`. Since `A = FreeAlgebra k (Fin n)` is a domain
and `xᵢ ≠ 0`, this gives `w = 0`, contradicting `ε(w) = 1` (as `s` is a section). Here `k` already
lives in `Type u`, the native universe of `A`, so no universe lift is needed for the lower bound. -/

/-- The augmentation `k⟨x₁, …, xₙ⟩ → k` sending every generator `xᵢ` to `0`. -/
noncomputable def freeAug (k : Type u) [Field k] (n : ℕ) : FreeAlgebra k (Fin n) →ₐ[k] k :=
  FreeAlgebra.lift k fun _ => (0 : k)

@[simp] theorem freeAug_ι (k : Type u) [Field k] (n : ℕ) (i : Fin n) :
    freeAug k n (FreeAlgebra.ι k i) = 0 := by
  rw [freeAug, FreeAlgebra.lift_ι_apply]

/-- **Problem 9.4.6 (i), free-algebra lower bound.** The free associative algebra on `n ≥ 1`
generators is not semisimple: it does not have homological dimension `0`.

The augmentation module `k` (each generator acting as `0`, carried as a *local* module instance to
avoid a spurious global `Module (FreeAlgebra k (Fin n)) k`) is not projective: a projective section
`s` of the surjection `A ↠ k`, `p ↦ p • 1`, would give `w := s(1)` with `x₀ · w = 0` yet
`ε(w) = 1`, impossible in the domain `A`. -/
theorem not_hasHomologicalDimensionLE_zero_freeAlgebra
    {k : Type u} [Field k] {n : ℕ} (hn : 1 ≤ n) :
    ¬ Etingof.HasHomologicalDimensionLE (FreeAlgebra k (Fin n)) 0 := by
  intro hall
  -- `k` as a left `A`-module through the augmentation `ε`, `a • v = ε(a) · v`.
  letI aug : Module (FreeAlgebra k (Fin n)) k := Module.compHom k (freeAug k n).toRingHom
  have smul_def : ∀ (a : FreeAlgebra k (Fin n)) (v : k), a • v = freeAug k n a * v :=
    fun _ _ => rfl
  -- The augmentation module as a `ModuleCat` object; under dimension `0` it is projective.
  let MA := ModuleCat.of (FreeAlgebra k (Fin n)) k
  have hpd : CategoryTheory.HasProjectiveDimensionLE MA 0 := hall MA
  haveI hproj : CategoryTheory.Projective MA :=
    projective_iff_hasProjectiveDimensionLT_one.mpr hpd
  haveI hmod : Module.Projective (FreeAlgebra k (Fin n)) k :=
    (IsProjective.iff_projective (R := FreeAlgebra k (Fin n)) k).mpr hproj
  -- The surjection `A ↠ k`, `p ↦ p • 1`.
  let surj := LinearMap.toSpanSingleton (FreeAlgebra k (Fin n)) k (1 : k)
  have hsurj : Function.Surjective surj := by
    intro v
    refine ⟨algebraMap k (FreeAlgebra k (Fin n)) v, ?_⟩
    show surj (algebraMap k (FreeAlgebra k (Fin n)) v) = v
    rw [LinearMap.toSpanSingleton_apply, smul_def, mul_one, AlgHom.commutes]
    simp
  -- Projectivity yields an `A`-linear section `s`.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property surj LinearMap.id hsurj
  set w : FreeAlgebra k (Fin n) := s (1 : k) with hw_def
  -- `s` is a section, so `ε(w) = 1`.
  have hsection : freeAug k n w = 1 := by
    have hcf := LinearMap.congr_fun hs (1 : k)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hcf
    rw [LinearMap.toSpanSingleton_apply, smul_def, mul_one] at hcf
    exact hcf
  -- The generator `x₀ = ι ⟨0, hn⟩` acts as `0`, so `x₀ · w = 0` in `A`.
  have hact : (FreeAlgebra.ι k ⟨0, hn⟩ : FreeAlgebra k (Fin n)) • (1 : k) = 0 := by
    rw [smul_def, freeAug_ι, zero_mul]
  have hzero : (FreeAlgebra.ι k ⟨0, hn⟩ : FreeAlgebra k (Fin n)) * w = 0 := by
    have h1 := s.map_smul (FreeAlgebra.ι k ⟨0, hn⟩) (1 : k)
    rw [hact, map_zero] at h1
    rw [← smul_eq_mul]; exact h1.symm
  -- `A` is a domain and `x₀ ≠ 0`, so `w = 0` — contradicting `ε(w) = 1`.
  have hw0 : w = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (FreeAlgebra.ι_ne_zero (⟨0, hn⟩ : Fin n))
    · exact h
  rw [hw0, map_zero] at hsection
  exact one_ne_zero hsection.symm

/-- **Problem 9.4.6 (i), free algebra.** The free associative algebra `k⟨x₁, …, xₙ⟩` on
`n ≥ 1` generators (the path algebra of the one-vertex quiver with `n` loops) has homological
dimension `1`.

`freePathEquiv k n : FreeAlgebra k (Fin n) ≃ₐ[k] PathAlgebra k (LoopVertex n)` realizes the free
algebra as the one-vertex path algebra. The two algebras live in *different* universes
(`FreeAlgebra k (Fin n) : Type u` but `PathAlgebra k (LoopVertex n) : Type (u+1)`), so the
same-universe `homologicalDimension_congr` is not enough. The upper bound
`HasHomologicalDimensionLE (FreeAlgebra k (Fin n)) 1` is obtained by lifting to universe `u+1`
(`hasHomologicalDimensionLE_of_ulift`), transferring across the ring equivalence
`ULift (FreeAlgebra k (Fin n)) ≃+* PathAlgebra k (LoopVertex n)` (now same-universe) and applying
the path-algebra upper bound. The lower bound is the direct non-semisimplicity result
`not_hasHomologicalDimensionLE_zero_freeAlgebra`. -/
theorem homologicalDimension_freeAlgebra_eq_one
    {k : Type u} [Field k] {n : ℕ} (hn : 1 ≤ n) :
    Etingof.homologicalDimension (FreeAlgebra k (Fin n)) = 1 := by
  -- The one-vertex loop quiver has an edge (the `0`-th loop).
  have hQ : ∃ a b : LoopVertex.{u} n, Nonempty (a ⟶ b) :=
    ⟨LoopVertex.pt n, LoopVertex.pt n, ⟨loopArrow n ⟨0, hn⟩⟩⟩
  -- The same-universe (`Type (u+1)`) ring equivalence `ULift (FreeAlg) ≃+* PathAlg`.
  let eRing : ULift.{u + 1} (FreeAlgebra k (Fin n)) ≃+* PathAlgebra k (LoopVertex.{u} n) :=
    (ULift.ringEquiv).trans (freePathEquiv k n).toRingEquiv
  -- Upper bound via universe lift + same-universe ring-equivalence transfer.
  have h1 : Etingof.HasHomologicalDimensionLE (FreeAlgebra k (Fin n)) 1 := by
    have hbig : Etingof.HasHomologicalDimensionLE (ULift.{u + 1} (FreeAlgebra k (Fin n))) 1 := by
      rw [Etingof.hasHomologicalDimensionLE_congr eRing]
      exact hasHomologicalDimensionLE_pathAlgebra_one
    exact Etingof.hasHomologicalDimensionLE_of_ulift hbig
  -- Lower bound: the free algebra is not semisimple.
  have h0 : ¬ Etingof.HasHomologicalDimensionLE (FreeAlgebra k (Fin n)) 0 :=
    not_hasHomologicalDimensionLE_zero_freeAlgebra hn
  exact Etingof.homologicalDimension_eq_one_of_not_le_zero h1 h0

/-- The path-counting matrix of a quiver `Q`: the `(i, j)` entry is the number of oriented
paths from `i` to `j`. This is the Cartan matrix of the path algebra of a finite acyclic
quiver (Problem 9.4.6 (ii)). -/
noncomputable def pathCountMatrix (Q : Type u) [Quiver Q] : Matrix Q Q ℕ :=
  Matrix.of fun i j => Nat.card (Quiver.Path i j)

/-- **Problem 9.4.6 (ii).** Let `Q` be a finite oriented graph without oriented cycles. Then
the Cartan matrix of the path algebra `P_Q` is the path-counting matrix: `cᵢⱼ` is the number
of oriented paths from `i` to `j`.

The projective covers `P` of the simple modules are supplied together with the defining
identification `hcover : Hom_A(Pᵢ, Pⱼ) ≅ (paths i → j) →₀ k` (for the path algebra these are
`Pᵢ = A·eᵢ` with `Hom_A(Pᵢ, Pⱼ) ≅ eᵢ A eⱼ`, free on the paths from `i` to `j`). Acyclicity
`hacyclic` makes each path type finite, so `Nat.card` is the genuine number of paths. -/
theorem cartanMatrix_pathAlgebra_eq_pathCount
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]
    (hacyclic : ∀ (i : Q) (p : Quiver.Path i i), p = Quiver.Path.nil)
    [∀ i j : Q, Finite (Quiver.Path i j)]
    (P : Q → Type u) [∀ i, AddCommGroup (P i)]
    [∀ i, Module (Etingof.PathAlgebra k Q) (P i)] [∀ i, Module k (P i)]
    [∀ i, SMulCommClass (Etingof.PathAlgebra k Q) k (P i)]
    (hcover : ∀ i j : Q,
      Nonempty ((P i →ₗ[Etingof.PathAlgebra k Q] P j) ≃ₗ[k] (Quiver.Path i j →₀ k))) :
    Etingof.algebraCartanMatrix (k := k) (A := Etingof.PathAlgebra k Q) P = pathCountMatrix Q := by
  ext i j
  obtain ⟨e⟩ := hcover i j
  have : Fintype (Quiver.Path i j) := Fintype.ofFinite _
  simp only [Etingof.algebraCartanMatrix, pathCountMatrix, Matrix.of_apply]
  rw [e.finrank_eq, Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

end Etingof.Problem946

import Mathlib

/-!
# Linear independence of trace-character functionals (Dedekind/Artin)

This file proves the classical fact that the **trace-character functionals** of a finite
family of pairwise non-isomorphic, finite-dimensional, *simple* modules over an algebra `A`
are linearly independent over the base field.

For an `A`-module `M` that is finite-dimensional over the field `𝕜` (with `𝕜` central in `A`),
the *trace character* is the `𝕜`-linear functional
`traceChar i : A →ₗ[𝕜] 𝕜`, `a ↦ trace_𝕜 (v ↦ a • v : M i → M i)`.

## Main result

* `Etingof.traceCharacter_linearIndependent` : if `M i` are pairwise non-isomorphic simple
  `A`-modules, finite-dimensional over a characteristic-zero field `𝕜`, then the functionals
  `traceChar M i` are `𝕜`-linearly independent.

## Proof strategy

This is the algebra-side Dedekind/Artin input to the `|ι| = |P|` counting step for the
Schur-Weyl decomposition (sub-issue of #4875 / #4870).

The heart is `Etingof.CharacterIndependence.exists_separating`: for each index `j` there is an
element `a ∈ A` acting as the **identity** on `M j` and as **zero** on every other `M i`.
Such separating elements come from the Jacobson density theorem: `A` surjects onto the
bicommutant `End_{End_A 𝕄}(𝕄)` of the semisimple module `𝕄 = ∀ i, M i`
(`Module.Finite.toModuleEnd_moduleEnd_surjective`), and the projection onto the `j`-th factor
lies in that bicommutant because, by Schur's lemma, every `A`-endomorphism of `𝕄` is
"block diagonal" (`Hom_A(M i, M k) = 0` for `i ≠ k` when the simples are non-isomorphic).

Given the separating elements, linear independence is immediate: testing a vanishing
combination `∑ i, g i • traceChar i = 0` against the separating element for `j` yields
`g j · dim_𝕜 (M j) = 0`, and `dim_𝕜 (M j) ≠ 0` in characteristic zero (`M j` is simple, hence
nontrivial, hence of positive dimension).

No algebraic closedness is needed: only `CharZero 𝕜`.
-/

open Module (End)

namespace Etingof

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]
variable {A : Type*} [Ring A] [Algebra 𝕜 A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
  [∀ i, Module 𝕜 (M i)] [∀ i, IsScalarTower 𝕜 A (M i)] [∀ i, Module.Finite 𝕜 (M i)]

namespace CharacterIndependence

/-- The Pi-type module `𝕄 = ∀ i, N i`, the direct sum on which the density theorem operates.
The argument is taken as a fresh type family so this abbreviation carries no module instances. -/
abbrev Pim (N : ι → Type*) : Type _ := ∀ i, N i

/-- Projection of `𝕄` onto its `j`-th factor, as an `A`-linear endomorphism. -/
def proj (j : ι) : Pim M →ₗ[A] Pim M :=
  (LinearMap.single A M j).comp (LinearMap.proj j)

omit [Fintype ι] in
@[simp]
theorem proj_apply (j : ι) (x : Pim M) : proj (A := A) M j x = Pi.single j (x j) := by
  simp [proj]

variable {M}

omit [Fintype ι] in
/-- **Schur's lemma, off-diagonal vanishing.** For pairwise non-isomorphic simple modules, any
`A`-linear endomorphism of `𝕄` sends the `i`-th factor to the `k`-th factor by the zero map
whenever `i ≠ k`. -/
theorem offDiag_eq_zero
    (hsimp : ∀ i, IsSimpleModule A (M i))
    (hdist : Pairwise (fun i j => ¬ Nonempty (M i ≃ₗ[A] M j)))
    (f : Pim M →ₗ[A] Pim M) {i k : ι} (hik : i ≠ k) (m : M i) :
    (f (Pi.single i m)) k = 0 := by
  haveI := hsimp i
  haveI := hsimp k
  -- the A-linear composite `M i → 𝕄 → 𝕄 → M k`
  let g : M i →ₗ[A] M k :=
    (LinearMap.proj k).comp (f.comp (LinearMap.single A M i))
  have hg : g = 0 := by
    rcases g.bijective_or_eq_zero with hbij | hz
    · exact absurd ⟨LinearEquiv.ofBijective g hbij⟩ (hdist hik)
    · exact hz
  have : g m = 0 := by rw [hg]; rfl
  simpa [g] using this

/-- Any element of `𝕄` is the sum of its single-factor components. -/
theorem sum_single (x : Pim M) : ∑ i, Pi.single i (x i) = x := by
  funext k
  rw [Finset.sum_apply, Finset.sum_pi_single]
  simp

/-- The `j`-th projection commutes with every `A`-linear endomorphism of `𝕄`: it lies in the
bicommutant. -/
theorem proj_comm
    (hsimp : ∀ i, IsSimpleModule A (M i))
    (hdist : Pairwise (fun i j => ¬ Nonempty (M i ≃ₗ[A] M j)))
    (j : ι) (f : Pim M →ₗ[A] Pim M) (x : Pim M) :
    proj (A := A) M j (f x) = f (proj (A := A) M j x) := by
  classical
  -- Key (a): `f` maps the `j`-th factor into the `j`-th factor.
  have ha : ∀ m : M j, f (Pi.single j m) = Pi.single j ((f (Pi.single j m)) j) := by
    intro m
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · rw [Pi.single_eq_of_ne hk]
      exact offDiag_eq_zero hsimp hdist f (Ne.symm hk) m
  -- Key (b): the `j`-component of `f x` only sees the `j`-component of `x`.
  have hb : (f x) j = (f (Pi.single j (x j))) j := by
    conv_lhs => rw [← sum_single x]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_eq_single j ?_ ?_
    · intro i _ hij
      exact offDiag_eq_zero hsimp hdist f hij (x i)
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [proj_apply, proj_apply, ha (x j), hb]

variable (M)

omit [∀ i, Module.Finite 𝕜 (M i)] in
/-- **Separating elements.** For each `j` there is `a ∈ A` acting as the identity on `M j` and
as zero on `M i` for `i ≠ j`. This is the Jacobson-density input: `A` surjects onto the
bicommutant of `𝕄 = ∀ i, M i`, which contains the `j`-th projection. -/
theorem exists_separating (hfin : ∀ i, Module.Finite 𝕜 (M i))
    (hsimp : ∀ i, IsSimpleModule A (M i))
    (hdist : Pairwise (fun i j => ¬ Nonempty (M i ≃ₗ[A] M j)))
    (j : ι) :
    ∃ a : A, ∀ (i : ι) (v : M i), a • v = if i = j then v else (0 : M i) := by
  classical
  haveI : ∀ i, IsSimpleModule A (M i) := hsimp
  haveI : ∀ i, IsSemisimpleModule A (M i) := fun i => inferInstance
  haveI : ∀ i, Module.Finite 𝕜 (M i) := hfin
  -- `𝕄` is finite over its endomorphism ring (it is finite over `𝕜 ⊆ End_A 𝕄`).
  haveI : Module.Finite (End A (Pim M)) (Pim M) :=
    Module.Finite.of_restrictScalars_finite 𝕜 (End A (Pim M)) (Pim M)
  -- The `j`-th projection, viewed as an element of the bicommutant `End_{End_A 𝕄}(𝕄)`.
  let P : End (End A (Pim M)) (Pim M) :=
    { toFun := proj (A := A) M j
      map_add' := (proj (A := A) M j).map_add
      map_smul' := by
        intro f x
        simp only [RingHom.id_apply, Module.End.smul_def]
        exact proj_comm hsimp hdist j f x }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := Pim M) P
  refine ⟨a, fun i v => ?_⟩
  -- `ha` says `a • x = proj j x` for all `x : 𝕄`.
  have key : ∀ x : Pim M, a • x = proj (A := A) M j x := fun x => DFunLike.congr_fun ha x
  -- Evaluate the identity at `Pi.single i v`, component `i`.
  have h1 := congrFun (key (Pi.single i v)) i
  rw [proj_apply] at h1
  rw [Pi.smul_apply, Pi.single_eq_same] at h1
  rw [h1]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij, Pi.single_eq_of_ne hij]

end CharacterIndependence

/-- The representation `A →ₐ[𝕜] End 𝕜 (M i)` given by the module action (`𝕜` central in `A`). -/
def repEnd (i : ι) : A →ₐ[𝕜] Module.End 𝕜 (M i) := Algebra.lsmul 𝕜 𝕜 (M i)

omit [Fintype ι] [DecidableEq ι] [∀ i, Module.Finite 𝕜 (M i)] in
@[simp]
theorem repEnd_apply (i : ι) (a : A) (v : M i) :
    (repEnd M i a : M i →ₗ[𝕜] M i) v = a • v := rfl

/-- The trace-character functional of the `i`-th module: `a ↦ trace_𝕜 (a • · : M i → M i)`. -/
def traceChar (i : ι) : A →ₗ[𝕜] 𝕜 :=
  (LinearMap.trace 𝕜 (M i)).comp (repEnd M i).toLinearMap

omit [Fintype ι] [DecidableEq ι] [∀ i, Module.Finite 𝕜 (M i)] in
@[simp]
theorem traceChar_apply (i : ι) (a : A) :
    traceChar M i a = LinearMap.trace 𝕜 (M i) (repEnd M i a) := rfl

open CharacterIndependence in
omit [DecidableEq ι] in
/-- **Linear independence of trace-character functionals (Dedekind/Artin).**

The trace characters of a finite family of pairwise non-isomorphic finite-dimensional simple
`A`-modules are linearly independent over a characteristic-zero base field `𝕜`. -/
theorem traceCharacter_linearIndependent [CharZero 𝕜]
    (hsimp : ∀ i, IsSimpleModule A (M i))
    (hdist : Pairwise (fun i j => ¬ Nonempty (M i ≃ₗ[A] M j))) :
    LinearIndependent 𝕜 (fun i => (traceChar M i : A →ₗ[𝕜] 𝕜)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  obtain ⟨a, ha⟩ := exists_separating (𝕜 := 𝕜) M (fun _ => inferInstance) hsimp hdist j
  -- For each `i`, the separating element makes `a` act as `if i = j then id else 0` on `M i`.
  have hact : ∀ i, (repEnd M i a : M i →ₗ[𝕜] M i) = if i = j then LinearMap.id else 0 := by
    intro i
    ext v
    rw [repEnd_apply]
    by_cases hij : i = j <;> simp [hij, ha i v]
  -- Hence each trace character evaluates to `if i = j then dim (M i) else 0`.
  have htrace : ∀ i, traceChar M i a = if i = j then (Module.finrank 𝕜 (M i) : 𝕜) else 0 := by
    intro i
    rw [traceChar_apply, hact i]
    by_cases hij : i = j <;> simp [hij, LinearMap.trace_id]
  -- Evaluate the vanishing combination at `a`.
  have happ : (∑ i, g i • (traceChar M i : A →ₗ[𝕜] 𝕜)) a = 0 := by rw [hg]; rfl
  rw [LinearMap.sum_apply] at happ
  simp only [LinearMap.smul_apply, htrace, smul_eq_mul, mul_ite, mul_zero] at happ
  rw [Finset.sum_ite_eq' Finset.univ j] at happ
  simp only [Finset.mem_univ, if_true] at happ
  -- `g j * dim (M j) = 0` with `dim (M j) ≠ 0` forces `g j = 0`.
  haveI := (hsimp j).nontrivial
  have hdim : (Module.finrank 𝕜 (M j) : 𝕜) ≠ 0 := by
    have : 0 < Module.finrank 𝕜 (M j) := Module.finrank_pos
    exact_mod_cast this.ne'
  exact (mul_eq_zero.mp happ).resolve_right hdim

end

end Etingof

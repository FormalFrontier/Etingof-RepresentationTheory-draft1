import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Classes

/-!
# Problem 4.12.5: decomposition of the icosahedral representations of `A₅`

**Problem 4.12.5.** Let `I` be the set of vertices of a regular icosahedron (`|I| = 12`). Let
`F(I)` be the space of complex functions on `I`. The group `G = A₅` of even permutations of
five items acts on the icosahedron, so we get a `12`-dimensional representation of `G` on
`F(I)`.

(a) Decompose this representation into irreducibles (find the multiplicities of all
irreducibles).

(b) Do the same for the representation of `G` on functions on the set of faces (`20`) and the
set of edges (`30`).

## Formalization

`A₅` is `alternatingGroup (Fin 5)`. Its irreducible complex representations have dimensions
`1, 3, 3', 4, 5` (the two `3`-dimensional ones are non-isomorphic). The icosahedral actions are
characterized purely group-theoretically: a transitive action of `A₅` on a `12`/`20`/`30`
element set with point stabilizer of order `5`/`3`/`2` is unique up to isomorphism (all Sylow
`5`-, `3`-subgroups and all involutions of `A₅` are conjugate), and reproduces the vertex /
face / edge action of the icosahedron. We therefore take the action as a hypothesis `act`
together with these transitivity and stabilizer-order conditions.

Given `act : G →* Equiv.Perm (Fin n)`, `permRep act` is the permutation representation on
`Fin n → ℂ`, `(permRep act g f) i = f (act g⁻¹ i)`. Writing `χ(g)` for the number of fixed
points of `act g`, the character inner products give the multiplicities:

* **(a) vertices (`12`):** `χ = (12, 0, 0, 2, 2)` on the classes `(1a, 2a, 3a, 5a, 5b)`, so
  `F(I) ≅ 1 ⊕ 3 ⊕ 3' ⊕ 5` (dimensions `1 + 3 + 3 + 5 = 12`).
* **(b) faces (`20`):** `χ = (20, 0, 2, 0, 0)`, so `≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5`
  (`1 + 3 + 3 + 4 + 4 + 5 = 20`).
* **(b) edges (`30`):** `χ = (30, 2, 0, 0, 0)`, so `≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5³`
  (`1 + 3 + 3 + 4 + 4 + 5 + 5 + 5 = 30`).

Each decomposition is stated as the existence of an internal direct sum of `G`-invariant
irreducible subspaces of the listed dimensions, in which the two `3`-dimensional summands are
non-isomorphic (their subrepresentation characters differ). Statement pass: `sorry` proofs.
-/

noncomputable section

namespace Etingof.Problem4_12_5

/-- The alternating group `A₅` of even permutations of five items. -/
abbrev A5 : Type := ↥(alternatingGroup (Fin 5))

/-- The permutation representation attached to an action `act : G →* Equiv.Perm (Fin n)`, on
the space `Fin n → ℂ` of complex functions on the `n`-element set:
`(permRep act g f) i = f (act g⁻¹ i)`. -/
def permRep {G : Type*} [Group G] {n : ℕ} (act : G →* Equiv.Perm (Fin n)) :
    Representation ℂ G (Fin n → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (act g⁻¹)
  map_one' := by
    ext f i
    simp
  map_mul' g h := by
    ext f i
    simp [LinearMap.funLeft_apply, Module.End.mul_apply, mul_inv_rev, map_mul]

/-- The character of the subrepresentation of `ρ` carried by a `G`-invariant submodule `S`:
the trace of `ρ g` restricted to `S`. -/
def subChar {G : Type*} [Group G] {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : G) : ℂ :=
  LinearMap.trace ℂ S ((ρ g).restrict (hS g))

/-- `IsIrredSub ρ S` says the `G`-invariant submodule `S` carries an irreducible
subrepresentation: it is nonzero and has no `G`-invariant submodule strictly between `⊥` and
`S`. -/
def IsIrredSub {G : Type*} [Group G] {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  S ≠ ⊥ ∧ ∀ T : Submodule ℂ (Fin n → ℂ),
    T ≤ S → (∀ g, ∀ v ∈ T, ρ g v ∈ T) → T = ⊥ ∨ T = S

/-! ## Reusable decomposition engine

The lemmas below are generic in the dimension `n` and the representation `ρ`; none of them
mentions the numbers `12/20/30`. They provide the structural facts shared by the three
decomposition theorems: semisimplicity of any `A₅`-representation, a fixed-point formula for
the character of `permRep`, and the existence of an internal direct-sum decomposition into
`IsIrredSub` invariant subspaces. -/

section Engine

/-- `A₅` has nonzero order in `ℂ` (its order is `60`), so Maschke's theorem applies. -/
instance : NeZero (Nat.card A5 : ℂ) := by
  refine ⟨?_⟩
  have h : Nat.card A5 ≠ 0 := Nat.card_pos.ne'
  exact_mod_cast h

/-- **Semisimplicity (Maschke).** Every `ℂ`-representation of `A₅` is a semisimple
`ℂ[A₅]`-module. This is the Maschke instance applied with `Nat.card A₅ = 60 ≠ 0` in `ℂ`. -/
theorem isSemisimple_asModule {n : ℕ} (ρ : Representation ℂ A5 (Fin n → ℂ)) :
    IsSemisimpleModule (MonoidAlgebra ℂ A5) ρ.asModule :=
  inferInstance

/-- `ρ.asModule` is module-finite over `ℂ[A₅]` (it is finite over `ℂ` and `ℂ ⊆ ℂ[A₅]`). -/
instance instFiniteAsModule {n : ℕ} (ρ : Representation ℂ A5 (Fin n → ℂ)) :
    Module.Finite (MonoidAlgebra ℂ A5) ρ.asModule :=
  Module.Finite.of_restrictScalars_finite ℂ (MonoidAlgebra ℂ A5) ρ.asModule

/-- `permRep act g` is the linear map of the permutation matrix of `act g⁻¹`. -/
lemma permRep_eq_toLin' {n : ℕ} (act : A5 →* Equiv.Perm (Fin n)) (g : A5) :
    (permRep act g) = (((act g⁻¹).permMatrix ℂ).toLin') := by
  apply LinearMap.ext; intro f; funext a
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec]
  rfl

/-- **Fixed-point character formula.** The trace of `permRep act g` on `Fin n → ℂ` equals the
number of fixed points of `act g`. -/
lemma permRep_trace_eq_fixCard {n : ℕ} (act : A5 →* Equiv.Perm (Fin n)) (g : A5) :
    LinearMap.trace ℂ (Fin n → ℂ) (permRep act g)
      = ((Finset.univ.filter (fun i : Fin n => act g i = i)).card : ℂ) := by
  rw [permRep_eq_toLin', Matrix.trace_toLin'_eq, Matrix.trace_permutation]
  have hset : Function.fixedPoints (⇑(act g⁻¹ : Equiv.Perm (Fin n)))
      = (↑(Finset.univ.filter (fun i : Fin n => act g i = i)) : Set (Fin n)) := by
    ext a
    simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
      Finset.mem_univ, true_and, map_inv]
    constructor
    · intro h; exact ((Equiv.symm_apply_eq _).mp h).symm
    · intro h; exact (Equiv.symm_apply_eq _).mpr h.symm
  rw [hset, Set.ncard_coe_finset]

/-- Membership in a subrepresentation is membership in its underlying submodule; the order on
`Subrepresentation ρ` agrees with the order on the underlying submodules. -/
lemma subrep_le_iff {n : ℕ} {ρ : Representation ℂ A5 (Fin n → ℂ)}
    {τ σ : Subrepresentation ρ} : τ ≤ σ ↔ τ.toSubmodule ≤ σ.toSubmodule := Iff.rfl

/-- **`IsIrredSub` as atomicity.** `IsIrredSub ρ σ.toSubmodule` says exactly that the
subrepresentation `σ` is an atom in the lattice of subrepresentations. -/
lemma isIrredSub_iff_isAtom {n : ℕ} {ρ : Representation ℂ A5 (Fin n → ℂ)}
    (σ : Subrepresentation ρ) :
    IsIrredSub ρ σ.toSubmodule ↔ IsAtom σ := by
  constructor
  · rintro ⟨hne, hmax⟩
    refine ⟨fun h => hne (by rw [h]; rfl), fun τ hτ => ?_⟩
    have hle : τ.toSubmodule ≤ σ.toSubmodule := subrep_le_iff.mp hτ.le
    rcases hmax τ.toSubmodule hle (fun g v hv => τ.apply_mem_toSubmodule g hv) with h1 | h2
    · exact Subrepresentation.toSubmodule_injective (by rw [h1]; rfl)
    · exact absurd (Subrepresentation.toSubmodule_injective h2) hτ.ne
  · rintro ⟨hne, hmax⟩
    refine ⟨fun h => hne (Subrepresentation.toSubmodule_injective (by rw [h]; rfl)), ?_⟩
    intro T hT hinv
    by_cases hTeq : T = σ.toSubmodule
    · exact Or.inr hTeq
    · refine Or.inl ?_
      have hτlt : (⟨T, hinv⟩ : Subrepresentation ρ) < σ :=
        lt_of_le_of_ne (subrep_le_iff.mpr hT)
          (fun h => hTeq (congrArg Subrepresentation.toSubmodule h))
      have := hmax _ hτlt
      exact congrArg Subrepresentation.toSubmodule this |>.trans (by rfl)

/-- **`IsIrredSub` ↔ simple subrepresentation bridge.** `IsIrredSub ρ σ.toSubmodule` holds iff
the corresponding `ℂ[A₅]`-submodule `σ.asSubmodule` of `ρ.asModule` is a simple module. -/
lemma isIrredSub_iff_isSimpleModule {n : ℕ} {ρ : Representation ℂ A5 (Fin n → ℂ)}
    (σ : Subrepresentation ρ) :
    IsIrredSub ρ σ.toSubmodule ↔
      IsSimpleModule (MonoidAlgebra ℂ A5) σ.asSubmodule := by
  rw [isIrredSub_iff_isAtom, isSimpleModule_iff_isAtom,
    ← Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff σ]
  rfl

/-- **`subChar` ↔ `FDRep` character bridge.** The ad-hoc restricted-trace `subChar ρ S hS`
agrees with the genuine character of the subrepresentation carried by `S`, packaged as an
`FDRep`. Per-part issues can therefore identify a summand's isomorphism type from its `subChar`
and apply `FDRep.char_iso`. -/
lemma subChar_eq_character {n : ℕ} (ρ : Representation ℂ A5 (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : A5) :
    subChar ρ S hS g
      = (FDRep.of (⟨S, hS⟩ : Subrepresentation ρ).toRepresentation).character g :=
  rfl

/-- **Generic internal decomposition.** Any `ℂ`-representation `ρ` of `A₅` on `Fin n → ℂ`
decomposes as an internal direct sum of finitely many `G`-invariant irreducible subspaces.
This is the structural engine consumed by the three per-part decomposition theorems. -/
theorem exists_isInternal_isIrredSub {n : ℕ} (ρ : Representation ℂ A5 (Fin n → ℂ)) :
    ∃ (m : ℕ) (S : Fin m → Submodule ℂ (Fin n → ℂ)),
      (∀ k, ∀ g : A5, ∀ v ∈ S k, ρ g v ∈ S k) ∧
      DirectSum.IsInternal S ∧ ∀ k, IsIrredSub ρ (S k) := by
  classical
  obtain ⟨s, hind, hsup, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (MonoidAlgebra ℂ A5) ρ.asModule
  have simple' : ∀ N : ↥s, IsSimpleModule (MonoidAlgebra ℂ A5) ↥(N.1) := fun N => hsimple N.1 N.2
  haveI hfin : Finite ↥s := by
    apply WellFoundedGT.finite_of_iSupIndep ((sSupIndep_iff s).mp hind)
    intro N
    haveI := simple' N
    exact (N.1.nontrivial_iff_ne_bot).mp (IsSimpleModule.nontrivial (MonoidAlgebra ℂ A5) _)
  set e := Finite.equivFin ↥s with he
  set N : Fin (Nat.card ↥s) → Submodule (MonoidAlgebra ℂ A5) ρ.asModule :=
    fun k => ((e.symm k : ↥s) : Submodule (MonoidAlgebra ℂ A5) ρ.asModule) with hNdef
  have hiN : iSupIndep N := ((sSupIndep_iff s).mp hind).comp e.symm.injective
  have hsupN : (⨆ k, N k) = ⊤ := by
    calc (⨆ k, N k) = ⨆ x : ↥s, (x : Submodule (MonoidAlgebra ℂ A5) ρ.asModule) :=
            Equiv.iSup_comp e.symm
      _ = sSup s := (sSup_eq_iSup' s).symm
      _ = ⊤ := hsup
  have hInternalN : DirectSum.IsInternal N :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hiN hsupN
  refine ⟨Nat.card ↥s, fun k => (Subrepresentation.ofSubmodule' (N k)).toSubmodule, ?_, ?_, ?_⟩
  · exact fun k g v hv => (Subrepresentation.ofSubmodule' (N k)).apply_mem_toSubmodule g hv
  · exact hInternalN
  · intro k
    set σ := Subrepresentation.ofSubmodule' (N k) with hσ
    have hsk : IsSimpleModule (MonoidAlgebra ℂ A5) σ.asSubmodule := simple' (e.symm k)
    exact (isIrredSub_iff_isSimpleModule σ).mpr hsk

end Engine

/-! ## Fixed-point counts from orbit-stabilizer

The three decomposition theorems need the value of the permutation character
`χ_perm(g) = #{ i | act g i = i }` on the five conjugacy-class representatives, computed purely
from transitivity plus the point-stabilizer order. The lemmas below provide the shared
group-theoretic core: a Burnside/orbit-stabilizer identity relating the fixed-point count to the
number of `x` with `x⁻¹ g x` in the stabilizer, and the conjugation-invariance of that count.
Both are generic in the acting group `G` and the degree `n`. -/

section FixCount

open Finset

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {n : ℕ}

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-- The conjugated element `x⁻¹ g x` fixes `i₀` iff `g` fixes `act x i₀`. -/
lemma act_conj_fix_iff (act : G →* Equiv.Perm (Fin n)) (g x : G) (i₀ : Fin n) :
    (act (x⁻¹ * g * x) i₀ = i₀) ↔ (act g (act x i₀) = act x i₀) := by
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
  exact Equiv.symm_apply_eq (act x)

/-- Every fiber of the orbit map `x ↦ act x i₀` (over a point `i` in the orbit) has the same
cardinality as the stabilizer of `i₀`. -/
lemma orbit_fiber_card (act : G →* Equiv.Perm (Fin n)) (i₀ i : Fin n) (xi : G)
    (hxi : act xi i₀ = i) :
    (univ.filter (fun x : G => act x i₀ = i)).card
      = (univ.filter (fun x : G => act x i₀ = i₀)).card := by
  apply Finset.card_nbij' (fun x => xi⁻¹ * x) (fun x => xi * x)
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [map_mul, Equiv.Perm.mul_apply, map_inv, hx, ← hxi]; simp
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [map_mul, Equiv.Perm.mul_apply, hx, hxi]
  · intro x _; simp
  · intro x _; simp

/-- **Core orbit-stabilizer identity.** For a transitive action of `G` on `Fin n`, the number of
fixed points of `g` times the order of a point stabilizer equals the number of `x` with
`x⁻¹ g x` fixing the base point `i₀`. -/
lemma fix_mul_stab_card (act : G →* Equiv.Perm (Fin n)) (g : G) (i₀ : Fin n)
    (htrans : ∀ j : Fin n, ∃ x : G, act x i₀ = j) :
    (univ.filter (fun i : Fin n => act g i = i)).card
        * (univ.filter (fun x : G => act x i₀ = i₀)).card
      = (univ.filter (fun x : G => act (x⁻¹ * g * x) i₀ = i₀)).card := by
  have key : (univ.filter (fun x : G => act (x⁻¹ * g * x) i₀ = i₀))
      = (univ.filter (fun x : G => act g (act x i₀) = act x i₀)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, act_conj_fix_iff]
  rw [key]
  symm
  rw [card_eq_sum_card_fiberwise (f := fun x : G => act x i₀)
      (t := (univ : Finset (Fin n))) (by intro x _; exact mem_univ _)]
  have hsum : ∀ i ∈ (univ : Finset (Fin n)),
      (univ.filter (fun x : G => act g (act x i₀) = act x i₀ ∧ act x i₀ = i)).card
        = if act g i = i then (univ.filter (fun x : G => act x i₀ = i₀)).card else 0 := by
    intro i _
    by_cases hgi : act g i = i
    · rw [if_pos hgi]
      obtain ⟨xi, hxi⟩ := htrans i
      rw [← orbit_fiber_card act i₀ i xi hxi]
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · intro h2; exact ⟨by rw [h2]; exact hgi, h2⟩
    · rw [if_neg hgi, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      rintro ⟨h1, h2⟩
      rw [h2] at h1; exact hgi h1
  have hrw : (fun i => (univ.filter (fun x : G => act g (act x i₀) = act x i₀)
        |>.filter (fun x => act x i₀ = i)).card)
      = (fun i => (univ.filter
          (fun x : G => act g (act x i₀) = act x i₀ ∧ act x i₀ = i)).card) := by
    funext i; congr 1; rw [Finset.filter_filter]
  rw [show (∑ i : Fin n, (univ.filter (fun x : G => act g (act x i₀) = act x i₀)
        |>.filter (fun x => act x i₀ = i)).card)
      = ∑ i : Fin n, (univ.filter (fun x : G => act g (act x i₀) = act x i₀ ∧ act x i₀ = i)).card
      from by rw [hrw]]
  rw [Finset.sum_congr rfl hsum, ← Finset.sum_filter, Finset.sum_const_nat (fun _ _ => rfl)]

/-- **Conjugation invariance of the twisted count.** If `T = c S c⁻¹` (expressed pointwise as
`y ∈ T ↔ c⁻¹ y c ∈ S`), then the number of `x` with `x⁻¹ g x ∈ S` equals the number with
`x⁻¹ g x ∈ T`. -/
lemma conj_count_eq (g c : G) (S T : Subgroup G)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : ∀ y : G, y ∈ T ↔ c⁻¹ * y * c ∈ S) :
    (univ.filter (fun x : G => x⁻¹ * g * x ∈ S)).card
      = (univ.filter (fun x : G => x⁻¹ * g * x ∈ T)).card := by
  apply Finset.card_nbij' (fun x => x * c⁻¹) (fun x => x * c)
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [h]
    have : c⁻¹ * ((x * c⁻¹)⁻¹ * g * (x * c⁻¹)) * c = x⁻¹ * g * x := by group
    rw [this]; exact hx
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [h] at hx
    have : c⁻¹ * (x⁻¹ * g * x) * c = (x * c)⁻¹ * g * (x * c) := by group
    rw [this] at hx; exact hx
  · intro x _; simp [mul_assoc]
  · intro x _; simp [mul_assoc]

end FixCount

/-- **Part (a): vertices.** For the icosahedral vertex action of `A₅` — any transitive action
on `12` points with point stabilizers of order `5` — the representation on `F(I) = Fin 12 → ℂ`
decomposes as `1 ⊕ 3 ⊕ 3' ⊕ 5`: an internal direct sum of four `G`-invariant irreducible
subspaces of dimensions `1, 3, 3, 5`, with the two `3`-dimensional summands non-isomorphic. -/
theorem vertices_decomposition
    (act : A5 →* Equiv.Perm (Fin 12))
    (htrans : ∀ i j : Fin 12, ∃ g : A5, act g i = j)
    (hstab : ∀ i : Fin 12, Nat.card {g : A5 // act g i = i} = 5) :
    ∃ (S : Fin 4 → Submodule ℂ (Fin 12 → ℂ))
      (hS : ∀ k, ∀ g : A5, ∀ v ∈ S k, permRep act g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrredSub (permRep act) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 5 ∧
      ∃ g : A5, subChar (permRep act) (S 1) (hS 1) g ≠ subChar (permRep act) (S 2) (hS 2) g := by
  sorry

/-- **Part (b): faces.** For the icosahedral face action of `A₅` — any transitive action on
`20` points with point stabilizers of order `3` — the representation on `Fin 20 → ℂ`
decomposes as `1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5`: an internal direct sum of six `G`-invariant irreducible
subspaces of dimensions `1, 3, 3, 4, 4, 5`, with the two `3`-dimensional summands
non-isomorphic. -/
theorem faces_decomposition
    (act : A5 →* Equiv.Perm (Fin 20))
    (htrans : ∀ i j : Fin 20, ∃ g : A5, act g i = j)
    (hstab : ∀ i : Fin 20, Nat.card {g : A5 // act g i = i} = 3) :
    ∃ (S : Fin 6 → Submodule ℂ (Fin 20 → ℂ))
      (hS : ∀ k, ∀ g : A5, ∀ v ∈ S k, permRep act g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrredSub (permRep act) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 4 ∧
      Module.finrank ℂ (S 4) = 4 ∧ Module.finrank ℂ (S 5) = 5 ∧
      ∃ g : A5, subChar (permRep act) (S 1) (hS 1) g ≠ subChar (permRep act) (S 2) (hS 2) g := by
  sorry

/-- **Part (b): edges.** For the icosahedral edge action of `A₅` — any transitive action on
`30` points with point stabilizers of order `2` — the representation on `Fin 30 → ℂ`
decomposes as `1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5³`: an internal direct sum of eight `G`-invariant
irreducible subspaces of dimensions `1, 3, 3, 4, 4, 5, 5, 5`, with the two `3`-dimensional
summands non-isomorphic. -/
theorem edges_decomposition
    (act : A5 →* Equiv.Perm (Fin 30))
    (htrans : ∀ i j : Fin 30, ∃ g : A5, act g i = j)
    (hstab : ∀ i : Fin 30, Nat.card {g : A5 // act g i = i} = 2) :
    ∃ (S : Fin 8 → Submodule ℂ (Fin 30 → ℂ))
      (hS : ∀ k, ∀ g : A5, ∀ v ∈ S k, permRep act g v ∈ S k),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrredSub (permRep act) (S k)) ∧
      Module.finrank ℂ (S 0) = 1 ∧ Module.finrank ℂ (S 1) = 3 ∧
      Module.finrank ℂ (S 2) = 3 ∧ Module.finrank ℂ (S 3) = 4 ∧
      Module.finrank ℂ (S 4) = 4 ∧ Module.finrank ℂ (S 5) = 5 ∧
      Module.finrank ℂ (S 6) = 5 ∧ Module.finrank ℂ (S 7) = 5 ∧
      ∃ g : A5, subChar (permRep act) (S 1) (hS 1) g ≠ subChar (permRep act) (S 2) (hS 2) g := by
  sorry

end Etingof.Problem4_12_5

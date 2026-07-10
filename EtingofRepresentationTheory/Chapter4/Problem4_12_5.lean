import Mathlib

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

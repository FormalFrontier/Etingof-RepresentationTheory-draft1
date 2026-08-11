import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Classes
import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Complete
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3

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

`Chapter4/Problem4_12_5_CosetModels.lean` constructs such actions (as left translation on the
coset spaces `A₅ ⧸ ⟨5-cycle⟩`, `A₅ ⧸ ⟨3-cycle⟩`, `A₅ ⧸ ⟨involution⟩`), proves the uniqueness
claimed above, and derives the hypothesis-free corollaries
`vertices_decomposition_icosahedral`, `faces_decomposition_icosahedral`,
`edges_decomposition_icosahedral`.

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
non-isomorphic (their subrepresentation characters differ). These decompositions are proved
(`sorry`-free).
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

/-! ## Reusable decomposition lemmas

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

/-- **`IsIrredSub` as a simple submodule.** `IsIrredSub ρ σ.toSubmodule` holds iff
the corresponding `ℂ[A₅]`-submodule `σ.asSubmodule` of `ρ.asModule` is a simple module. -/
lemma isIrredSub_iff_isSimpleModule {n : ℕ} {ρ : Representation ℂ A5 (Fin n → ℂ)}
    (σ : Subrepresentation ρ) :
    IsIrredSub ρ σ.toSubmodule ↔
      IsSimpleModule (MonoidAlgebra ℂ A5) σ.asSubmodule := by
  rw [isIrredSub_iff_isAtom, isSimpleModule_iff_isAtom,
    ← Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff σ]
  rfl

/-- **`subChar` as an `FDRep` character.** The restricted-trace `subChar ρ S hS`
agrees with the character of the subrepresentation carried by `S`, packaged as an
`FDRep`. One can therefore identify a summand's isomorphism type from its `subChar`
and apply `FDRep.char_iso`. -/
lemma subChar_eq_character {n : ℕ} (ρ : Representation ℂ A5 (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : A5) :
    subChar ρ S hS g
      = (FDRep.of (⟨S, hS⟩ : Subrepresentation ρ).toRepresentation).character g :=
  rfl

/-- **Generic internal decomposition.** Any `ℂ`-representation `ρ` of `A₅` on `Fin n → ℂ`
decomposes as an internal direct sum of finitely many `G`-invariant irreducible subspaces.
This is the structural result used by the three per-part decomposition theorems. -/
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

/-! ### Isotypic / multiplicity layer

The generic decomposition `exists_isInternal_isIrredSub` produces an internal direct sum of
`IsIrredSub` summands but records no dimension or isomorphism-type information. This layer
identifies the isomorphism type of each summand against the completeness list `irrepA5`,
turns the fixed-point character into a sum over summand characters (trace additivity, together
with the summand dimensions), and, via character orthonormality (`FDRep.char_orthonormal`),
computes the multiplicity of each irreducible as a character inner product. These are the shared
facts used by the three per-part decomposition theorems. -/

open CategoryTheory

open Etingof.Example4_8_1.A5 (irrepA5 irrepA5_finrank irrepA5_pairwise irrepA5_simple
  simple_iso_irrepA5 classRepA5)

/-- `|A₅| = 60` is invertible in `ℂ`, so the character orthonormality relation applies. -/
noncomputable instance : Invertible (Fintype.card A5 : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Two of the five `irrepA5` are isomorphic exactly when their indices agree (they are pairwise
non-isomorphic, `irrepA5_pairwise`). -/
lemma irrepA5_iso_iff (a b : Fin 5) : Nonempty (irrepA5 a ≅ irrepA5 b) ↔ a = b := by
  constructor
  · intro h; by_contra hne; exact irrepA5_pairwise a b hne h
  · rintro rfl; exact ⟨Iso.refl _⟩

/-- **Character additivity.** For an internal direct-sum decomposition `S` of the permutation
representation into invariant subspaces, the fixed-point character of `permRep act g` is the sum
of the subrepresentation characters `subChar (S k)`. This is trace additivity over
`DirectSum.IsInternal` (`LinearMap.trace_eq_sum_trace_restrict`): each `permRep act g` preserves
every `S k`. -/
lemma fixCard_eq_sum_subChar {n m : ℕ} (act : A5 →* Equiv.Perm (Fin n))
    (S : Fin m → Submodule ℂ (Fin n → ℂ))
    (hS : ∀ k, ∀ g : A5, ∀ v ∈ S k, permRep act g v ∈ S k)
    (hInt : DirectSum.IsInternal S) (g : A5) :
    ((Finset.univ.filter (fun i : Fin n => act g i = i)).card : ℂ)
      = ∑ k, subChar (permRep act) (S k) (hS k) g := by
  have hmaps : ∀ k, Set.MapsTo (permRep act g) (S k) (S k) := fun k v hv => hS k g v hv
  rw [← permRep_trace_eq_fixCard]
  exact LinearMap.trace_eq_sum_trace_restrict hInt hmaps

/-- The `FDRep ℂ A₅` carried by a `permRep`-invariant submodule `S`: the subrepresentation on
`S`, packaged as a finite-dimensional representation. Its character is `subChar`
(`subChar_eq_character`). -/
def subFDRep {n : ℕ} (ρ : Representation ℂ A5 (Fin n → ℂ)) (S : Submodule ℂ (Fin n → ℂ))
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : FDRep ℂ A5 :=
  FDRep.of (⟨S, hS⟩ : Subrepresentation ρ).toRepresentation

/-- `subChar` is the character of the packaged `subFDRep`. -/
lemma subChar_eq_subFDRep_character {n : ℕ} (ρ : Representation ℂ A5 (Fin n → ℂ))
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : A5) :
    subChar ρ S hS g = (subFDRep ρ S hS).character g :=
  rfl

/-- The `ℂ[A₅]`-module `(σ.toRepresentation).asModule` carried by a subrepresentation `σ` is, as a
`ℂ[A₅]`-module, the corresponding submodule `σ.asSubmodule` of `ρ.asModule`: both have underlying
set `σ.toSubmodule`, and on `single g t` both actions send `y ↦ t • ρ g y`. (Inlined here to avoid
a `Chapter4 → Chapter5` import; cf. `Etingof.toRepAsModuleEquiv`.) -/
private def toRepAsModuleEquiv {n : ℕ} {ρ : Representation ℂ A5 (Fin n → ℂ)}
    (σ : Subrepresentation ρ) :
    (σ.toRepresentation).asModule ≃ₗ[MonoidAlgebra ℂ A5] σ.asSubmodule where
  toFun y := ⟨((σ.toRepresentation).asModuleEquiv y).1, ((σ.toRepresentation).asModuleEquiv y).2⟩
  map_add' y z := by apply Subtype.ext; simp
  map_smul' c y := by
    apply Subtype.ext
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add c₁ c₂ h₁ h₂ =>
        simp only [add_smul, RingHom.id_apply] at h₁ h₂ ⊢
        rw [Submodule.coe_add, ← h₁, ← h₂]; rfl
    | single g t =>
        simp only [RingHom.id_apply, SetLike.val_smul]
        rw [Representation.single_smul, Representation.single_smul]; rfl
  invFun x := (σ.toRepresentation).asModuleEquiv.symm ⟨x.1, x.2⟩
  left_inv y := by simp
  right_inv x := by apply Subtype.ext; simp

/-- **`IsIrredSub` summands are simple.** An `IsIrredSub` invariant submodule carries a simple
object of `FDRep ℂ A₅` (via `isIrredSub_iff_isSimpleModule`, the `asSubmodule ≃ asModule` transport,
and the module-to-representation simplicity result `simple_fdRepOf_of_isSimpleModule`). -/
lemma subFDRep_simple {n : ℕ} {ρ : Representation ℂ A5 (Fin n → ℂ)}
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S)
    (h : IsIrredSub ρ S) : Simple (subFDRep ρ S hS) := by
  haveI hsimple : IsSimpleModule (MonoidAlgebra ℂ A5)
      (⟨S, hS⟩ : Subrepresentation ρ).asSubmodule :=
    (isIrredSub_iff_isSimpleModule ⟨S, hS⟩).mp h
  haveI : IsSimpleModule (MonoidAlgebra ℂ A5)
      ((⟨S, hS⟩ : Subrepresentation ρ).toRepresentation).asModule :=
    IsSimpleModule.congr (toRepAsModuleEquiv ⟨S, hS⟩)
  exact Etingof.simple_fdRepOf_of_isSimpleModule _

/-- **Type classification of a summand.** An `IsIrredSub` summand is isomorphic to some
`irrepA5 t` (completeness). -/
lemma exists_subFDRep_iso_irrepA5 {n : ℕ} {ρ : Representation ℂ A5 (Fin n → ℂ)}
    (S : Submodule ℂ (Fin n → ℂ)) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S)
    (h : IsIrredSub ρ S) :
    ∃ t : Fin 5, Nonempty (subFDRep ρ S hS ≅ irrepA5 t) := by
  haveI := subFDRep_simple S hS h
  exact simple_iso_irrepA5 (subFDRep ρ S hS)

/-- **Typed isotypic decomposition.** Any permutation representation `permRep act`
of `A₅` decomposes as an internal direct sum of `IsIrredSub` summands `S k`, each carrying a
well-defined isomorphism type `type k : Fin 5` such that:

* `subChar (S k) = (irrepA5 (type k)).character` (each summand's character is a table row);
* `finrank ℂ (S k) = ![1,3,3,4,5] (type k)` (its dimension);
* the number of summands of type `i` equals the character inner product
  `⟨χ_perm, χ_{irrepA5 i}⟩` (multiplicity, via `FDRep.char_orthonormal` and trace additivity).

The three per-part decomposition theorems use this: they compute the fixed-point character
`χ_perm` explicitly and read off the multiplicities from the last clause. -/
theorem exists_typed_isotypic_decomposition {n : ℕ} (act : A5 →* Equiv.Perm (Fin n)) :
    ∃ (m : ℕ) (S : Fin m → Submodule ℂ (Fin n → ℂ))
      (hS : ∀ k, ∀ g : A5, ∀ v ∈ S k, permRep act g v ∈ S k)
      (type : Fin m → Fin 5),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrredSub (permRep act) (S k)) ∧
      (∀ k g, subChar (permRep act) (S k) (hS k) g = (irrepA5 (type k)).character g) ∧
      (∀ k, Module.finrank ℂ (S k) = ![1, 3, 3, 4, 5] (type k)) ∧
      ∀ i : Fin 5,
        ((Finset.univ.filter (fun k => type k = i)).card : ℂ)
          = ⅟(Fintype.card A5 : ℂ) • ∑ g : A5,
              ((Finset.univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
                * (irrepA5 i).character g⁻¹ := by
  classical
  obtain ⟨m, S, hS, hInt, hIrr⟩ := exists_isInternal_isIrredSub (permRep act)
  choose type hiso using fun k => exists_subFDRep_iso_irrepA5 (S k) (hS k) (hIrr k)
  -- Each summand's `subChar` is the character of its type.
  have hchar : ∀ k g, subChar (permRep act) (S k) (hS k) g = (irrepA5 (type k)).character g := by
    intro k g
    rw [subChar_eq_subFDRep_character]
    exact congrFun (FDRep.char_iso (hiso k).some) g
  -- Each summand's dimension is the tabulated value.
  have hfr : ∀ k, Module.finrank ℂ (S k) = ![1, 3, 3, 4, 5] (type k) := by
    intro k
    have h1 : (subFDRep (permRep act) (S k) (hS k)).character 1
        = (irrepA5 (type k)).character 1 := congrFun (FDRep.char_iso (hiso k).some) 1
    rw [FDRep.char_one, FDRep.char_one] at h1
    have h2 : Module.finrank ℂ (subFDRep (permRep act) (S k) (hS k))
        = Module.finrank ℂ (irrepA5 (type k)) := by exact_mod_cast h1
    rw [irrepA5_finrank] at h2
    exact h2
  refine ⟨m, S, hS, type, hInt, hIrr, hchar, hfr, ?_⟩
  intro i
  -- The fixed-point character is the sum of the type characters (additivity + `hchar`).
  have hperm : ∀ g : A5,
      ((Finset.univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
        = ∑ k, (irrepA5 (type k)).character g := by
    intro g
    rw [fixCard_eq_sum_subChar act S hS hInt g]
    exact Finset.sum_congr rfl fun k _ => hchar k g
  -- Multiplicity = inner product, term by term via `char_orthonormal`.
  have hcard : ((Finset.univ.filter (fun k => type k = i)).card : ℂ)
      = ∑ k : Fin m, ⅟(Fintype.card A5 : ℂ) • ∑ g : A5,
          (irrepA5 (type k)).character g * (irrepA5 i).character g⁻¹ := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun k _ => ?_
    haveI := irrepA5_simple (type k)
    haveI := irrepA5_simple i
    rw [smul_eq_mul, invOf_eq_inv]
    rw [← Nat.card_eq_fintype_card]
    rw [FDRep.char_orthonormal (irrepA5 (type k)) (irrepA5 i), irrepA5_iso_iff]
    by_cases h : type k = i <;> simp [h]
  rw [hcard]
  -- Pull the scalar out, swap the order of summation, factor, and fold in `hperm`.
  rw [← Finset.smul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hperm g, Finset.sum_mul]

/-- **Sorted isotypic decomposition.** The typed decomposition of
`exists_typed_isotypic_decomposition`, reindexed by `Tuple.sort` so that `type` is monotone. One
computes the multiplicity vector `mult i = ⟨χ_perm, χ_{irrepA5 i}⟩` from the last clause;
monotonicity then pins down the whole summand list in nondecreasing type order, realising each type
`i` exactly `mult i` times (with dimensions `![1,3,3,4,5]`). This is the shape the three per-part
decomposition theorems reindex to. The `3 ≇ 3'` distinction is available through
`hchar`: two summands of types `1` and `2` have `subChar` differing at `classRepA5 3`, since
`(irrepA5 1).character` and `(irrepA5 2).character` differ there (`irrepA5_pairwise`). -/
theorem exists_sorted_isotypic_decomposition {n : ℕ} (act : A5 →* Equiv.Perm (Fin n)) :
    ∃ (m : ℕ) (S : Fin m → Submodule ℂ (Fin n → ℂ))
      (hS : ∀ k, ∀ g : A5, ∀ v ∈ S k, permRep act g v ∈ S k)
      (type : Fin m → Fin 5),
      DirectSum.IsInternal S ∧
      (∀ k, IsIrredSub (permRep act) (S k)) ∧
      Monotone type ∧
      (∀ k g, subChar (permRep act) (S k) (hS k) g = (irrepA5 (type k)).character g) ∧
      (∀ k, Module.finrank ℂ (S k) = ![1, 3, 3, 4, 5] (type k)) ∧
      ∀ i : Fin 5,
        ((Finset.univ.filter (fun k => type k = i)).card : ℂ)
          = ⅟(Fintype.card A5 : ℂ) • ∑ g : A5,
              ((Finset.univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
                * (irrepA5 i).character g⁻¹ := by
  classical
  obtain ⟨m, S, hS, type, hInt, hIrr, hchar, hfr, hmult⟩ :=
    exists_typed_isotypic_decomposition act
  set e := Tuple.sort type with he
  refine ⟨m, S ∘ e, fun k => hS (e k), type ∘ e, ?_, fun k => hIrr (e k),
    Tuple.monotone_sort type, fun k g => hchar (e k) g, fun k => hfr (e k), ?_⟩
  · -- Reindexing an internal direct sum by a permutation is again internal.
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hInt ⊢
    obtain ⟨hind, hsup⟩ := hInt
    exact ⟨hind.comp e.injective, by rw [← hsup]; exact Equiv.iSup_comp e⟩
  · -- The type multiplicities are permutation-invariant.
    intro i
    rw [← hmult i]
    congr 1
    rw [← Finset.card_image_of_injective (Finset.univ.filter (fun k => (type ∘ e) k = i))
      e.injective]
    congr 1
    ext j
    simp only [Function.comp_apply, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact hk
    · intro hj; exact ⟨e.symm j, by simpa using hj, by simp⟩

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

/-! ## Fixed-point characters of the icosahedral actions

We now specialise the orbit-stabilizer core to `A₅` and compute the fixed-point character
`χ_perm(g) = #{ i | act g i = i }` on the five class representatives `classRepA5 j`
(ordered as `1a, 3a, 2a, 5a, 5b`, matching `classRepA5`/`chiA5`). The point stabilizer, of prime
order `p`, is conjugate to the concrete cyclic subgroup `⟨classRepA5 k⟩`, by Sylow's theorem for
`p = 5, 3` (where the stabilizer is a full Sylow subgroup), and by the conjugacy of involutions
for `p = 2`. The twisted counts `#{ x | x⁻¹ g x ∈ ⟨classRepA5 k⟩ }` are then finite `decide`
computations over `A₅`. -/

section A5FixCounts

open Finset Etingof.Example4_8_1.A5
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

variable {N : ℕ}

/-- Point stabilizer of `act` at `i₀`, as a subgroup of `A₅`. -/
def stabSub (act : A5 →* Equiv.Perm (Fin N)) (i₀ : Fin N) : Subgroup A5 where
  carrier := {a | act a i₀ = i₀}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb; simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Equiv.Perm.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha; simp only [Set.mem_setOf_eq] at *
    rw [map_inv]; exact (Equiv.symm_apply_eq (act a)).mpr ha.symm

@[simp] lemma mem_stabSub (act : A5 →* Equiv.Perm (Fin N)) (i₀ : Fin N) (a : A5) :
    a ∈ stabSub act i₀ ↔ act a i₀ = i₀ := Iff.rfl

/-- `|A₅| = 60`. -/
lemma card_A5 : Nat.card A5 = 60 := card_G

/-- `#{x | x⁻¹ g x ∈ ⟨a⟩}` computed from the fixed-point count, given a conjugator taking the
concrete cyclic subgroup `⟨a⟩` into the point stabilizer at `0`. -/
lemma fix_mul_stab_eq_twisted [NeZero N] (act : A5 →* Equiv.Perm (Fin N)) (a g : A5)
    (htrans : ∀ i j : Fin N, ∃ x : A5, act x i = j) (c : A5)
    (hconj : ∀ y : A5, y ∈ Subgroup.zpowers a ↔ c⁻¹ * y * c ∈ stabSub act 0) :
    (univ.filter (fun i : Fin N => act g i = i)).card
        * (univ.filter (fun x : A5 => act x 0 = 0)).card
      = (univ.filter (fun x : A5 => x⁻¹ * g * x ∈ Subgroup.zpowers a)).card := by
  haveI : DecidablePred (· ∈ stabSub act 0) := Classical.decPred _
  haveI : DecidablePred (· ∈ Subgroup.zpowers a) := Classical.decPred _
  rw [fix_mul_stab_card act g 0 (fun j => htrans 0 j)]
  have hPeq : (univ.filter (fun x : A5 => act (x⁻¹ * g * x) 0 = 0)).card
      = (univ.filter (fun x : A5 => x⁻¹ * g * x ∈ stabSub act 0)).card := by
    apply congrArg; ext x; simp only [mem_filter, mem_univ, true_and, mem_stabSub]
  rw [hPeq]
  convert conj_count_eq (S := stabSub act 0) (T := Subgroup.zpowers a) g c hconj using 2
  exact Finset.filter_congr_decidable _ _ _

/-- The stabilizer-card filter equals `p` from the `Nat.card` hypothesis. -/
lemma stab_filter_card (act : A5 →* Equiv.Perm (Fin N)) (i₀ : Fin N) (p : ℕ)
    (hstab : Nat.card {x : A5 // act x i₀ = i₀} = p) :
    (univ.filter (fun x : A5 => act x i₀ = i₀)).card = p := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hstab; exact hstab

/-- Membership in the finite cyclic subgroup `⟨a⟩` as an explicit `range`-image predicate. -/
lemma mem_zpowers_range (a : A5) (m : ℕ) (h : orderOf a = m) (y : A5) :
    y ∈ Subgroup.zpowers a ↔ y ∈ (Finset.range m).image (a ^ ·) := by
  have hy := (isOfFinOrder_of_finite a).mem_zpowers_iff_mem_range_orderOf (y := y)
  rwa [h] at hy

/-- **Sylow conjugator.** When `⟨a⟩` and the point stabilizer both have prime order `p` equal to
the full `p`-part of `|A₅|`, they are conjugate (Sylow's second theorem). -/
lemma exists_conj_stab_sylow [NeZero N] {p : ℕ} [Fact p.Prime]
    (act : A5 →* Equiv.Perm (Fin N)) (a : A5)
    (hord : orderOf a = p) (hpfact : (Nat.card A5).factorization p = 1)
    (hstabc : Nat.card (stabSub act 0) = p) :
    ∃ c : A5, ∀ y : A5, y ∈ Subgroup.zpowers a ↔ c⁻¹ * y * c ∈ stabSub act 0 := by
  let P : Sylow p A5 := Sylow.ofCard (stabSub act 0) (by rw [hstabc, hpfact, pow_one])
  have hQc : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
  let Q : Sylow p A5 := Sylow.ofCard (Subgroup.zpowers a) (by rw [hQc, hpfact, pow_one])
  obtain ⟨cc, hcc⟩ := MulAction.exists_smul_eq A5 P Q
  refine ⟨cc, fun y => ?_⟩
  have hco : (Q : Subgroup A5) = MulAut.conj cc • (P : Subgroup A5) := by rw [← hcc]; rfl
  have hPc : (P : Subgroup A5) = stabSub act 0 := Sylow.coe_ofCard _ _
  have hQcoe : (Q : Subgroup A5) = Subgroup.zpowers a := Sylow.coe_ofCard _ _
  rw [← hQcoe, ← hPc, hco, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]

/-- Every involution of `A₅` lies in class `2a` (index `2`). -/
lemma classIdx_of_involution (s : A5) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    classIdxA5 s = 2 := by
  revert s; decide

/-- Conjugation carries `⟨t⟩` to `⟨c t c⁻¹⟩`. -/
lemma conj_smul_zpowers (c t : A5) :
    MulAut.conj c • Subgroup.zpowers t = Subgroup.zpowers (c * t * c⁻¹) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [conj_zpow, hk]; group⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [conj_zpow] at hk; rw [← hk]; group⟩

/-- **Involution conjugator.** The order-`2` point stabilizer is conjugate to `⟨classRepA5 2⟩`,
because all involutions of `A₅` are conjugate (a single class). This is the `p = 2` analogue of
`exists_conj_stab_sylow`, where the stabilizer is *not* a full Sylow subgroup. -/
lemma exists_conj_stab_invol [NeZero N] (act : A5 →* Equiv.Perm (Fin N))
    (hstabc : Nat.card (stabSub act 0) = 2) :
    ∃ c : A5, ∀ y : A5,
      y ∈ Subgroup.zpowers (classRepA5 2) ↔ c⁻¹ * y * c ∈ stabSub act 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Nontrivial (stabSub act 0) := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  obtain ⟨s, hs_mem, hs_ne⟩ := (stabSub act 0).nontrivial_iff_exists_ne_one.mp inferInstance
  have hdvd : orderOf s ∣ 2 := by
    rw [← hstabc]
    have := orderOf_dvd_natCard (⟨s, hs_mem⟩ : stabSub act 0)
    rwa [Subgroup.orderOf_mk] at this
  have hord2 : orderOf s = 2 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hdvd) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs_ne
    · exact h
  have hs2 : s ^ 2 = 1 := by rw [← hord2]; exact pow_orderOf_eq_one s
  have hcl : classIdxA5 s = 2 := classIdx_of_involution s hs2 hs_ne
  obtain ⟨c, hc⟩ := classIdxA5_spec s
  rw [hcl] at hc
  refine ⟨c⁻¹, fun y => ?_⟩
  have hzs : Subgroup.zpowers s = stabSub act 0 := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hs_mem
    · rw [Nat.card_zpowers, hord2, hstabc]
  have hstabeq : (stabSub act 0 : Subgroup A5)
      = MulAut.conj c • Subgroup.zpowers (classRepA5 2) := by
    rw [conj_smul_zpowers, hc, hzs]
  rw [hstabeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, inv_inv]
  constructor
  · intro hy; rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group]; exact hy
  · intro hy; rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at hy; exact hy

/-! ### Orders and prime factorizations for the three concrete generators -/

lemma ord_cr3 : orderOf (classRepA5 3) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

lemma ord_cr1 : orderOf (classRepA5 1) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

lemma ord_cr2 : orderOf (classRepA5 2) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

lemma fact5 : (Nat.card A5).factorization 5 = 1 := by
  rw [card_A5, show (60 : ℕ) = 5 * 12 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

lemma fact3 : (Nat.card A5).factorization 3 = 1 := by
  rw [card_A5, show (60 : ℕ) = 3 * 20 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

/-! ### Twisted counts (`decide` over `A₅`) -/

/-- Rewrite the twisted-membership filter into the explicit `range`-image form for `decide`. -/
lemma twisted_filter_eq (a g : A5) (m : ℕ) (h : orderOf a = m) :
    (univ.filter (fun x : A5 => x⁻¹ * g * x ∈ Subgroup.zpowers a))
      = (univ.filter (fun x : A5 => x⁻¹ * g * x ∈ (Finset.range m).image (a ^ ·))) := by
  ext x; simp only [mem_filter, mem_univ, true_and]; exact mem_zpowers_range _ m h _

lemma twisted_p5 (j : Fin 5) :
    (univ.filter (fun x : A5 => x⁻¹ * classRepA5 j * x ∈ Subgroup.zpowers (classRepA5 3))).card
      = ![60, 0, 0, 10, 10] j := by
  rw [twisted_filter_eq (classRepA5 3) (classRepA5 j) 5 ord_cr3]
  fin_cases j <;> decide

lemma twisted_p3 (j : Fin 5) :
    (univ.filter (fun x : A5 => x⁻¹ * classRepA5 j * x ∈ Subgroup.zpowers (classRepA5 1))).card
      = ![60, 6, 0, 0, 0] j := by
  rw [twisted_filter_eq (classRepA5 1) (classRepA5 j) 3 ord_cr1]
  fin_cases j <;> decide

lemma twisted_p2 (j : Fin 5) :
    (univ.filter (fun x : A5 => x⁻¹ * classRepA5 j * x ∈ Subgroup.zpowers (classRepA5 2))).card
      = ![60, 0, 4, 0, 0] j := by
  rw [twisted_filter_eq (classRepA5 2) (classRepA5 j) 2 ord_cr2]
  fin_cases j <;> decide

/-- **Vertices (p = 5).** Fixed-point character of a transitive `A₅`-action on `Fin 12` with
order-`5` point stabilizers: `χ_perm = (12, 0, 0, 2, 2)` on classes `(1a, 3a, 2a, 5a, 5b)`. -/
theorem fixCount_vertices (act : A5 →* Equiv.Perm (Fin 12))
    (htrans : ∀ i j : Fin 12, ∃ g : A5, act g i = j)
    (hstab : ∀ i : Fin 12, Nat.card {g : A5 // act g i = i} = 5) (j : Fin 5) :
    (univ.filter (fun i => act (classRepA5 j) i = i)).card = ![12, 0, 0, 2, 2] j := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hstabc : Nat.card (stabSub act 0) = 5 := by
    change Nat.card {a : A5 // act a 0 = 0} = 5; exact hstab 0
  obtain ⟨c, hc⟩ := exists_conj_stab_sylow act (classRepA5 3) ord_cr3 fact5 hstabc
  have h := fix_mul_stab_eq_twisted act (classRepA5 3) (classRepA5 j) htrans c hc
  rw [stab_filter_card act 0 5 (hstab 0), twisted_p5] at h
  have hvec : ![60, 0, 0, 10, 10] j = 5 * ![12, 0, 0, 2, 2] j := by fin_cases j <;> rfl
  rw [hvec] at h; omega

/-- **Faces (p = 3).** Fixed-point character of a transitive `A₅`-action on `Fin 20` with
order-`3` point stabilizers: `χ_perm = (20, 2, 0, 0, 0)` on classes `(1a, 3a, 2a, 5a, 5b)`. -/
theorem fixCount_faces (act : A5 →* Equiv.Perm (Fin 20))
    (htrans : ∀ i j : Fin 20, ∃ g : A5, act g i = j)
    (hstab : ∀ i : Fin 20, Nat.card {g : A5 // act g i = i} = 3) (j : Fin 5) :
    (univ.filter (fun i => act (classRepA5 j) i = i)).card = ![20, 2, 0, 0, 0] j := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hstabc : Nat.card (stabSub act 0) = 3 := by
    change Nat.card {a : A5 // act a 0 = 0} = 3; exact hstab 0
  obtain ⟨c, hc⟩ := exists_conj_stab_sylow act (classRepA5 1) ord_cr1 fact3 hstabc
  have h := fix_mul_stab_eq_twisted act (classRepA5 1) (classRepA5 j) htrans c hc
  rw [stab_filter_card act 0 3 (hstab 0), twisted_p3] at h
  have hvec : ![60, 6, 0, 0, 0] j = 3 * ![20, 2, 0, 0, 0] j := by fin_cases j <;> rfl
  rw [hvec] at h; omega

/-- **Edges (p = 2).** Fixed-point character of a transitive `A₅`-action on `Fin 30` with
order-`2` point stabilizers: `χ_perm = (30, 0, 2, 0, 0)` on classes `(1a, 3a, 2a, 5a, 5b)`. -/
theorem fixCount_edges (act : A5 →* Equiv.Perm (Fin 30))
    (htrans : ∀ i j : Fin 30, ∃ g : A5, act g i = j)
    (hstab : ∀ i : Fin 30, Nat.card {g : A5 // act g i = i} = 2) (j : Fin 5) :
    (univ.filter (fun i => act (classRepA5 j) i = i)).card = ![30, 0, 2, 0, 0] j := by
  have hstabc : Nat.card (stabSub act 0) = 2 := by
    change Nat.card {a : A5 // act a 0 = 0} = 2; exact hstab 0
  obtain ⟨c, hc⟩ := exists_conj_stab_invol act hstabc
  have h := fix_mul_stab_eq_twisted act (classRepA5 2) (classRepA5 j) htrans c hc
  rw [stab_filter_card act 0 2 (hstab 0), twisted_p2] at h
  have hvec : ![60, 0, 4, 0, 0] j = 2 * ![30, 0, 2, 0, 0] j := by fin_cases j <;> rfl
  rw [hvec] at h; omega

end A5FixCounts

/-! ## From the sorted decomposition to the explicit per-part decompositions

The result `exists_sorted_isotypic_decomposition` produces a monotone-by-type internal direct
sum whose type-multiplicities are the character inner products `⟨χ_perm, χ_i⟩`, written as a raw
sum over `A₅`. The two lemmas below reduce that group sum to the five-term conjugacy-class sum
(so the multiplicities become a concrete `norm_num` computation from the fixed-point counts) and
record that the fixed-point count is a class function. -/

open Finset

open Etingof.Example4_8_1 (chiA5 Q5toC)
open Etingof.Example4_8_1.Q5 (mk_re mk_im ofNat_re ofNat_im neg_re neg_im one_re one_im
  zero_re zero_im)

open Etingof.Example4_8_1.A5 (irrepA5 classRepA5 classIdxA5 classIdxA5_card classIdxA5_spec
  classRepA5_inv_conj irrepA5_character_book rowA5 sqrt5_sq)

/-- **The fixed-point count is a class function.** For any `g`, the number of fixed points of
`act g` equals the number of fixed points of `act` at the class representative
`classRepA5 (classIdxA5 g)`. (Conjugate permutations share their fixed-point counts; here via
trace-conjugation invariance of `permRep`.) -/
lemma fixCard_eq_classRep {n : ℕ} (act : A5 →* Equiv.Perm (Fin n)) (g : A5) :
    ((univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
      = ((univ.filter (fun p : Fin n =>
          act (classRepA5 (classIdxA5 g)) p = p)).card : ℂ) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  have key : permRep act g
      = permRep act c * permRep act (classRepA5 (classIdxA5 g)) * permRep act c⁻¹ := by
    conv_lhs => rw [← hc]
    rw [map_mul, map_mul]
  rw [← permRep_trace_eq_fixCard, ← permRep_trace_eq_fixCard, key,
    LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- **Multiplicity as a conjugacy-class sum.** The character inner product `⟨χ_perm, χ_i⟩`
appearing in `exists_sorted_isotypic_decomposition`, a raw sum over `A₅` of the fixed-point
count times `χ_i(g⁻¹)`, collapses to a five-term sum over the conjugacy classes, weighted by the
class sizes `(1, 20, 15, 12, 12)`, with each factor evaluated at the class representative. Both
the fixed-point count (`fixCard_eq_classRep`) and the character (`FDRep.char_conj` plus
`classRepA5_inv_conj`) are class functions of `g`; `Finset.sum_fiberwise'` collects the fibers
and `classIdxA5_card` supplies the sizes. -/
lemma perm_mult_classSum {n : ℕ} (act : A5 →* Equiv.Perm (Fin n)) (i : Fin 5) :
    ∑ g : A5, ((univ.filter (fun p : Fin n => act g p = p)).card : ℂ)
        * (irrepA5 i).character g⁻¹
      = ∑ j : Fin 5, ((![1, 20, 15, 12, 12] j : ℕ) : ℂ)
          * ((univ.filter (fun p : Fin n => act (classRepA5 j) p = p)).card : ℂ)
          * Q5toC (chiA5 i j) := by
  classical
  have hclass : ∀ a b : A5, (∃ c, c * a * c⁻¹ = b) →
      (irrepA5 i).character b = (irrepA5 i).character a := by
    rintro a b ⟨c, rfl⟩; rw [FDRep.char_conj]
  have hterm : ∀ g : A5,
      ((univ.filter (fun p : Fin n => act g p = p)).card : ℂ) * (irrepA5 i).character g⁻¹
        = ((univ.filter (fun p : Fin n => act (classRepA5 (classIdxA5 g)) p = p)).card : ℂ)
          * Q5toC (chiA5 i (classIdxA5 g)) := by
    intro g
    obtain ⟨c, hc⟩ := classIdxA5_spec g
    obtain ⟨d, hd⟩ := classRepA5_inv_conj (classIdxA5 g)
    have hginv : (irrepA5 i).character g⁻¹
        = (irrepA5 i).character (classRepA5 (classIdxA5 g)) := by
      have step1 : (irrepA5 i).character g⁻¹
          = (irrepA5 i).character (classRepA5 (classIdxA5 g))⁻¹ := by
        refine hclass _ _ ⟨c, ?_⟩
        conv_rhs => rw [← hc]
        group
      rw [step1]; exact hclass _ _ ⟨d, hd⟩
    rw [hginv, fixCard_eq_classRep act g, irrepA5_character_book]
    simp only [rowA5, id_eq]
  rw [Finset.sum_congr rfl (fun g _ => hterm g),
    show (∑ g : A5,
        ((univ.filter (fun p : Fin n => act (classRepA5 (classIdxA5 g)) p = p)).card : ℂ)
          * Q5toC (chiA5 i (classIdxA5 g)))
      = ∑ j : Fin 5, ∑ _g ∈ univ.filter (fun g => classIdxA5 g = j),
          ((univ.filter (fun p : Fin n => act (classRepA5 j) p = p)).card : ℂ)
            * Q5toC (chiA5 i j)
      from (Finset.sum_fiberwise' univ classIdxA5
        (fun j => ((univ.filter (fun p : Fin n => act (classRepA5 j) p = p)).card : ℂ)
          * Q5toC (chiA5 i j))).symm]
  simp only [Finset.sum_const, classIdxA5_card, nsmul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => (mul_assoc _ _ _).symm)

/-! ## Multiplicity computation and reindexing to sorted dimension order

The generic pieces below are used by the three per-part decomposition theorems. They turn the
multiplicity clause (an inner product `⟨χ_perm, χ_i⟩` written as a `60`-term group sum) into a
class-size-weighted sum over the five class representatives, and pin down the monotone type vector
`type : Fin m → Fin 5` of the sorted decomposition from its fibre cardinalities. -/

section Multiplicity

open Finset Etingof.Example4_8_1 Etingof.Example4_8_1.A5 CategoryTheory

set_option linter.unusedSectionVars false

/-- **Class-function collapse.** A conjugation-invariant `F : A₅ → ℂ` sums over `A₅` to the
class-size-weighted sum over the five class representatives (sizes `1, 20, 15, 12, 12`). -/
lemma sum_classfn (F : A5 → ℂ) (hF : ∀ g c : A5, F (c * g * c⁻¹) = F g) :
    ∑ g : A5, F g
      = ∑ j : Fin 5, ((![1, 20, 15, 12, 12] j : ℕ) : ℂ) * F (classRepA5 j) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun g => classIdxA5 g) F]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∀ g ∈ Finset.univ.filter (fun g => classIdxA5 g = j),
      F g = F (classRepA5 j) := by
    intro g hg
    have hj : classIdxA5 g = j := (Finset.mem_filter.mp hg).2
    obtain ⟨c, hc⟩ := classIdxA5_spec g
    rw [← hc, hF, hj]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, classIdxA5_card j, nsmul_eq_mul]

/-- **Conjugation invariance of the fixed-point count.** The number of fixed points of
`act (c * g * c⁻¹)` equals that of `act g` (the fixed-point set is carried across by `act c⁻¹`). -/
lemma fixCount_conj {n : ℕ} (act : A5 →* Equiv.Perm (Fin n)) (g c : A5) :
    (univ.filter (fun i : Fin n => act (c * g * c⁻¹) i = i)).card
      = (univ.filter (fun i : Fin n => act g i = i)).card := by
  apply Finset.card_nbij' (fun i => act c⁻¹ i) (fun i => act c i)
  · intro i hi
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    have h := act_conj_fix_iff act g c⁻¹ i
    rw [inv_inv] at h
    exact h.mp hi
  · intro i hi
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    have h := act_conj_fix_iff act g c⁻¹ (act c i)
    rw [inv_inv] at h
    rw [h, show act c⁻¹ (act c i) = i from by simp [map_inv]]
    exact hi
  · intro i _; simp [map_inv]
  · intro i _; simp [map_inv]

/-- **Initial-segment characterisation of a down-closed predicate under a monotone tuple.** If `P`
is down-closed on `Fin 5` and `t : Fin m → Fin 5` is monotone, then `P (t k)` holds iff `k` lies
strictly below the number of indices satisfying `P ∘ t`. This pins each value `t k` from the
fibre cardinalities. -/
lemma monotone_initial {m : ℕ} {P : Fin 5 → Prop} [DecidablePred P]
    (hP : ∀ ⦃a b : Fin 5⦄, a ≤ b → P b → P a)
    {t : Fin m → Fin 5} (hmono : Monotone t) (k : Fin m) :
    P (t k) ↔ (k : ℕ) < (univ.filter (fun j => P (t j))).card := by
  constructor
  · intro hpk
    have hsub : Finset.Iic k ⊆ univ.filter (fun j => P (t j)) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      exact Finset.mem_filter.mpr ⟨mem_univ _, hP (hmono hj) hpk⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hlt
    by_contra hnp
    have hsub : univ.filter (fun j => P (t j)) ⊆ Finset.Iio k := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Iio]
      by_contra hjk
      rw [not_lt] at hjk
      exact hnp (hP (hmono hjk) hj.2)
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

end Multiplicity

/-- **Part (a): vertices.** For the icosahedral vertex action of `A₅` (any transitive action
on `12` points with point stabilizers of order `5`), the representation on `F(I) = Fin 12 → ℂ`
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
  classical
  obtain ⟨m, S, hS, type, hInt, hIrr, hmono, hchar, hfr, hmult⟩ :=
    exists_sorted_isotypic_decomposition act
  -- The multiplicity vector `⟨χ_perm, χ_i⟩` is `(1, 1, 1, 0, 1)`.
  have hmultnat : ∀ i : Fin 5,
      (univ.filter (fun k => type k = i)).card = ![1, 1, 1, 0, 1] i := by
    intro i
    have h := hmult i
    rw [perm_mult_classSum act i] at h
    simp only [fixCount_vertices act htrans hstab] at h
    have hcard : (Fintype.card A5 : ℂ) = 60 := by
      have : (Fintype.card A5 : ℕ) = 60 := by rw [← Nat.card_eq_fintype_card]; exact card_A5
      rw [this]; norm_num
    have hsum : (∑ j : Fin 5, ((![1, 20, 15, 12, 12] j : ℕ) : ℂ)
          * ((![12, 0, 0, 2, 2] j : ℕ) : ℂ) * Q5toC (chiA5 i j))
        = (Fintype.card A5 : ℂ) * ((![1, 1, 1, 0, 1] i : ℕ) : ℂ) := by
      rw [hcard]
      fin_cases i <;>
        norm_num [Fin.sum_univ_five, chiA5, Q5toC, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
          Matrix.tail_cons, mk_re, mk_im, ofNat_re, ofNat_im, neg_re, neg_im,
          one_re, one_im, zero_re, zero_im] <;>
        ring
    rw [hsum, smul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul] at h
    exact_mod_cast h
  -- Exactly four summands (`1 + 1 + 1 + 0 + 1`).
  have hpart : (univ : Finset (Fin m)).card
      = ∑ i : Fin 5, (univ.filter (fun k => type k = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (type k))
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  have hm4 : m = 4 := by rw [hpart]; simp only [hmultnat]; decide
  subst hm4
  -- Every type appears at most once, so `type` is strictly monotone.
  have hle1 : ∀ v : Fin 5, (univ.filter (fun k => type k = v)).card ≤ 1 := by
    intro v; rw [hmultnat v]; fin_cases v <;> decide
  have hinj : Function.Injective type := by
    intro a b hab
    by_contra hne
    have hsub : ({a, b} : Finset (Fin 4)) ⊆ univ.filter (fun k => type k = type a) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp
      · simp [hab]
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at h2
    exact absurd (h2.trans (hle1 (type a))) (by norm_num)
  have hstrict : StrictMono type := hmono.strictMono_of_injective hinj
  -- No summand has type `3` (its multiplicity is `0`).
  have hne3 : ∀ k : Fin 4, type k ≠ 3 := by
    intro k hk
    have hmem : k ∈ univ.filter (fun k => type k = 3) := by simp [hk]
    have hpos := Finset.card_pos.mpr ⟨k, hmem⟩
    rw [hmultnat 3] at hpos
    simp at hpos
  -- A strictly increasing `Fin 4 → Fin 5` avoiding `3` is `![0, 1, 2, 4]`.
  have s01 : (type 0).val < (type 1).val := Fin.lt_def.mp (hstrict (by decide))
  have s12 : (type 1).val < (type 2).val := Fin.lt_def.mp (hstrict (by decide))
  have s23 : (type 2).val < (type 3).val := Fin.lt_def.mp (hstrict (by decide))
  have b0 : (type 0).val < 5 := (type 0).isLt
  have b1 : (type 1).val < 5 := (type 1).isLt
  have b2 : (type 2).val < 5 := (type 2).isLt
  have b3 : (type 3).val < 5 := (type 3).isLt
  have n0 : (type 0).val ≠ 3 := fun hh => hne3 0 (Fin.ext hh)
  have n1 : (type 1).val ≠ 3 := fun hh => hne3 1 (Fin.ext hh)
  have n2 : (type 2).val ≠ 3 := fun hh => hne3 2 (Fin.ext hh)
  have n3 : (type 3).val ≠ 3 := fun hh => hne3 3 (Fin.ext hh)
  have ht0 : type 0 = 0 := Fin.ext (by omega)
  have ht1 : type 1 = 1 := Fin.ext (by omega)
  have ht2 : type 2 = 2 := Fin.ext (by omega)
  have ht3 : type 3 = 4 := Fin.ext (by omega)
  refine ⟨S, hS, hInt, hIrr, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hfr, ht0]
  · simp [hfr, ht1]
  · simp [hfr, ht2]
  · simp [hfr, ht3]
  · refine ⟨classRepA5 3, ?_⟩
    rw [hchar, hchar, ht1, ht2, irrepA5_character_book, irrepA5_character_book]
    simp only [rowA5, id_eq, Q5toC, chiA5, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      mk_re, mk_im]
    intro hcontra
    have hz : (Real.sqrt 5 : ℂ) = 0 := by linear_combination hcontra
    have hsq := sqrt5_sq
    rw [hz] at hsq
    norm_num at hsq

open Finset Etingof.Example4_8_1 Etingof.Example4_8_1.A5 CategoryTheory in
/-- **Part (b): faces.** For the icosahedral face action of `A₅` (any transitive action on
`20` points with point stabilizers of order `3`), the representation on `Fin 20 → ℂ`
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
  classical
  obtain ⟨m, S, hS, type, hInt, hIrr, hmono, hchar, hfr, hmult⟩ :=
    exists_sorted_isotypic_decomposition act
  -- Fixed-point count at each class representative (cast to `ℂ`).
  have hfix : ∀ j : Fin 5,
      ((univ.filter (fun p : Fin 20 => act (classRepA5 j) p = p)).card : ℂ)
        = ((![20, 2, 0, 0, 0] j : ℕ) : ℂ) := by
    intro j; rw [fixCount_faces act htrans hstab j]
  -- Character of `irrepA5 i` at the inverse class representative = tabulated value.
  have hchar_inv : ∀ (i j : Fin 5),
      (irrepA5 i).character (classRepA5 j)⁻¹ = Q5toC (chiA5 i j) := by
    intro i j
    obtain ⟨d, hd⟩ := classRepA5_inv_conj j
    rw [show (classRepA5 j)⁻¹ = d * classRepA5 j * d⁻¹ from hd.symm, FDRep.char_conj,
      irrepA5_character_book]
    simp only [rowA5, id_eq]
  -- `|A₅| = 60` in `ℂ`.
  have hcard60 : (Fintype.card A5 : ℂ) = 60 := by
    rw [show Fintype.card A5 = 60 from by rw [← Nat.card_eq_fintype_card]; exact card_A5]; norm_num
  -- Multiplicities: `⟨χ_perm, χ_i⟩ = (1, 1, 1, 2, 1)`.
  have hmulti : ∀ i : Fin 5, (univ.filter (fun k => type k = i)).card = ![1, 1, 1, 2, 1] i := by
    intro i
    have hFconj : ∀ g c : A5,
        ((univ.filter (fun p : Fin 20 => act (c * g * c⁻¹) p = p)).card : ℂ)
              * (irrepA5 i).character (c * g * c⁻¹)⁻¹
          = ((univ.filter (fun p : Fin 20 => act g p = p)).card : ℂ)
              * (irrepA5 i).character g⁻¹ := by
      intro g c
      rw [fixCount_conj act g c,
        show (c * g * c⁻¹)⁻¹ = c * g⁻¹ * c⁻¹ from by group, FDRep.char_conj]
    have hsum : (∑ g : A5, ((univ.filter (fun p : Fin 20 => act g p = p)).card : ℂ)
          * (irrepA5 i).character g⁻¹)
        = (60 : ℂ) * ((![1, 1, 1, 2, 1] i : ℕ) : ℂ) := by
      rw [sum_classfn (fun g => ((univ.filter (fun p : Fin 20 => act g p = p)).card : ℂ)
          * (irrepA5 i).character g⁻¹) hFconj]
      simp only [hfix, hchar_inv]
      fin_cases i <;>
        · rw [Fin.sum_univ_five]
          norm_num [chiA5, Q5toC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
            Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im, Q5.one_re,
            Q5.one_im, Q5.zero_re, Q5.zero_im]
    have hC : ((univ.filter (fun k => type k = i)).card : ℂ) = ((![1, 1, 1, 2, 1] i : ℕ) : ℂ) := by
      rw [hmult i, smul_eq_mul, hsum, ← hcard60, ← mul_assoc, invOf_mul_self, one_mul]
    exact_mod_cast hC
  -- The number of summands is `m = 1 + 1 + 1 + 2 + 1 = 6`.
  have hm : m = 6 := by
    have hpart : (univ : Finset (Fin m)).card
        = ∑ i : Fin 5, (univ.filter (fun k => type k = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun k _ => mem_univ (type k))
    rw [Finset.card_univ, Fintype.card_fin] at hpart
    rw [hpart]; simp only [hmulti]; decide
  subst hm
  -- Down-set cardinalities of `type`.
  have hp : ∀ i : Fin 5, (univ.filter (fun j => type j ≤ i)).card = ![1, 2, 3, 5, 6] i := by
    intro i
    rw [Finset.card_eq_sum_card_fiberwise
      (s := univ.filter (fun j : Fin 6 => type j ≤ i)) (t := (univ : Finset (Fin 5)))
      (f := type) (fun j _ => mem_univ (type j))]
    have hterm : ∀ b : Fin 5,
        ((univ.filter (fun j : Fin 6 => type j ≤ i)).filter (fun j => type j = b)).card
          = if b ≤ i then (![1, 1, 1, 2, 1] b) else 0 := by
      intro b
      by_cases hb : b ≤ i
      · rw [if_pos hb, Finset.filter_filter, ← hmulti b]
        congr 1; ext j
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
      · rw [if_neg hb, Finset.filter_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hj; exact hb (hj.2 ▸ hj.1)
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    fin_cases i <;> decide
  have hq : ∀ i : Fin 5, (univ.filter (fun j => type j < i)).card = ![0, 1, 2, 3, 5] i := by
    intro i
    rw [Finset.card_eq_sum_card_fiberwise
      (s := univ.filter (fun j : Fin 6 => type j < i)) (t := (univ : Finset (Fin 5)))
      (f := type) (fun j _ => mem_univ (type j))]
    have hterm : ∀ b : Fin 5,
        ((univ.filter (fun j : Fin 6 => type j < i)).filter (fun j => type j = b)).card
          = if b < i then (![1, 1, 1, 2, 1] b) else 0 := by
      intro b
      by_cases hb : b < i
      · rw [if_pos hb, Finset.filter_filter, ← hmulti b]
        congr 1; ext j
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
      · rw [if_neg hb, Finset.filter_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hj; exact hb (hj.2 ▸ hj.1)
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    fin_cases i <;> decide
  -- Monotonicity + fibre cardinalities pin the type vector to `![0,1,2,3,3,4]`.
  have htype : ∀ k : Fin 6, type k = ![0, 1, 2, 3, 3, 4] k := by
    intro k
    have hle : ∀ v : Fin 5, (k : ℕ) < ![1, 2, 3, 5, 6] v → type k ≤ v := by
      intro v hv
      have h := monotone_initial (P := fun x => x ≤ v) (fun a b hab hb => le_trans hab hb) hmono k
      rw [hp v] at h; exact h.mpr hv
    have hgt : ∀ v : Fin 5, ![0, 1, 2, 3, 5] v ≤ (k : ℕ) → v ≤ type k := by
      intro v hv
      by_contra hlt
      rw [not_le] at hlt
      have h := monotone_initial (P := fun x => x < v)
        (fun a b hab hb => lt_of_le_of_lt hab hb) hmono k
      rw [hq v] at h
      have := h.mp hlt; omega
    fin_cases k <;> exact le_antisymm (hle _ (by decide)) (hgt _ (by decide))
  -- Type values at the two `3`-dimensional summands, for the distinguishing witness.
  have h1 : type 1 = 1 := by rw [htype 1]; rfl
  have h2 : type 2 = 2 := by rw [htype 2]; rfl
  refine ⟨S, hS, hInt, hIrr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr 0, htype 0]; rfl
  · rw [hfr 1, htype 1]; rfl
  · rw [hfr 2, htype 2]; rfl
  · rw [hfr 3, htype 3]; rfl
  · rw [hfr 4, htype 4]; rfl
  · rw [hfr 5, htype 5]; rfl
  · refine ⟨classRepA5 3, ?_⟩
    rw [hchar 1 (classRepA5 3), hchar 2 (classRepA5 3), h1, h2,
      irrepA5_character_book, irrepA5_character_book]
    simp only [rowA5, id_eq]
    -- The two `3`-dimensional characters differ at the 5-cycle class by `√5 ≠ 0`.
    simp only [Q5toC, chiA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Q5.mk_re, Q5.mk_im]
    intro h
    have hz : (Real.sqrt 5 : ℂ) = 0 := by linear_combination h
    have hsq := sqrt5_sq
    rw [hz] at hsq; norm_num at hsq

open Finset Etingof.Example4_8_1 Etingof.Example4_8_1.A5 CategoryTheory in
/-- **Part (b): edges.** For the icosahedral edge action of `A₅` (any transitive action on
`30` points with point stabilizers of order `2`), the representation on `Fin 30 → ℂ`
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
  classical
  obtain ⟨m, S, hS, type, hInt, hIrr, hmono, hchar, hfr, hmult⟩ :=
    exists_sorted_isotypic_decomposition act
  -- Fixed-point count at each class representative (cast to `ℂ`).
  have hfix : ∀ j : Fin 5,
      ((univ.filter (fun p : Fin 30 => act (classRepA5 j) p = p)).card : ℂ)
        = ((![30, 0, 2, 0, 0] j : ℕ) : ℂ) := by
    intro j; rw [fixCount_edges act htrans hstab j]
  -- Character of `irrepA5 i` at the inverse class representative = tabulated value.
  have hchar_inv : ∀ (i j : Fin 5),
      (irrepA5 i).character (classRepA5 j)⁻¹ = Q5toC (chiA5 i j) := by
    intro i j
    obtain ⟨d, hd⟩ := classRepA5_inv_conj j
    rw [show (classRepA5 j)⁻¹ = d * classRepA5 j * d⁻¹ from hd.symm, FDRep.char_conj,
      irrepA5_character_book]
    simp only [rowA5, id_eq]
  -- `|A₅| = 60` in `ℂ`.
  have hcard60 : (Fintype.card A5 : ℂ) = 60 := by
    rw [show Fintype.card A5 = 60 from by rw [← Nat.card_eq_fintype_card]; exact card_A5]; norm_num
  -- Multiplicities: `⟨χ_perm, χ_i⟩ = (1, 1, 1, 2, 3)`.
  have hmulti : ∀ i : Fin 5, (univ.filter (fun k => type k = i)).card = ![1, 1, 1, 2, 3] i := by
    intro i
    have hFconj : ∀ g c : A5,
        ((univ.filter (fun p : Fin 30 => act (c * g * c⁻¹) p = p)).card : ℂ)
              * (irrepA5 i).character (c * g * c⁻¹)⁻¹
          = ((univ.filter (fun p : Fin 30 => act g p = p)).card : ℂ)
              * (irrepA5 i).character g⁻¹ := by
      intro g c
      rw [fixCount_conj act g c,
        show (c * g * c⁻¹)⁻¹ = c * g⁻¹ * c⁻¹ from by group, FDRep.char_conj]
    have hsum : (∑ g : A5, ((univ.filter (fun p : Fin 30 => act g p = p)).card : ℂ)
          * (irrepA5 i).character g⁻¹)
        = (60 : ℂ) * ((![1, 1, 1, 2, 3] i : ℕ) : ℂ) := by
      rw [sum_classfn (fun g => ((univ.filter (fun p : Fin 30 => act g p = p)).card : ℂ)
          * (irrepA5 i).character g⁻¹) hFconj]
      simp only [hfix, hchar_inv]
      fin_cases i <;>
        · rw [Fin.sum_univ_five]
          norm_num [chiA5, Q5toC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
            Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im, Q5.one_re,
            Q5.one_im, Q5.zero_re, Q5.zero_im]
    have hC : ((univ.filter (fun k => type k = i)).card : ℂ) = ((![1, 1, 1, 2, 3] i : ℕ) : ℂ) := by
      rw [hmult i, smul_eq_mul, hsum, ← hcard60, ← mul_assoc, invOf_mul_self, one_mul]
    exact_mod_cast hC
  -- The number of summands is `m = 1 + 1 + 1 + 2 + 3 = 8`.
  have hm : m = 8 := by
    have hpart : (univ : Finset (Fin m)).card
        = ∑ i : Fin 5, (univ.filter (fun k => type k = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun k _ => mem_univ (type k))
    rw [Finset.card_univ, Fintype.card_fin] at hpart
    rw [hpart]; simp only [hmulti]; decide
  subst hm
  -- Down-set cardinalities of `type`.
  have hp : ∀ i : Fin 5, (univ.filter (fun j => type j ≤ i)).card = ![1, 2, 3, 5, 8] i := by
    intro i
    rw [Finset.card_eq_sum_card_fiberwise
      (s := univ.filter (fun j : Fin 8 => type j ≤ i)) (t := (univ : Finset (Fin 5)))
      (f := type) (fun j _ => mem_univ (type j))]
    have hterm : ∀ b : Fin 5,
        ((univ.filter (fun j : Fin 8 => type j ≤ i)).filter (fun j => type j = b)).card
          = if b ≤ i then (![1, 1, 1, 2, 3] b) else 0 := by
      intro b
      by_cases hb : b ≤ i
      · rw [if_pos hb, Finset.filter_filter, ← hmulti b]
        congr 1; ext j
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
      · rw [if_neg hb, Finset.filter_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hj; exact hb (hj.2 ▸ hj.1)
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    fin_cases i <;> decide
  have hq : ∀ i : Fin 5, (univ.filter (fun j => type j < i)).card = ![0, 1, 2, 3, 5] i := by
    intro i
    rw [Finset.card_eq_sum_card_fiberwise
      (s := univ.filter (fun j : Fin 8 => type j < i)) (t := (univ : Finset (Fin 5)))
      (f := type) (fun j _ => mem_univ (type j))]
    have hterm : ∀ b : Fin 5,
        ((univ.filter (fun j : Fin 8 => type j < i)).filter (fun j => type j = b)).card
          = if b < i then (![1, 1, 1, 2, 3] b) else 0 := by
      intro b
      by_cases hb : b < i
      · rw [if_pos hb, Finset.filter_filter, ← hmulti b]
        congr 1; ext j
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
      · rw [if_neg hb, Finset.filter_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hj; exact hb (hj.2 ▸ hj.1)
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    fin_cases i <;> decide
  -- Monotonicity + fibre cardinalities pin the type vector to `![0,1,2,3,3,4,4,4]`.
  have htype : ∀ k : Fin 8, type k = ![0, 1, 2, 3, 3, 4, 4, 4] k := by
    intro k
    have hle : ∀ v : Fin 5, (k : ℕ) < ![1, 2, 3, 5, 8] v → type k ≤ v := by
      intro v hv
      have h := monotone_initial (P := fun x => x ≤ v) (fun a b hab hb => le_trans hab hb) hmono k
      rw [hp v] at h; exact h.mpr hv
    have hgt : ∀ v : Fin 5, ![0, 1, 2, 3, 5] v ≤ (k : ℕ) → v ≤ type k := by
      intro v hv
      by_contra hlt
      rw [not_le] at hlt
      have h := monotone_initial (P := fun x => x < v)
        (fun a b hab hb => lt_of_le_of_lt hab hb) hmono k
      rw [hq v] at h
      have := h.mp hlt; omega
    fin_cases k <;> exact le_antisymm (hle _ (by decide)) (hgt _ (by decide))
  -- Type values at the two `3`-dimensional summands, for the distinguishing witness.
  have h1 : type 1 = 1 := by rw [htype 1]; rfl
  have h2 : type 2 = 2 := by rw [htype 2]; rfl
  refine ⟨S, hS, hInt, hIrr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr 0, htype 0]; rfl
  · rw [hfr 1, htype 1]; rfl
  · rw [hfr 2, htype 2]; rfl
  · rw [hfr 3, htype 3]; rfl
  · rw [hfr 4, htype 4]; rfl
  · rw [hfr 5, htype 5]; rfl
  · rw [hfr 6, htype 6]; rfl
  · rw [hfr 7, htype 7]; rfl
  · refine ⟨classRepA5 3, ?_⟩
    rw [hchar 1 (classRepA5 3), hchar 2 (classRepA5 3), h1, h2,
      irrepA5_character_book, irrepA5_character_book]
    simp only [rowA5, id_eq]
    -- The two `3`-dimensional characters differ at the 5-cycle class by `√5 ≠ 0`.
    simp only [Q5toC, chiA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Q5.mk_re, Q5.mk_im]
    intro h
    have hz : (Real.sqrt 5 : ℂ) = 0 := by linear_combination h
    have hsq := sqrt5_sq
    rw [hz] at hsq; norm_num at hsq

end Etingof.Problem4_12_5

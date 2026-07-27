import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.Length

/-!
# Proposition 3.1.4: Classification of Subrepresentations in Semisimple Representations

Let `Vᵢ`, `1 ≤ i ≤ m`, be irreducible finite dimensional pairwise nonisomorphic
representations of `A`, and let `W` be a subrepresentation of `V = ⊕ᵢ nᵢVᵢ`. Then `W`
is isomorphic to `⊕ᵢ rᵢVᵢ` with `rᵢ ≤ nᵢ`.

We formalize representations of the algebra `A` as `A`-modules. The hypotheses are:
the `V i` are simple (irreducible), finite-dimensional, and pairwise nonisomorphic. The
ambient representation `V = ⊕ᵢ nᵢ Vᵢ` is modeled by `⨁ i, (Fin (n i) → V i)` (each
`Fin (n i) → V i` is `nᵢ` copies of `Vᵢ`).

The substantive content of the proposition, and the part missing from a bare
"submodules of a semisimple module are semisimple" statement, is the multiplicity
bound `r i ≤ n i` together with the explicit isomorphism type `W ≅ ⊕ᵢ rᵢ Vᵢ`. Both are
asserted here.

The book additionally describes the inclusion `φ : W → V` as a direct sum of maps
`φᵢ : rᵢVᵢ → nᵢVᵢ` given by right multiplication by an `rᵢ × nᵢ` matrix `Xᵢ` with linearly
independent rows. That description is `subrepresentation_of_semisimple_matrix_pi` (and its
`⨁` form `subrepresentation_of_semisimple_matrix`) below. The book works over an
algebraically closed field, where Schur's lemma makes the entries of `Xᵢ` scalars; over the
arbitrary ring `A` used here the entries are elements of the division ring
`Module.End A (V i)`, acting on `V i` on the left. "Linearly independent rows" is then
independence over `(Module.End A (V i))ᵐᵒᵖ`, i.e. with respect to the right multiplication
`Xᵢ ↦ Xᵢ · c` that the book's row-vector convention `(v₁, …, v_{rᵢ}) Xᵢ` produces; the
matrix is only recovered up to that convention, and there is no left/right symmetry to
appeal to over a noncommutative `Module.End A (V i)`.
Block-diagonality of `φ` — the "direct sum of inclusions" clause — is the statement that
the `i`-th coordinate of `φ w` only involves the `i`-th block of `w`, which is exactly the
shape of the displayed formula.

The proof uses the isotypic decomposition of the semisimple module `W`: `W` is the direct
sum of its `V i`-isotypic components `C i`, each `C i ≅ Fin (r i) → V i`, and `r i ≤ n i`
because `C i` embeds (length-monotonically) into the `V i`-isotypic component of `V`, which
is the `i`-th summand `Fin (n i) → V i` of length `n i`. Pairwise nonisomorphism is what
confines the `V i`-isotypic part of `V` to the `i`-th summand.

## Relation to Problem 2.3.15

The book's proof extracts an irreducible subrepresentation `P ⊆ W` "by Problem 2.3.15".
This formalization does not use that problem: the ambient `⊕ᵢ nᵢ Vᵢ` is a
finite direct sum of simples, hence semisimple, so existence of a simple submodule of any
submodule comes directly from `IsSemisimpleModule.eq_bot_or_exists_simple_le` (used inside
`iSupIndep` and `htop` below). This is stronger, since it needs no
finite-dimensionality, so Proposition 3.1.4 does not silently assume Problem 2.3.15. The
book problem itself is formalized in `Chapter2/Problem2_3_15.lean`
(`Etingof.exists_isSimpleModule_of_finite`).
-/

open Module

open scoped DirectSum

namespace Etingof

/-- A finite direct sum of copies of a simple module `S` is isotypic of type `S`:
every simple submodule of `Fin m → S` is isomorphic to `S`. -/
theorem isIsotypicOfType_fun {A : Type*} [Ring A] {S : Type*} [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (m : ℕ) : IsIsotypicOfType A (Fin m → S) S := by
  intro p _
  -- Some coordinate projection is nonzero on `p`, otherwise `p` is trivial.
  have hex : ∃ j, ((LinearMap.proj j) ∘ₗ p.subtype : ↥p →ₗ[A] S) ≠ 0 := by
    by_contra h
    push Not at h
    haveI : Nontrivial ↥p := IsSimpleModule.nontrivial A ↥p
    have : Subsingleton ↥p := by
      refine ⟨fun a b => ?_⟩
      have eq0 : ∀ c : ↥p, c = 0 := by
        intro c
        apply Subtype.ext
        funext j
        have := DFunLike.congr_fun (h j) c
        simpa using this
      rw [eq0 a, eq0 b]
    exact (not_subsingleton ↥p) this
  obtain ⟨j, hj⟩ := hex
  have hinj := LinearMap.injective_of_ne_zero hj
  exact ⟨LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hj)⟩

section

variable {A : Type*} [Ring A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
  [∀ i, IsSimpleModule A (V i)] [∀ i, Module.Finite A (V i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Module.Finite A (V i)] in
/-- A simple submodule of the ambient `⊕ᵢ nᵢ Vᵢ` (in `Pi` form) is isomorphic to some `Vᵢ`. -/
private theorem exists_iso_of_simple (n : ι → ℕ)
    (s : Submodule A (∀ k, Fin (n k) → V k)) [IsSimpleModule A ↥s] :
    ∃ i, Nonempty (↥s ≃ₗ[A] V i) := by
  have hex : ∃ i, ((LinearMap.proj i) ∘ₗ s.subtype : ↥s →ₗ[A] _) ≠ 0 := by
    by_contra h
    push Not at h
    haveI : Nontrivial ↥s := IsSimpleModule.nontrivial A ↥s
    have : Subsingleton ↥s := by
      refine ⟨fun a b => ?_⟩
      have eq0 : ∀ c : ↥s, c = 0 := by
        intro c
        apply Subtype.ext
        funext i
        have := DFunLike.congr_fun (h i) c
        simpa using this
      rw [eq0 a, eq0 b]
    exact (not_subsingleton ↥s) this
  obtain ⟨i, hi⟩ := hex
  have hinj := LinearMap.injective_of_ne_zero hi
  haveI : IsSimpleModule A ↥(LinearMap.range ((LinearMap.proj i) ∘ₗ s.subtype)) :=
    (LinearEquiv.isSimpleModule_iff (LinearEquiv.ofInjective _ hinj)).mp inferInstance
  refine ⟨i, ⟨(LinearEquiv.ofInjective _ hinj).trans
    (isIsotypicOfType_fun (n i) (LinearMap.range ((LinearMap.proj i) ∘ₗ s.subtype))).some⟩⟩

omit [Fintype ι] [DecidableEq ι] [∀ i, Module.Finite A (V i)] in
/-- If a submodule `m` of `⊕ⱼ nⱼ Vⱼ` is isomorphic to `Vᵢ`, then all its coordinates away
from `i` vanish: this is where pairwise nonisomorphism of the `Vⱼ` is used. -/
private theorem coord_eq_zero_of_iso (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    {i j : ι} (hij : i ≠ j) {m : Submodule A (∀ k, Fin (n k) → V k)}
    (hm : Nonempty (↥m ≃ₗ[A] V i)) {x : ∀ k, Fin (n k) → V k} (hx : x ∈ m) :
    x j = 0 := by
  obtain ⟨em⟩ := hm
  haveI : IsSimpleModule A ↥m := (LinearEquiv.isSimpleModule_iff em).mpr inferInstance
  set f : ↥m →ₗ[A] (Fin (n j) → V j) := (LinearMap.proj j) ∘ₗ m.subtype with hf
  rcases eq_or_ne f 0 with h0 | h0
  · have : f ⟨x, hx⟩ = 0 := by rw [h0]; rfl
    simpa [hf] using this
  · exfalso
    have hinj := LinearMap.injective_of_ne_zero h0
    haveI : IsSimpleModule A ↥(LinearMap.range f) :=
      (LinearEquiv.isSimpleModule_iff (LinearEquiv.ofInjective f hinj)).mp inferInstance
    have e2 := (isIsotypicOfType_fun (n j) (LinearMap.range f)).some
    exact hij (hd ⟨em.symm.trans ((LinearEquiv.ofInjective f hinj).trans e2)⟩)

omit [DecidableEq ι] [∀ i, Module.Finite A (V i)] in
/- Finiteness of the indexing type is essential to the finite-product argument, although the
result type only records the multiplicities pointwise. -/
set_option linter.unusedFintypeInType false in
/-- **Proposition 3.1.4** (`Pi` form of the ambient representation).
Let the `V i` be simple, finite-dimensional, pairwise nonisomorphic `A`-modules. Any
subrepresentation `W` of `⊕ᵢ nᵢ Vᵢ` is isomorphic to `⊕ᵢ rᵢ Vᵢ` with `r i ≤ n i`. -/
theorem subrepresentation_of_semisimple_pi (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (∀ i, Fin (n i) → V i)) :
    ∃ r : ι → ℕ, (∀ i, r i ≤ n i) ∧ Nonempty (↥W ≃ₗ[A] ∀ i, Fin (r i) → V i) := by
  classical
  -- The `V i`-isotypic component of `W`.
  set C : ι → Submodule A ↥W := fun i => isotypicComponent A (↥W) (V i) with hC
  have hCiso : ∀ i, IsIsotypicOfType A ↥(C i) (V i) := fun i => le_isotypicComponent_iff.mp le_rfl
  -- Multiplicities `r i` and isomorphisms `C i ≅ Fin (r i) → V i`.
  choose r hr using fun i => (hCiso i).linearEquiv_fun
  have e : ∀ i, ↥(C i) ≃ₗ[A] (Fin (r i) → V i) := fun i => (hr i).some
  -- A length computation: `length (Fin m → V j) = m`.
  have length_fun : ∀ (m : ℕ) (j : ι), Module.length A (Fin m → V j) = (m : ℕ∞) := by
    intro m j
    rw [Module.length_pi_of_fintype]
    simp
  -- A simple submodule of `W` lies in some isotypic component `C i`.
  have iso_of_le : ∀ {k : ι} {t : Submodule A ↥W} (_ : IsSimpleModule A ↥t),
      t ≤ C k → Nonempty (↥t ≃ₗ[A] V k) := by
    intro k t hsimp hle
    haveI := hsimp
    have hit : IsIsotypicOfType A ↥t (V k) := le_isotypicComponent_iff.mp hle
    -- `↥t` is a simple submodule of itself, hence isomorphic to `V k`.
    exact isIsotypicOfType_submodule_iff.mp hit t le_rfl
  have simple_mem : ∀ {s : Submodule A ↥W}, IsSimpleModule A ↥s → ∃ i, s ≤ C i := by
    intro s hs
    haveI := hs
    -- Push `s` into the ambient module to apply `exists_iso_of_simple`.
    have es := Submodule.equivMapOfInjective W.subtype W.subtype_injective s
    haveI : IsSimpleModule A ↥(Submodule.map W.subtype s) :=
      (LinearEquiv.isSimpleModule_iff es).mp hs
    obtain ⟨i, ⟨ei⟩⟩ := exists_iso_of_simple n (Submodule.map W.subtype s)
    refine ⟨i, ?_⟩
    rw [hC, le_isotypicComponent_iff]
    exact (IsIsotypicOfType.of_isSimpleModule A ↥s).of_linearEquiv_type (es.trans ei)
  -- `⨆ i, C i = ⊤`.
  have htop : ⨆ i, C i = ⊤ := by
    rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top A ↥W]
    apply sSup_le
    intro s hs
    obtain ⟨i, hi⟩ := simple_mem hs
    exact hi.trans (le_iSup C i)
  -- `C` is an independent family.
  have hind : iSupIndep C := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, ← le_bot_iff]
    -- Show the meet has no simple submodule.
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (C i ⊓ ⨆ j, ⨆ (_ : j ≠ i), C j) with
      hbot | ⟨t, htle, _⟩
    · rw [hbot]
    · exfalso
      have ht_i : t ≤ C i := htle.trans inf_le_left
      have ht_sup : t ≤ ⨆ j, ⨆ (_ : j ≠ i), C j := htle.trans inf_le_right
      -- `t ≅ V i`.
      obtain ⟨eti⟩ := iso_of_le ‹IsSimpleModule A ↥t› ht_i
      -- `t ≅ V j` for some `j ≠ i`, contradicting pairwise nonisomorphism.
      have hts : t ≤ sSup (C '' {j | j ≠ i}) := by
        rw [sSup_image]; exact ht_sup
      haveI : ∀ q : ↥(C '' {j | j ≠ i}), IsSemisimpleModule A ↥(q : Submodule A ↥W) :=
        fun q => inferInstance
      obtain ⟨q, hq, S, hSle, ⟨eS⟩⟩ :=
        Submodule.le_linearEquiv_of_le_sSup t (C '' {j | j ≠ i}) hts
      obtain ⟨j, hj, rfl⟩ := hq
      haveI : IsSimpleModule A ↥S := (LinearEquiv.isSimpleModule_iff eS).mp ‹_›
      obtain ⟨eSj⟩ := iso_of_le ‹IsSimpleModule A ↥S› hSle
      exact hj (hd ⟨(eti.symm.trans (eS.trans eSj)).symm⟩)
  -- The internal direct sum: `W ≅ ⨁ i, C i ≅ ∀ i, C i ≅ ∀ i, Fin (r i) → V i`.
  have eqW : ↥W ≃ₗ[A] ∀ i, Fin (r i) → V i :=
    (hind.linearEquiv htop).symm.trans
      ((DirectSum.linearEquivFunOnFintype A ι (fun i => ↥(C i))).trans
        (LinearEquiv.piCongrRight fun i => e i))
  refine ⟨r, ?_, ⟨eqW⟩⟩
  -- The multiplicity bound `r i ≤ n i`.
  intro i
  -- `length (C i) = r i`.
  have hlenC : Module.length A ↥(C i) = (r i : ℕ∞) := by
    rw [(e i).length_eq, length_fun]
  -- Image of `C i` in the ambient module.
  have eCi' := Submodule.equivMapOfInjective W.subtype W.subtype_injective (C i)
  have hCi'_le : Submodule.map W.subtype (C i) ≤
      isotypicComponent A (∀ k, Fin (n k) → V k) (V i) := by
    rw [le_isotypicComponent_iff]
    exact (LinearEquiv.isIsotypicOfType_iff eCi').mp (hCiso i)
  -- The `V i`-isotypic component of the ambient module sits inside the `i`-th summand.
  have hisoComp_le : isotypicComponent A (∀ k, Fin (n k) → V k) (V i) ≤
      LinearMap.range (LinearMap.single A (fun k => Fin (n k) → V k) i) := by
    refine sSup_le ?_
    rintro m ⟨em⟩
    intro x hx
    refine ⟨x i, ?_⟩
    funext j
    rw [LinearMap.single_apply]
    rcases eq_or_ne j i with rfl | hji
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hji]
      exact (coord_eq_zero_of_iso n hd (Ne.symm hji) ⟨em⟩ hx).symm
  -- `length (range (single i)) = n i`.
  have hlenSummand : Module.length A
      ↥(LinearMap.range (LinearMap.single A (fun k => Fin (n k) → V k) i)) = (n i : ℕ∞) := by
    have hsi : Function.Injective (LinearMap.single A (fun k => Fin (n k) → V k) i) := by
      intro a b hab
      have h2 := congrFun hab i
      simpa [LinearMap.single_apply] using h2
    rw [(LinearEquiv.ofInjective _ hsi).symm.length_eq, length_fun]
  -- Assemble the length inequality and conclude.
  have hchain : (r i : ℕ∞) ≤ (n i : ℕ∞) := by
    rw [← hlenC, ← hlenSummand]
    calc Module.length A ↥(C i)
        = Module.length A ↥(Submodule.map W.subtype (C i)) := eCi'.length_eq
      _ ≤ Module.length A ↥(isotypicComponent A (∀ k, Fin (n k) → V k) (V i)) :=
          Module.length_le_of_injective (Submodule.inclusion hCi'_le)
            (Submodule.inclusion_injective hCi'_le)
      _ ≤ Module.length A ↥(LinearMap.range (LinearMap.single A (fun k => Fin (n k) → V k) i)) :=
          Module.length_le_of_injective (Submodule.inclusion hisoComp_le)
            (Submodule.inclusion_injective hisoComp_le)
  exact_mod_cast hchain

omit [DecidableEq ι] [∀ i, Module.Finite A (V i)] in
/- Finiteness of the indexing type is essential to identify the external direct sum with a
finite product, although it does not occur in the proposition returned. -/
set_option linter.unusedFintypeInType false in
/-- **Proposition 3.1.4.**
Let `V i` be simple (irreducible), finite-dimensional, pairwise nonisomorphic `A`-modules,
and let `W` be a subrepresentation of `V = ⊕ᵢ nᵢ Vᵢ`. Then `W` is isomorphic to `⊕ᵢ rᵢ Vᵢ`
with `r i ≤ n i`. Etingof Proposition 3.1.4. -/
theorem subrepresentation_of_semisimple (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (⨁ i, (Fin (n i) → V i))) :
    ∃ r : ι → ℕ, (∀ i, r i ≤ n i) ∧ Nonempty (↥W ≃ₗ[A] ⨁ i, (Fin (r i) → V i)) := by
  classical
  -- Transport across `⨁ i, P i ≃ₗ ∀ i, P i` (a finite direct sum equals the product).
  set g := DirectSum.linearEquivFunOnFintype A ι (fun i => Fin (n i) → V i) with hg
  obtain ⟨r, hr, ⟨e⟩⟩ := subrepresentation_of_semisimple_pi n hd (Submodule.map g.toLinearMap W)
  refine ⟨r, hr, ⟨?_⟩⟩
  exact (Submodule.equivMapOfInjective g.toLinearMap g.injective W).trans
    (e.trans (DirectSum.linearEquivFunOnFintype A ι (fun i => Fin (r i) → V i)).symm)

end

section Matrix

variable {A : Type*} [Ring A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
  [∀ i, IsSimpleModule A (V i)]

omit [Fintype ι] [DecidableEq ι] in
/-- Schur's lemma for a pairwise nonisomorphic family of simple modules: every `A`-linear
map between two distinct members is zero. -/
private theorem hom_eq_zero_of_ne
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    {i j : ι} (hij : i ≠ j) (f : V i →ₗ[A] V j) : f = 0 := by
  by_contra h
  exact hij (hd ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero h)⟩)

omit [DecidableEq ι] in
/- Finiteness is needed by the finite block-matrix construction, although it does not occur in
the existential result type. -/
set_option linter.unusedFintypeInType false in
/-- **Proposition 3.1.4**, matrix form (`Pi` model of the ambient representation).

On top of `subrepresentation_of_semisimple_pi` this exhibits the inclusion `W ↪ ⊕ᵢ nᵢVᵢ`
in the book's shape: there are matrices `X i` over `Module.End A (V i)` with linearly
independent rows such that, writing `w ∈ W` in the coordinates supplied by
`e : W ≃ ⊕ᵢ rᵢVᵢ`, the `i`-th block of `w` is the row vector `e w i` multiplied by `X i`.
In particular the inclusion is block diagonal: block `i` of the image depends only on
block `i` of the source. -/
theorem subrepresentation_of_semisimple_matrix_pi (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (∀ i, Fin (n i) → V i)) :
    ∃ (r : ι → ℕ) (X : ∀ i, Matrix (Fin (r i)) (Fin (n i)) (Module.End A (V i)))
      (e : ↥W ≃ₗ[A] ∀ i, Fin (r i) → V i),
      (∀ i, r i ≤ n i) ∧
      (∀ i, LinearIndependent (Module.End A (V i))ᵐᵒᵖ (X i)) ∧
      ∀ (w : ↥W) (i : ι) (l : Fin (n i)),
        (w : ∀ k, Fin (n k) → V k) i l = ∑ a, X i a l (e w i a) := by
  classical
  obtain ⟨r, hr, ⟨e⟩⟩ := subrepresentation_of_semisimple_pi n hd W
  -- The inclusion `W ↪ ⊕ᵢ nᵢVᵢ`, read through the model `⊕ᵢ rᵢVᵢ` of `W`.
  set φ : (∀ k, Fin (r k) → V k) →ₗ[A] (∀ k, Fin (n k) → V k) :=
    W.subtype ∘ₗ (e.symm : (∀ k, Fin (r k) → V k) →ₗ[A] ↥W) with hφdef
  have hφinj : Function.Injective φ := W.subtype_injective.comp e.symm.injective
  -- Its scalar coordinates.
  set Φ : ∀ i : ι, Fin (n i) → ((∀ k, Fin (r k) → V k) →ₗ[A] V i) := fun i l =>
    (LinearMap.proj l) ∘ₗ (LinearMap.proj i) ∘ₗ φ with hΦdef
  -- The inclusion of the `a`-th copy of `V k` into `⊕ᵢ rᵢVᵢ`.
  set sr : ∀ k : ι, Fin (r k) → (V k →ₗ[A] (∀ k, Fin (r k) → V k)) := fun k a =>
    (LinearMap.single A (fun k => Fin (r k) → V k) k) ∘ₗ
      (LinearMap.single A (fun _ : Fin (r k) => V k) a) with hsrdef
  -- The full matrix of `φ`, including its off-diagonal blocks.
  set G : ∀ k : ι, Fin (r k) → ∀ i : ι, Fin (n i) → (V k →ₗ[A] V i) := fun k a i l =>
    (Φ i l) ∘ₗ (sr k a) with hGdef
  set X : ∀ i, Matrix (Fin (r i)) (Fin (n i)) (Module.End A (V i)) := fun i a l =>
    G i a i l with hXdef
  -- Off-diagonal blocks vanish: that is Schur's lemma plus pairwise nonisomorphism.
  have hoff : ∀ (k i : ι), k ≠ i → ∀ (a : Fin (r k)) (l : Fin (n i)), G k a i l = 0 :=
    fun k i hki a l => hom_eq_zero_of_ne hd hki _
  have decompR : ∀ y : ∀ k, Fin (r k) → V k,
      (∑ k, LinearMap.single A (fun k => Fin (r k) → V k) k (y k)) = y := by
    intro y
    simpa [LinearMap.single_apply] using Finset.univ_sum_single y
  have decompr : ∀ (k : ι) (z : Fin (r k) → V k),
      (∑ a, LinearMap.single A (fun _ : Fin (r k) => V k) a (z a)) = z := by
    intro k z
    simpa [LinearMap.single_apply] using Finset.univ_sum_single z
  -- The matrix formula for `φ`, valid on the whole of `⊕ᵢ rᵢVᵢ`.
  have key : ∀ (y : ∀ k, Fin (r k) → V k) (i : ι) (l : Fin (n i)),
      φ y i l = ∑ a, X i a l (y i a) := by
    intro y i l
    have h1 : Φ i l y = ∑ k, ∑ a, G k a i l (y k a) := by
      conv_lhs => rw [← decompR y]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [← decompr k (y k)]
      simp only [map_sum, hGdef, hsrdef, LinearMap.comp_apply]
    have h2 : (∑ k, ∑ a, G k a i l (y k a)) = ∑ a, G i a i l (y i a) := by
      refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
      simp [hoff k i hk]
    calc φ y i l = Φ i l y := rfl
      _ = ∑ a, G i a i l (y i a) := by rw [h1, h2]
      _ = ∑ a, X i a l (y i a) := by simp [hXdef]
  refine ⟨r, X, e, hr, ?_, ?_⟩
  · -- Linear independence of the rows of `X i`, from injectivity of `φ`.
    intro i
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have hc' : ∀ (l : Fin (n i)) (v : V i), (∑ b, X i b l ((c b).unop v)) = 0 := by
      intro l v
      have h := congrFun hc l
      rw [Finset.sum_apply] at h
      have h2 : (∑ b, X i b l * (c b).unop) = 0 := h
      have := congrArg (fun f : Module.End A (V i) => f v) h2
      simpa [Module.End.mul_apply] using this
    -- Every column vector `a ↦ (c a).unop v` is killed by `φ`, hence is zero.
    have hz : ∀ v : V i, ∀ b : Fin (r i), (c b).unop v = 0 := by
      intro v
      set z : Fin (r i) → V i := fun b => (c b).unop v with hzdef
      set y : ∀ k, Fin (r k) → V k :=
        LinearMap.single A (fun k => Fin (r k) → V k) i z with hydef
      have h0 : φ y = 0 := by
        funext j
        funext l'
        rw [key y j l']
        rcases eq_or_ne j i with rfl | hji
        · have hyj : y j = z := by simp [hydef, LinearMap.single_apply]
          rw [hyj]
          simpa using hc' l' v
        · have hyj : y j = 0 := by
            simp [hydef, LinearMap.single_apply, Pi.single_eq_of_ne hji]
          simp [hyj]
      have hy0 : y = 0 := hφinj (by rw [h0, map_zero])
      intro b
      have := congrFun (congrFun hy0 i) b
      simpa [hydef, LinearMap.single_apply] using this
    have : (c a).unop = 0 := by
      ext v
      exact hz v a
    exact MulOpposite.unop_injective (by simpa using this)
  · intro w i l
    have hw : (w : ∀ k, Fin (n k) → V k) = φ (e w) := by
      simp [hφdef]
    rw [hw]
    exact key (e w) i l

omit [DecidableEq ι] in
/- Finiteness is needed to pass between the external direct sum and its finite product model,
although it does not occur in the existential result type. -/
set_option linter.unusedFintypeInType false in
/-- **Proposition 3.1.4**, matrix form. See `subrepresentation_of_semisimple_matrix_pi`;
this is the same statement with the ambient representation written as an external direct
sum. Etingof Proposition 3.1.4. -/
theorem subrepresentation_of_semisimple_matrix (n : ι → ℕ)
    (hd : ∀ ⦃i j⦄, Nonempty (V i ≃ₗ[A] V j) → i = j)
    (W : Submodule A (⨁ i, (Fin (n i) → V i))) :
    ∃ (r : ι → ℕ) (X : ∀ i, Matrix (Fin (r i)) (Fin (n i)) (Module.End A (V i)))
      (e : ↥W ≃ₗ[A] ⨁ i, (Fin (r i) → V i)),
      (∀ i, r i ≤ n i) ∧
      (∀ i, LinearIndependent (Module.End A (V i))ᵐᵒᵖ (X i)) ∧
      ∀ (w : ↥W) (i : ι) (l : Fin (n i)),
        (w : ⨁ k, (Fin (n k) → V k)) i l = ∑ a, X i a l (e w i a) := by
  classical
  set g := DirectSum.linearEquivFunOnFintype A ι (fun i => Fin (n i) → V i) with hg
  obtain ⟨r, X, e, hr, hli, hform⟩ :=
    subrepresentation_of_semisimple_matrix_pi n hd (Submodule.map g.toLinearMap W)
  set g' := DirectSum.linearEquivFunOnFintype A ι (fun i => Fin (r i) → V i) with hg'
  set em := Submodule.equivMapOfInjective g.toLinearMap g.injective W with hem
  refine ⟨r, X, em.trans (e.trans g'.symm), hr, hli, ?_⟩
  intro w i l
  have h := hform (em w) i l
  -- `linearEquivFunOnFintype` is the coercion `⨁ i, M i → ∀ i, M i`, so both transports are
  -- invisible on coordinates.
  have hcoe : ∀ (z : ⨁ k, (Fin (n k) → V k)) (j : ι), g z j = z j := fun _ _ => rfl
  have hcoe' : ∀ (z : ⨁ k, (Fin (r k) → V k)) (j : ι), g' z j = z j := fun _ _ => rfl
  have hleft : ((em w : ↥(Submodule.map g.toLinearMap W)) : ∀ k, Fin (n k) → V k) i
      = (w : ⨁ k, (Fin (n k) → V k)) i := by
    rw [hem, Submodule.coe_equivMapOfInjective_apply]
    exact hcoe _ i
  have hright : ∀ a, (e (em w)) i a = ((em.trans (e.trans g'.symm)) w) i a := by
    intro a
    have hz : ((em.trans (e.trans g'.symm)) w) i = (g' (g'.symm (e (em w)))) i :=
      (hcoe' (g'.symm (e (em w))) i).symm
    rw [hz, g'.apply_symm_apply]
  rw [← hleft, h]
  exact Finset.sum_congr rfl fun a _ => by rw [hright a]

end Matrix

end Etingof

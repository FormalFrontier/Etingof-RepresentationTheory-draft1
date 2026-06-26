import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.Length
import Mathlib.Algebra.DirectSum.Module

/-!
# Proposition 3.1.4: Classification of Subrepresentations in Semisimple Representations

Let `Vᵢ`, `1 ≤ i ≤ m`, be irreducible finite dimensional pairwise nonisomorphic
representations of `A`, and let `W` be a subrepresentation of `V = ⊕ᵢ nᵢVᵢ`. Then `W`
is isomorphic to `⊕ᵢ rᵢVᵢ` with `rᵢ ≤ nᵢ`.

We formalize representations of the algebra `A` as `A`-modules. The hypotheses are:
the `V i` are simple (irreducible), finite-dimensional, and pairwise nonisomorphic. The
ambient representation `V = ⊕ᵢ nᵢ Vᵢ` is modeled by `⨁ i, (Fin (n i) → V i)` (each
`Fin (n i) → V i` is `nᵢ` copies of `Vᵢ`).

The substantive content of the proposition — and the part missing from a bare
"submodules of a semisimple module are semisimple" statement — is the *multiplicity
bound* `r i ≤ n i` together with the explicit isomorphism type `W ≅ ⊕ᵢ rᵢ Vᵢ`. Both are
asserted here. (The book additionally describes the inclusion `φ : W → V` by matrices
`X_i` with linearly independent rows; that structural description of the embedding is not
formalized.)

The proof uses the isotypic decomposition of the semisimple module `W`: `W` is the direct
sum of its `V i`-isotypic components `C i`, each `C i ≅ Fin (r i) → V i`, and `r i ≤ n i`
because `C i` embeds (length-monotonically) into the `V i`-isotypic component of `V`, which
is the `i`-th summand `Fin (n i) → V i` of length `n i`. Pairwise nonisomorphism is what
confines the `V i`-isotypic part of `V` to the `i`-th summand.
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
    push_neg at h
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
    push_neg at h
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

omit [∀ i, Module.Finite A (V i)] in
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
    intro k t _ hle
    have hit : IsIsotypicOfType A ↥t (V k) := le_isotypicComponent_iff.mp hle
    haveI : IsSimpleModule A ↥(⊤ : Submodule A ↥t) :=
      (LinearEquiv.isSimpleModule_iff Submodule.topEquiv).mpr ‹_›
    exact ⟨Submodule.topEquiv.symm.trans (hit ⊤).some⟩
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

omit [∀ i, Module.Finite A (V i)] in
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

end Etingof

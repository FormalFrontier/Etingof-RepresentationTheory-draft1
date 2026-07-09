import Mathlib

/-!
# Exercise 7.8.4: Exact sequences of vector spaces split

**Exercise 7.8.4.** Show that any exact sequence of vector spaces is isomorphic to a
direct sum of complexes of the form
`0 → V → V → 0`,
where `V` stands at the places `i` and `i + 1` and the map `V → V` is the identity (in
particular, any short exact sequence of vector spaces is split). Is this true in the
category of abelian groups?

## Formalization

Being isomorphic to a direct sum of contractible complexes `0 → V →^{id} V → 0` is
equivalent to the complex being **contractible**, i.e. the identity map is
null-homotopic. We state the headline claim `Exercise7_8_4` as: for every acyclic
cochain complex of `k`-vector spaces, the identity morphism is homotopic to `0`.

We also record the "in particular" consequence `Exercise7_8_4_split` (short exact
sequences of vector spaces split) and the answer to the final question,
`Exercise7_8_4_not_abelianGroups`: over `ℤ` this fails — there is a short exact
sequence of abelian groups (e.g. `0 → ℤ →^{·2} ℤ → ℤ/2 → 0`) that does not split.
-/

open CategoryTheory

/-- Exercise 7.8.4 (main claim): every acyclic (exact) cochain complex of vector spaces
over a field `k` is contractible — its identity morphism is null-homotopic — which is
equivalent to being isomorphic to a direct sum of contractible complexes
`0 → V →^{id} V → 0`. -/
theorem Etingof.Exercise7_8_4 {k : Type*} [Field k]
    (K : CochainComplex (ModuleCat.{0} k) ℤ) (hK : K.Acyclic) :
    Nonempty (Homotopy (𝟙 K) 0) := by
  sorry

/-- Exercise 7.8.4 (in particular): any short exact sequence of `k`-vector spaces is
split. -/
theorem Etingof.Exercise7_8_4_split {k : Type*} [Field k]
    (S : ShortComplex (ModuleCat.{0} k)) (hS : S.ShortExact) :
    Nonempty S.Splitting :=
  -- `S.X₃` is a `k`-vector space, hence free, hence projective, so the epi `S.g`
  -- has a section and the short exact sequence splits.
  ⟨hS.splittingOfProjective⟩

/-- Exercise 7.8.4 (final question): the statement is **not** true in the category of
abelian groups — there is a short exact sequence of abelian groups that does not split.
-/
theorem Etingof.Exercise7_8_4_not_abelianGroups :
    ∃ S : ShortComplex (ModuleCat.{0} ℤ), S.ShortExact ∧ IsEmpty S.Splitting := by
  -- The short exact sequence `0 → ℤ →^{·2} ℤ → ℤ/2 → 0`.
  let f : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id
  let g : ℤ →ₗ[ℤ] ZMod 2 := (Int.castAddHom (ZMod 2)).toIntLinearMap
  have hf : ∀ x : ℤ, f x = 2 * x := fun x => by simp [f]
  have hg : ∀ x : ℤ, g x = (x : ZMod 2) := fun x => by simp [g, AddMonoidHom.coe_toIntLinearMap]
  have hcomp : g.comp f = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hf, hg, LinearMap.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨x, by push_cast; ring⟩
  refine ⟨ShortComplex.moduleCatMk f g hcomp, ?_, ?_⟩
  · -- Short exactness.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · -- Exactness: `ker g = range f`, i.e. the kernel of `ℤ → ℤ/2` is the even integers.
      rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
      change LinearMap.ker g ≤ LinearMap.range f
      intro x hx
      rw [LinearMap.mem_ker, hg, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, ?_⟩
      rw [hf]
      push_cast at hc
      omega
    · -- `·2` is injective on `ℤ`.
      change Mono (ModuleCat.ofHom f)
      rw [ModuleCat.mono_iff_injective]
      have hinj : Function.Injective f := by
        intro a b hab; rw [hf, hf] at hab; omega
      exact fun a b hab => hinj hab
    · -- `ℤ → ℤ/2` is surjective.
      change Epi (ModuleCat.ofHom g)
      rw [ModuleCat.epi_iff_surjective]
      have hsurj : Function.Surjective g := by
        intro y
        refine ⟨(y.val : ℤ), ?_⟩
        rw [hg]; push_cast; exact ZMod.natCast_zmod_val y
      intro y
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨x, hx⟩
  · -- No splitting: a retraction `r` of `·2` would give `2 * r 1 = 1` in `ℤ`.
    refine ⟨fun sp => ?_⟩
    -- View the retraction as a genuine linear map `ρ : ℤ →ₗ[ℤ] ℤ` (the carriers are `ℤ`).
    let ρ : ℤ →ₗ[ℤ] ℤ := sp.r.hom
    have hr : ρ.comp f = LinearMap.id := by
      have h := ModuleCat.hom_ext_iff.mp sp.f_r
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
      exact h
    have key := DFunLike.congr_fun hr (1 : ℤ)
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, mul_one] at key
    -- `key : ρ 2 = 1`; but `ρ 2 = 2 * ρ 1` by linearity.
    have hlin : ρ (2 : ℤ) = 2 * ρ (1 : ℤ) := by
      have h := map_smul ρ (2 : ℤ) (1 : ℤ)
      simpa using h
    rw [hlin] at key
    omega

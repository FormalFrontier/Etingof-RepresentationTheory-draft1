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

## The contracting homotopy

The proof of the headline claim is the elementary degreewise-splitting construction,
valid for *unbounded* complexes.  For each degree `n` write `Kⁿ = Zⁿ ⊕ Wⁿ` where
`Zⁿ = ker dⁿ` and `Wⁿ` is a chosen complement.  Acyclicity gives
`range dⁿ = ker dⁿ⁺¹ = Zⁿ⁺¹`, so `dⁿ` restricts to an isomorphism `Wⁿ ≅ Zⁿ⁺¹`.  The
contracting homotopy `sⁿ⁺¹ : Kⁿ⁺¹ → Kⁿ` is the inverse of that isomorphism on `Zⁿ⁺¹`
and `0` on `Wⁿ⁺¹`; a pointwise splitting `x = z + w` then gives
`sⁿ⁺¹(dⁿ x) + dⁿ⁻¹(sⁿ x) = x`, i.e. `d ∘ s + s ∘ d = 𝟙`.
-/

open CategoryTheory

namespace Etingof.Exercise7_8_4Aux

variable {k : Type*} [Field k] (K : CochainComplex (ModuleCat.{0} k) ℤ)

/-- The cocycles `Zⁿ = ker dⁿ`, as a submodule of `Kⁿ`. -/
noncomputable def Zsub (n : ℤ) : Submodule k (K.X n) := LinearMap.ker (K.d n (n + 1)).hom

/-- A chosen complement `Wⁿ` of `Zⁿ` in `Kⁿ` (exists since `Kⁿ` is a vector space). -/
noncomputable def Wsub (n : ℤ) : Submodule k (K.X n) :=
  (Submodule.exists_isCompl (Zsub K n)).choose

lemma isCompl_Wsub (n : ℤ) : IsCompl (Zsub K n) (Wsub K n) :=
  (Submodule.exists_isCompl (Zsub K n)).choose_spec

/-- The differential `dⁿ` restricted to the complement `Wⁿ`. -/
noncomputable def dW (n : ℤ) : Wsub K n →ₗ[k] K.X (n + 1) :=
  (K.d n (n + 1)).hom ∘ₗ (Wsub K n).subtype

/-- Splitting an element of `Kⁿ` along `Kⁿ = Zⁿ ⊕ Wⁿ`. -/
lemma exists_split (n : ℤ) (x : K.X n) :
    ∃ z ∈ Zsub K n, ∃ w ∈ Wsub K n, z + w = x := by
  have hsup := (isCompl_Wsub K n).sup_eq_top
  have hx : x ∈ (⊤ : Submodule k (K.X n)) := Submodule.mem_top
  rw [← hsup, Submodule.mem_sup] at hx
  obtain ⟨z, hz, w, hw, hzw⟩ := hx
  exact ⟨z, hz, w, hw, hzw⟩

variable {K} in
/-- Acyclicity: `range dⁿ = ker dⁿ⁺¹ = Zⁿ⁺¹`. -/
lemma range_d_eq_Zsub (hK : K.Acyclic) (n : ℤ) :
    LinearMap.range (K.d n (n + 1)).hom = Zsub K (n + 1) := by
  have h := hK (n + 1)
  rw [K.exactAt_iff' n (n + 1) (n + 1 + 1)
      ((ComplexShape.up ℤ).prev_eq' (by simp))
      ((ComplexShape.up ℤ).next_eq' (by simp))] at h
  have hrk := h.moduleCat_range_eq_ker
  simpa [Zsub] using hrk

/-- `dⁿ` restricted to `Wⁿ` is injective. -/
lemma dW_injective (n : ℤ) : Function.Injective (dW K n) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  simp only [LinearMap.mem_ker, dW, LinearMap.comp_apply, Submodule.subtype_apply] at hw
  have hwZ : (w : K.X n) ∈ Zsub K n := hw
  have hwW : (w : K.X n) ∈ Wsub K n := w.2
  have hmem : (w : K.X n) ∈ Zsub K n ⊓ Wsub K n := ⟨hwZ, hwW⟩
  rw [(isCompl_Wsub K n).inf_eq_bot] at hmem
  simpa using hmem

variable {K} in
/-- The range of `dⁿ|_{Wⁿ}` is all of `Zⁿ⁺¹`. -/
lemma range_dW (hK : K.Acyclic) (n : ℤ) :
    LinearMap.range (dW K n) = Zsub K (n + 1) := by
  rw [← range_d_eq_Zsub hK n]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact ⟨(Wsub K n).subtype w, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz, w, hw, rfl⟩ := exists_split K n x
    rw [map_add]
    have hz0 : (K.d n (n + 1)).hom z = 0 := hz
    rw [hz0, zero_add]
    exact ⟨⟨w, hw⟩, rfl⟩

variable {K} in
/-- `IsCompl (range dⁿ|_{Wⁿ}) Wⁿ⁺¹`, used to build the projection defining `sⁿ⁺¹`. -/
lemma isCompl_range_dW (hK : K.Acyclic) (n : ℤ) :
    IsCompl (LinearMap.range (dW K n)) (Wsub K (n + 1)) := by
  rw [range_dW hK n]
  exact isCompl_Wsub K (n + 1)

variable {K} in
/-- The degreewise contracting homotopy `sⁿ⁺¹ : Kⁿ⁺¹ → Kⁿ`: the inverse of the
isomorphism `dⁿ|_{Wⁿ} : Wⁿ ≅ Zⁿ⁺¹` on `Zⁿ⁺¹`, and `0` on `Wⁿ⁺¹`. -/
noncomputable def sMap (hK : K.Acyclic) (n : ℤ) : K.X (n + 1) →ₗ[k] K.X n :=
  (Wsub K n).subtype ∘ₗ
    LinearMap.linearProjOfIsCompl (Wsub K (n + 1)) (dW K n) (dW_injective K n)
      (isCompl_range_dW hK n)

variable {K} in
/-- The homotopy relation `sⁿ⁺¹(dⁿ x) + dⁿ⁻¹(sⁿ x) = x` in degree `n + 1`. -/
lemma sMap_homotopy (hK : K.Acyclic) (n : ℤ) (x : K.X (n + 1)) :
    sMap hK (n + 1) ((K.d (n + 1) (n + 1 + 1)).hom x)
      + (K.d n (n + 1)).hom (sMap hK n x) = x := by
  -- split `x = z + w` with `z ∈ Zⁿ⁺¹`, `w ∈ Wⁿ⁺¹`
  obtain ⟨z, hz, w, hw, rfl⟩ := exists_split K (n + 1) x
  -- `z ∈ Zⁿ⁺¹ = range dⁿ|_{Wⁿ}`, so `z = dⁿ w₀` for a unique `w₀ ∈ Wⁿ`
  have hzrange : z ∈ LinearMap.range (dW K n) := by rw [range_dW hK n]; exact hz
  obtain ⟨w0, hw0⟩ := hzrange
  -- second summand: `dⁿ(sⁿ(z + w)) = z`
  have hproj2 : (LinearMap.linearProjOfIsCompl (Wsub K (n + 1)) (dW K n)
      (dW_injective K n) (isCompl_range_dW hK n)) (z + w) = w0 := by
    rw [map_add, ← hw0, LinearMap.linearProjOfIsCompl_apply_left,
      LinearMap.linearProjOfIsCompl_apply_right' (Wsub K (n + 1)) (dW K n)
        (dW_injective K n) (isCompl_range_dW hK n) w hw, add_zero]
  have hsecond : (K.d n (n + 1)).hom (sMap hK n (z + w)) = z := by
    rw [sMap, LinearMap.comp_apply, hproj2, ← hw0]
    rfl
  -- first summand: `sⁿ⁺¹(dⁿ⁺¹(z + w)) = w`
  have hzker : (K.d (n + 1) (n + 1 + 1)).hom z = 0 := hz
  have hwd : (K.d (n + 1) (n + 1 + 1)).hom w = dW K (n + 1) ⟨w, hw⟩ := by
    rw [dW, LinearMap.comp_apply, Submodule.subtype_apply]
  have hproj1 : (LinearMap.linearProjOfIsCompl (Wsub K (n + 1 + 1)) (dW K (n + 1))
      (dW_injective K (n + 1)) (isCompl_range_dW hK (n + 1)))
      ((K.d (n + 1) (n + 1 + 1)).hom (z + w)) = ⟨w, hw⟩ := by
    rw [map_add, hzker, zero_add, hwd, LinearMap.linearProjOfIsCompl_apply_left]
  have hfirst : sMap hK (n + 1) ((K.d (n + 1) (n + 1 + 1)).hom (z + w)) = w := by
    rw [sMap, LinearMap.comp_apply, hproj1, Submodule.subtype_apply]
  rw [hfirst, hsecond]
  abel

variable {K} in
/-- The degreewise contracting homotopy assembled into a family of morphisms
`hom i j : Kⁱ ⟶ Kʲ`, nonzero only when `i = j + 1`. -/
noncomputable def htpy (hK : K.Acyclic) (i j : ℤ) : K.X i ⟶ K.X j :=
  if h : i = j + 1 then eqToHom (congrArg K.X h) ≫ ModuleCat.ofHom (sMap hK j) else 0

variable {K} in
@[simp] lemma htpy_succ (hK : K.Acyclic) (j : ℤ) :
    htpy hK (j + 1) j = ModuleCat.ofHom (sMap hK j) := by
  rw [htpy, dif_pos rfl]; simp

variable {K} in
lemma htpy_eq_zero (hK : K.Acyclic) {i j : ℤ} (h : ¬ i = j + 1) :
    htpy hK i j = 0 := dif_neg h

end Etingof.Exercise7_8_4Aux

/-- Exercise 7.8.4 (main claim): every acyclic (exact) cochain complex of vector spaces
over a field `k` is contractible — its identity morphism is null-homotopic — which is
equivalent to being isomorphic to a direct sum of contractible complexes
`0 → V →^{id} V → 0`. -/
theorem Etingof.Exercise7_8_4 {k : Type*} [Field k]
    (K : CochainComplex (ModuleCat.{0} k) ℤ) (hK : K.Acyclic) :
    Nonempty (Homotopy (𝟙 K) 0) := by
  refine ⟨{ hom := Etingof.Exercise7_8_4Aux.htpy hK, zero := ?_, comm := ?_ }⟩
  · -- the homotopy vanishes off the relation `j + 1 = i`
    intro i j hij
    refine Etingof.Exercise7_8_4Aux.htpy_eq_zero hK (fun h => hij ?_)
    rw [ComplexShape.up_Rel]; exact h.symm
  · -- the homotopy relation, checked degreewise
    intro i
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, i = m + 1 := ⟨i - 1, by ring⟩
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (m + 1) (m + 1 + 1) by simp),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel m (m + 1) by simp),
        Etingof.Exercise7_8_4Aux.htpy_succ, Etingof.Exercise7_8_4Aux.htpy_succ]
    apply ModuleCat.hom_ext
    ext x
    simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply,
      HomologicalComplex.zero_f, add_zero]
    exact (Etingof.Exercise7_8_4Aux.sMap_homotopy hK m x).symm

/-- Exercise 7.8.4 (in particular): any short exact sequence of `k`-vector spaces is
split. -/
theorem Etingof.Exercise7_8_4_split {k : Type*} [Field k]
    (S : ShortComplex (ModuleCat.{0} k)) (hS : S.ShortExact) :
    Nonempty S.Splitting := by
  sorry

/-- Exercise 7.8.4 (final question): the statement is **not** true in the category of
abelian groups — there is a short exact sequence of abelian groups that does not split.
-/
theorem Etingof.Exercise7_8_4_not_abelianGroups :
    ∃ S : ShortComplex (ModuleCat.{0} ℤ), S.ShortExact ∧ IsEmpty S.Splitting := by
  sorry

import Mathlib

set_option backward.isDefEq.respectTransparency false

/-!
# Exercise 7.8.4: Exact sequences of vector spaces split

**Exercise 7.8.4.** Show that any exact sequence of vector spaces is isomorphic to a
direct sum of complexes of the form
`0 → V → V → 0`,
where `V` stands at the places `i` and `i + 1` and the map `V → V` is the identity (in
particular, any short exact sequence of vector spaces is split). Is this true in the
category of abelian groups?

## Formalization

`Exercise7_8_4_directSum` is the conclusion the exercise asks for: for every acyclic cochain
complex `K` of `k`-vector spaces there are a family of vector spaces `V : ℤ → ModuleCat k`, a
family of complexes `D i` concentrated in degrees `i` and `i + 1` with `(D i).X i = V i`,
`(D i).X (i + 1) = V i` and an isomorphism between them, and an isomorphism `K ≅ ∐ D`.  The
summands are `disk (Wⁱ) i` (see below), and `disk_d_self` says their differential is the
identity of `Wⁱ` transported along those two equalities, so they are literally the complexes
`0 → V →^{id} V → 0` of the statement.

`Exercise7_8_4` records the equivalent contractibility statement: for every acyclic cochain
complex of `k`-vector spaces the identity morphism is homotopic to `0`.

We also record the "in particular" consequence `Exercise7_8_4_split` (short exact
sequences of vector spaces split) and the answer to the final question,
`Exercise7_8_4_not_abelianGroups`: over `ℤ` this fails, since there is a short exact
sequence of abelian groups (e.g. `0 → ℤ →^{·2} ℤ → ℤ/2 → 0`) that does not split.

## The decomposition

`disk V i` is the two-term complex with `V` in degrees `i` and `i + 1` and the identity between
them.  With `Kⁿ = Zⁿ ⊕ Wⁿ` as below, `isoDiskSum` is the isomorphism `K ≅ ∐ᵢ disk (Wⁱ) i`.  Its
inverse `fromDiskSum` sends the `i`-th summand to `Wⁱ ↪ Kⁱ` in degree `i` and to `dⁱ|_{Wⁱ}` in
degree `i + 1`; the forward map `toDiskSum` is, in degree `n`, the projection `Kⁿ ↠ Wⁿ` into
the `n`-th summand plus the contracting homotopy `Kⁿ → Wⁿ⁻¹` into the `(n-1)`-st.  That these
are mutually inverse is exactly the degreewise splitting `Kⁿ⁺¹ = Wⁿ⁺¹ ⊕ dⁿ(Wⁿ)`
(`projW_add_d_sW`).

## The contracting homotopy

The proof of the headline claim is the elementary degreewise-splitting construction,
valid for unbounded complexes.  For each degree `n` write `Kⁿ = Zⁿ ⊕ Wⁿ` where
`Zⁿ = ker dⁿ` and `Wⁿ` is a chosen complement.  Acyclicity gives
`range dⁿ = ker dⁿ⁺¹ = Zⁿ⁺¹`, so `dⁿ` restricts to an isomorphism `Wⁿ ≅ Zⁿ⁺¹`.  The
contracting homotopy `sⁿ⁺¹ : Kⁿ⁺¹ → Kⁿ` is the inverse of that isomorphism on `Zⁿ⁺¹`
and `0` on `Wⁿ⁺¹`; a pointwise splitting `x = z + w` then gives
`sⁿ⁺¹(dⁿ x) + dⁿ⁻¹(sⁿ x) = x`, i.e. `d ∘ s + s ∘ d = 𝟙`.
-/

open CategoryTheory

universe u

namespace Etingof.Exercise7_8_4Aux

variable {k : Type u} [Field k] (K : CochainComplex (ModuleCat.{u} k) ℤ)

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

/-!
## The two-term complexes `0 → V →^{id} V → 0`

The exercise asks for an isomorphism onto a direct sum of complexes concentrated in two
adjacent degrees with the identity between them.  `disk V i` is that complex, with `V` in
degrees `i` and `i + 1`.
-/

section Disk

open CategoryTheory.Limits
open scoped ZeroObject

/-- The degree-`n` object of the two-term complex `0 → V →^{id} V → 0` with `V` placed in
degrees `i` and `i + 1`. -/
noncomputable def diskX (V : ModuleCat.{u} k) (i n : ℤ) : ModuleCat.{u} k :=
  if n = i ∨ n = i + 1 then V else 0

lemma diskX_eq_self {V : ModuleCat.{u} k} {i n : ℤ} (h : n = i ∨ n = i + 1) :
    diskX V i n = V := if_pos h

lemma diskX_eq_zero {V : ModuleCat.{u} k} {i n : ℤ} (h : ¬(n = i ∨ n = i + 1)) :
    diskX V i n = 0 := if_neg h

lemma isZero_diskX {V : ModuleCat.{u} k} {i n : ℤ} (h : ¬(n = i ∨ n = i + 1)) :
    IsZero (diskX V i n) :=
  (isZero_zero _).of_iso (eqToIso (diskX_eq_zero h))

/-- **The two-term complex `0 → V →^{id} V → 0`**, with `V` in degrees `i` and `i + 1` and the
identity of `V` as the only nonzero differential. -/
noncomputable def disk (V : ModuleCat.{u} k) (i : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ where
  X n := diskX V i n
  d m n :=
    if h : m = i ∧ n = i + 1 then
      eqToHom (diskX_eq_self (Or.inl h.1)) ≫ eqToHom (diskX_eq_self (Or.inr h.2)).symm
    else 0
  shape _ _ hmn := dif_neg fun h => hmn (by simp [ComplexShape.up_Rel, h.1, h.2])
  d_comp_d' m n p _ _ := by
    by_cases h : m = i ∧ n = i + 1
    · have h2 : ¬(n = i ∧ p = i + 1) := by rintro ⟨hn, -⟩; rw [h.2] at hn; omega
      rw [dif_neg h2, comp_zero]
    · rw [dif_neg h, zero_comp]

@[simp] lemma disk_X (V : ModuleCat.{u} k) (i n : ℤ) : (disk V i).X n = diskX V i n := rfl

/-- Outside degrees `i` and `i + 1` the two-term complex vanishes. -/
lemma isZero_disk_X {V : ModuleCat.{u} k} {i n : ℤ} (h : ¬(n = i ∨ n = i + 1)) :
    IsZero ((disk V i).X n) := isZero_diskX h

lemma disk_d_self (V : ModuleCat.{u} k) (i : ℤ) :
    (disk V i).d i (i + 1) = eqToHom (diskX_eq_self (Or.inl rfl)) ≫
      eqToHom (diskX_eq_self (V := V) (i := i) (Or.inr rfl)).symm :=
  dif_pos ⟨rfl, rfl⟩

lemma disk_d_eq_zero (V : ModuleCat.{u} k) (i : ℤ) {m n : ℤ} (h : ¬(m = i ∧ n = i + 1)) :
    (disk V i).d m n = 0 := dif_neg h

/-- **The differential of the two-term complex is the identity of `V`.** Together with
`isZero_disk_X` this pins `disk V i` down as the complex `0 → V →^{id} V → 0` of the exercise. -/
instance isIso_disk_d (V : ModuleCat.{u} k) (i : ℤ) : IsIso ((disk V i).d i (i + 1)) := by
  have h : (disk V i).d i (i + 1) =
      eqToHom ((diskX_eq_self (V := V) (i := i) (Or.inl rfl)).trans
        (diskX_eq_self (V := V) (i := i) (Or.inr rfl)).symm) := by
    rw [disk_d_self, eqToHom_trans]
  rw [h]; infer_instance

/-- A morphism out of `disk V i` is determined by its value `V ⟶ Kⁱ` in degree `i`. -/
noncomputable def diskDesc {V : ModuleCat.{u} k} {i : ℤ}
    {L : CochainComplex (ModuleCat.{u} k) ℤ} (f : V ⟶ L.X i) : disk V i ⟶ L where
  f n :=
    if h : n = i then
      eqToHom (diskX_eq_self (Or.inl h)) ≫ f ≫ eqToHom (congrArg L.X h.symm)
    else if h' : n = i + 1 then
      eqToHom (diskX_eq_self (Or.inr h')) ≫ f ≫ L.d i (i + 1) ≫ eqToHom (congrArg L.X h'.symm)
    else 0
  comm' m n hmn := by
    rw [ComplexShape.up_Rel] at hmn
    by_cases hm : m = i
    · subst hm
      obtain rfl : n = m + 1 := hmn.symm
      rw [disk_d_self, dif_pos rfl, dif_neg (by omega), dif_pos rfl]
      simp
    · rw [disk_d_eq_zero V i (by tauto), zero_comp, dif_neg hm]
      by_cases hm' : m = i + 1
      · subst hm'
        obtain rfl : n = i + 1 + 1 := hmn.symm
        rw [dif_pos rfl]
        simp only [Category.assoc, eqToHom_refl, Category.comp_id,
          HomologicalComplex.d_comp_d, comp_zero]
      · rw [dif_neg hm', zero_comp]

lemma diskDesc_f_of_eq {V : ModuleCat.{u} k} {i n : ℤ}
    {L : CochainComplex (ModuleCat.{u} k) ℤ} (f : V ⟶ L.X i) (h : n = i) :
    (diskDesc f).f n = eqToHom (diskX_eq_self (Or.inl h)) ≫ f ≫ eqToHom (congrArg L.X h.symm) :=
  dif_pos h

lemma diskDesc_f_of_eq_succ {V : ModuleCat.{u} k} {i n : ℤ}
    {L : CochainComplex (ModuleCat.{u} k) ℤ} (f : V ⟶ L.X i) (h : n = i + 1) :
    (diskDesc f).f n = eqToHom (diskX_eq_self (Or.inr h)) ≫ f ≫ L.d i (i + 1) ≫
      eqToHom (congrArg L.X h.symm) :=
  (dif_neg (show ¬(n = i) by omega)).trans (dif_pos h)

/-- Two morphisms out of `disk V i` agreeing in degrees `i` and `i + 1` are equal. -/
lemma disk_hom_ext {V : ModuleCat.{u} k} {i : ℤ} {L : CochainComplex (ModuleCat.{u} k) ℤ}
    (α β : disk V i ⟶ L) (h0 : α.f i = β.f i) (h1 : α.f (i + 1) = β.f (i + 1)) : α = β := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases h : n = i
  · subst h; exact h0
  · by_cases h' : n = i + 1
    · subst h'; exact h1
    · exact (isZero_diskX (V := V) (i := i) (n := n) (by tauto)).eq_of_src _ _

end Disk

/-!
## The decomposition of an acyclic complex

The summands are the chosen complements: the `i`-th one is `disk Wⁱ i`, i.e. `Wⁱ` placed in
degrees `i` and `i + 1`.  In degree `n` only the summands `i = n` and `i = n - 1` contribute,
matching the two halves of `Kⁿ = Wⁿ ⊕ Zⁿ` together with `Zⁿ ≅ Wⁿ⁻¹`.
-/

section DirectSum

open CategoryTheory.Limits

/-- The chosen complement `Wⁿ`, as an object of `ModuleCat k`. -/
noncomputable def Wob (n : ℤ) : ModuleCat.{u} k := ModuleCat.of k (Wsub K n)

/-- The inclusion `Wⁿ ↪ Kⁿ`. -/
noncomputable def Winc (n : ℤ) : Wob K n ⟶ K.X n := ModuleCat.ofHom (Wsub K n).subtype

/-- The projection `Kⁿ ↠ Wⁿ` along `Kⁿ = Zⁿ ⊕ Wⁿ`, as a linear map. -/
noncomputable def projW (n : ℤ) : K.X n →ₗ[k] Wsub K n :=
  (Wsub K n).projectionOnto (Zsub K n) (isCompl_Wsub K n).symm

/-- The projection `Kⁿ ↠ Wⁿ`. -/
noncomputable def Wproj (n : ℤ) : K.X n ⟶ Wob K n := ModuleCat.ofHom (projW K n)

lemma projW_coe (n : ℤ) (w : Wsub K n) : projW K n (w : K.X n) = w :=
  Submodule.projectionOnto_apply_left _ w

lemma projW_of_mem_Z (n : ℤ) {z : K.X n} (hz : z ∈ Zsub K n) : projW K n z = 0 :=
  Submodule.projectionOnto_apply_right _ ⟨z, hz⟩

lemma projW_d (n : ℤ) (x : K.X n) : projW K (n + 1) ((K.d n (n + 1)).hom x) = 0 := by
  refine projW_of_mem_Z K (n + 1) ?_
  have h := congrArg (fun f : K.X n ⟶ K.X (n + 1 + 1) => f.hom x)
    (K.d_comp_d n (n + 1) (n + 1 + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  exact h

/-- `Wⁿ ↪ Kⁿ ↠ Wⁿ` is the identity. -/
@[reassoc]
lemma Winc_comp_Wproj (n : ℤ) : Winc K n ≫ Wproj K n = 𝟙 (Wob K n) := by
  apply ModuleCat.hom_ext
  ext w
  exact projW_coe K n w

/-- The differential lands in `Zⁿ⁺¹`, which the projection onto `Wⁿ⁺¹` kills. -/
@[reassoc]
lemma d_comp_Wproj (n : ℤ) : K.d n (n + 1) ≫ Wproj K (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  ext x
  exact projW_d K n x

variable {K}

/-- The inverse of `dⁿ|_{Wⁿ} : Wⁿ ≅ Zⁿ⁺¹`, extended by `0` on `Wⁿ⁺¹`; the linear map underlying
the contracting homotopy `sⁿ⁺¹`. -/
noncomputable def sW (hK : K.Acyclic) (n : ℤ) : K.X (n + 1) →ₗ[k] Wsub K n :=
  LinearMap.linearProjOfIsCompl (Wsub K (n + 1)) (dW K n) (dW_injective K n)
    (isCompl_range_dW hK n)

/-- The contracting homotopy, with values in the chosen complement. -/
noncomputable def Wsplit (hK : K.Acyclic) (n : ℤ) : K.X (n + 1) ⟶ Wob K n :=
  ModuleCat.ofHom (sW hK n)

lemma sW_dW (hK : K.Acyclic) (n : ℤ) (w : Wsub K n) : sW hK n (dW K n w) = w :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ w

lemma sW_of_mem_W (hK : K.Acyclic) (n : ℤ) {x : K.X (n + 1)} (hx : x ∈ Wsub K (n + 1)) :
    sW hK n x = 0 :=
  LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ x hx

/-- **`sⁿ ∘ dⁿ⁻¹` is the projection onto `Wⁿ`.** -/
lemma sW_comp_d (hK : K.Acyclic) (n : ℤ) (x : K.X n) :
    sW hK n ((K.d n (n + 1)).hom x) = projW K n x := by
  obtain ⟨z, hz, w, hw, rfl⟩ := exists_split K n x
  have hz0 : (K.d n (n + 1)).hom z = 0 := hz
  have hwd : (K.d n (n + 1)).hom w = dW K n ⟨w, hw⟩ := rfl
  rw [map_add, hz0, hwd, zero_add, sW_dW, map_add, projW_of_mem_Z K n hz, zero_add]
  exact (projW_coe K n ⟨w, hw⟩).symm

@[reassoc]
lemma d_comp_Wsplit (hK : K.Acyclic) (n : ℤ) : K.d n (n + 1) ≫ Wsplit hK n = Wproj K n := by
  apply ModuleCat.hom_ext
  ext x
  exact sW_comp_d hK n x

@[reassoc]
lemma Winc_comp_Wsplit (hK : K.Acyclic) (n : ℤ) : Winc K (n + 1) ≫ Wsplit hK n = 0 := by
  apply ModuleCat.hom_ext
  ext w
  exact sW_of_mem_W hK n w.2

/-- **`Kⁿ⁺¹ = Wⁿ⁺¹ ⊕ dⁿ(Wⁿ)`.** This is the degreewise splitting that makes the comparison
morphism an isomorphism. -/
lemma projW_add_d_sW (hK : K.Acyclic) (n : ℤ) (x : K.X (n + 1)) :
    ((projW K (n + 1) x : K.X (n + 1))) + (K.d n (n + 1)).hom ((sW hK n x : K.X n)) = x := by
  obtain ⟨z, hz, w, hw, rfl⟩ := exists_split K (n + 1) x
  have hzr : z ∈ LinearMap.range (dW K n) := by rw [range_dW hK n]; exact hz
  obtain ⟨w0, rfl⟩ := hzr
  have hfirst : projW K (n + 1) (dW K n w0 + w) = ⟨w, hw⟩ := by
    rw [map_add, projW_of_mem_Z K (n + 1) hz, zero_add]
    exact projW_coe K (n + 1) ⟨w, hw⟩
  have hsecond : sW hK n (dW K n w0 + w) = w0 := by
    rw [map_add, sW_dW, sW_of_mem_W hK n hw, add_zero]
  rw [hfirst, hsecond]
  change (w : K.X (n + 1)) + dW K n w0 = _
  exact add_comm _ _

variable (K)

/-- The family of two-term complexes: the `i`-th summand is `Wⁱ` in degrees `i` and `i + 1`. -/
noncomputable def diskFam (i : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ := disk (Wob K i) i

/-- The `i`-th summand mapped into `K`: the inclusion `Wⁱ ↪ Kⁱ` in degree `i`, and `dⁱ|_{Wⁱ}` in
degree `i + 1`. -/
noncomputable def diskInc (i : ℤ) : diskFam K i ⟶ K := diskDesc (Winc K i)

/-- The comparison morphism `∐ᵢ (Wⁱ in degrees i, i+1) ⟶ K`. -/
noncomputable def fromDiskSum : (∐ diskFam K) ⟶ K := Sigma.desc (diskInc K)

lemma ι_comp_fromDiskSum (i n : ℤ) :
    (Sigma.ι (diskFam K) i).f n ≫ (fromDiskSum K).f n = (diskInc K i).f n := by
  rw [← HomologicalComplex.comp_f, fromDiskSum, Sigma.ι_desc]

/-- The degree-`n` component of `K ⟶ ∐` coming from the summand indexed by `n` itself. -/
noncomputable def newPart (n : ℤ) : K.X n ⟶ (∐ diskFam K).X n :=
  Wproj K n ≫ eqToHom (diskX_eq_self (V := Wob K n) (i := n) (Or.inl rfl)).symm ≫
    (Sigma.ι (diskFam K) n).f n

variable {K}

/-- The degree-`n` component of `K ⟶ ∐` coming from the summand indexed by `m`; it is nonzero
only for `n = m + 1`. -/
noncomputable def oldPart (hK : K.Acyclic) (m n : ℤ) : K.X n ⟶ (∐ diskFam K).X n :=
  if h : n = m + 1 then
    eqToHom (congrArg K.X h) ≫ Wsplit hK m ≫
      eqToHom (diskX_eq_self (V := Wob K m) (i := m) (Or.inr h)).symm ≫
      (Sigma.ι (diskFam K) m).f n
  else 0

lemma oldPart_eq_zero (hK : K.Acyclic) {m n : ℤ} (h : ¬n = m + 1) : oldPart hK m n = 0 :=
  dif_neg h

lemma oldPart_succ (hK : K.Acyclic) (m : ℤ) :
    oldPart hK m (m + 1) = Wsplit hK m ≫
      eqToHom (diskX_eq_self (V := Wob K m) (i := m) (Or.inr rfl)).symm ≫
      (Sigma.ι (diskFam K) m).f (m + 1) := by
  rw [oldPart, dif_pos rfl]
  simp

/-- Composing the "new" component with the differential of the direct sum lands in the same
summand, one degree up. -/
lemma newPart_comp_d (m : ℤ) :
    newPart K m ≫ (∐ diskFam K).d m (m + 1) = Wproj K m ≫
      eqToHom (diskX_eq_self (V := Wob K m) (i := m) (Or.inr rfl)).symm ≫
      (Sigma.ι (diskFam K) m).f (m + 1) := by
  rw [newPart, Category.assoc, Category.assoc, (Sigma.ι (diskFam K) m).comm m (m + 1)]
  simp only [diskFam, disk_d_self]
  simp

/-- The direct-sum differential kills the summand indexed by `m - 1` in degree `m`. -/
lemma oldPart_comp_d (hK : K.Acyclic) (m : ℤ) :
    oldPart hK (m - 1) m ≫ (∐ diskFam K).d m (m + 1) = 0 := by
  rw [oldPart, dif_pos (show m = m - 1 + 1 by omega), Category.assoc, Category.assoc,
    Category.assoc, (Sigma.ι (diskFam K) (m - 1)).comm m (m + 1)]
  simp only [diskFam, disk_d_eq_zero _ _ (show ¬(m = m - 1 ∧ m + 1 = m - 1 + 1) by omega)]
  simp

/-- **The inverse comparison morphism** `K ⟶ ∐ᵢ (Wⁱ in degrees i, i+1)`, built from the
degreewise splitting `Kⁿ = Wⁿ ⊕ dⁿ⁻¹(Wⁿ⁻¹)`. -/
noncomputable def toDiskSum (hK : K.Acyclic) : K ⟶ (∐ diskFam K) where
  f n := newPart K n + oldPart hK (n - 1) n
  comm' m n hmn := by
    rw [ComplexShape.up_Rel] at hmn
    subst hmn
    simp only [show m + 1 - 1 = m from by omega, Preadditive.comp_add, Preadditive.add_comp]
    rw [newPart_comp_d, oldPart_comp_d, add_zero]
    simp only [newPart, oldPart_succ, d_comp_Wproj_assoc, d_comp_Wsplit_assoc,
      zero_comp, zero_add]

lemma toDiskSum_f (hK : K.Acyclic) (n : ℤ) :
    (toDiskSum hK).f n = newPart K n + oldPart hK (n - 1) n := rfl

/-- **The comparison morphisms are mutually inverse (one way).** -/
lemma toDiskSum_comp_fromDiskSum (hK : K.Acyclic) : toDiskSum hK ≫ fromDiskSum K = 𝟙 K := by
  apply HomologicalComplex.hom_ext
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [HomologicalComplex.comp_f, toDiskSum_f, show m + 1 - 1 = m from by omega,
    Preadditive.add_comp, newPart, oldPart_succ, Category.assoc, ι_comp_fromDiskSum,
    diskInc, HomologicalComplex.id_f]
  rw [diskDesc_f_of_eq (Winc K (m + 1)) rfl, diskDesc_f_of_eq_succ (Winc K m) rfl]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, eqToHom_trans_assoc]
  apply ModuleCat.hom_ext
  ext x
  exact projW_add_d_sW hK m x

/-- **The comparison morphisms are mutually inverse (the other way).** -/
lemma fromDiskSum_comp_toDiskSum (hK : K.Acyclic) :
    fromDiskSum K ≫ toDiskSum hK = 𝟙 (∐ diskFam K) := by
  refine Sigma.hom_ext _ _ fun i => ?_
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [← Category.assoc, fromDiskSum, Sigma.ι_desc, Category.comp_id]
  refine disk_hom_ext _ _ ?_ ?_
  · rw [HomologicalComplex.comp_f, toDiskSum_f, show m + 1 - 1 = m from by omega]
    simp only [diskInc, diskDesc_f_of_eq (Winc K (m + 1)) rfl, Preadditive.comp_add, newPart,
      oldPart_succ, Category.assoc, eqToHom_refl, Category.comp_id,
      Winc_comp_Wproj_assoc, Winc_comp_Wsplit_assoc, Category.id_comp, zero_comp, comp_zero,
      add_zero, eqToHom_trans_assoc]
  · rw [HomologicalComplex.comp_f, toDiskSum_f, show m + 1 + 1 - 1 = m + 1 from by omega]
    simp only [diskInc, diskDesc_f_of_eq_succ (Winc K (m + 1)) rfl, Preadditive.comp_add,
      newPart, oldPart_succ, Category.assoc, eqToHom_refl, Category.comp_id,
      d_comp_Wproj_assoc, d_comp_Wsplit_assoc, Winc_comp_Wproj_assoc, Category.id_comp,
      zero_comp, comp_zero, zero_add, eqToHom_trans_assoc]

/-- **Exercise 7.8.4.** An acyclic complex of vector spaces is isomorphic to the direct sum of
the two-term complexes `0 → Wⁱ →^{id} Wⁱ → 0`, where `Wⁱ` is a chosen complement of the
cocycles `Zⁱ ⊆ Kⁱ`. -/
noncomputable def isoDiskSum (hK : K.Acyclic) : K ≅ (∐ diskFam K) where
  hom := toDiskSum hK
  inv := fromDiskSum K
  hom_inv_id := toDiskSum_comp_fromDiskSum hK
  inv_hom_id := fromDiskSum_comp_toDiskSum hK

end DirectSum

end Etingof.Exercise7_8_4Aux

open CategoryTheory.Limits in
/-- **Exercise 7.8.4 (the source conclusion).** Every exact sequence of vector spaces — that is,
every acyclic cochain complex `K` of `k`-vector spaces — is isomorphic to a direct sum of
complexes of the form `0 → V → V → 0`, with `V` at the places `i` and `i + 1` and an
isomorphism between them.

The summands are `Exercise7_8_4Aux.disk (Wⁱ) i`, where `Wⁱ` is a chosen complement of the
cocycles `Zⁱ ⊆ Kⁱ`; the isomorphism is `Exercise7_8_4Aux.isoDiskSum`, whose two components are
the degreewise projection `Kⁿ ↠ Wⁿ` together with the contracting homotopy, and the inclusion
`Wⁱ ↪ Kⁱ` together with `dⁱ|_{Wⁱ}`.

The four conditions on the summands say exactly that `D i` is the two-term complex
`0 → V i →^{≅} V i → 0` concentrated in degrees `i` and `i + 1`; for the summands actually used
the differential is literally the identity of `V i` transported along those two equalities
(`Exercise7_8_4Aux.disk_d_self`). -/
theorem Etingof.Exercise7_8_4_directSum {k : Type u} [Field k]
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (hK : K.Acyclic) :
    ∃ (V : ℤ → ModuleCat.{u} k) (D : ℤ → CochainComplex (ModuleCat.{u} k) ℤ),
      (∀ i, (D i).X i = V i) ∧ (∀ i, (D i).X (i + 1) = V i) ∧
      (∀ i n, ¬(n = i ∨ n = i + 1) → IsZero ((D i).X n)) ∧
      (∀ i, IsIso ((D i).d i (i + 1))) ∧
      Nonempty (K ≅ ∐ D) := by
  refine ⟨Etingof.Exercise7_8_4Aux.Wob K, Etingof.Exercise7_8_4Aux.diskFam K,
    fun i => Etingof.Exercise7_8_4Aux.diskX_eq_self (Or.inl rfl),
    fun i => Etingof.Exercise7_8_4Aux.diskX_eq_self (Or.inr rfl),
    fun i n h => Etingof.Exercise7_8_4Aux.isZero_disk_X h,
    fun i => Etingof.Exercise7_8_4Aux.isIso_disk_d _ _,
    ⟨Etingof.Exercise7_8_4Aux.isoDiskSum hK⟩⟩

/-- Exercise 7.8.4 (main claim): every acyclic (exact) cochain complex of vector spaces
over a field `k` is contractible (its identity morphism is null-homotopic), which is
equivalent to being isomorphic to a direct sum of contractible complexes
`0 → V →^{id} V → 0` (`Etingof.Exercise7_8_4_directSum`). -/
theorem Etingof.Exercise7_8_4 {k : Type u} [Field k]
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (hK : K.Acyclic) :
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
theorem Etingof.Exercise7_8_4_split {k : Type u} [Field k]
    (S : ShortComplex (ModuleCat.{u} k)) (hS : S.ShortExact) :
    Nonempty S.Splitting :=
  -- `S.X₃` is a `k`-vector space, hence free, hence projective, so the epi `S.g`
  -- has a section and the short exact sequence splits.
  ⟨hS.splittingOfProjective⟩

/-- Exercise 7.8.4 (final question): the statement is not true in the category of
abelian groups, since there is a short exact sequence of abelian groups that does not split.
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
    -- View the retraction as a linear map `ρ : ℤ →ₗ[ℤ] ℤ` (the carriers are `ℤ`).
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

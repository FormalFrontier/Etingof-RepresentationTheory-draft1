import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import EtingofRepresentationTheory.Chapter9.Definition9_5_1

/-!
# Problem 9.3.2: a four-dimensional algebra with a single block

Etingof's Problem 9.3.2 asks to study the `ℂ`-algebra

  `A = ℂ⟨g, x⟩ / (gx + xg, x², g² - 1)`,

a four-dimensional algebra (basis `1, g, x, gx`). Its two simple modules are the two
one-dimensional "sign" representations `S₊` (with `g = +1`, `x = 0`) and `S₋`
(with `g = -1`, `x = 0`); they are non-isomorphic. The algebra is **not** semisimple:
`x` is a nonzero nilpotent in the radical, and the two simples are linked by a genuine
nonsplit extension

  `0 → S₋ → P₊ → S₊ → 0`,

where `P₊ = ℂ²` carries `g = diag(1, -1)`, `x = [[0,0],[1,0]]`. This witnesses
`Ext¹(S₊, S₋) ≠ 0`, so `S₊` and `S₋` are `Etingof.AreLinked`: the algebra has a single
block. This is the content of Etingof Example 9.5.2 (iii), which until now was only a
TODO comment in `Chapter9/Example9_5_2.lean`.

The Ext nonvanishing is proved homologically rather than by hand: the covariant long
exact sequence of `Ext(S₊, -)` applied to the displayed short exact sequence shows that
the connecting class (the `extClass` of the sequence) is nonzero, because the sequence
has no section `S₊ → P₊` (any such section would force `x · (section 1) = 0`, while
the section condition forces its first coordinate to be `1`).
-/

universe u

open CategoryTheory

namespace Etingof.Problem932

/-! ## The algebra `A = ℂ⟨g, x⟩ / (gx + xg, x², g² - 1)` -/

/-- Generators of the free algebra: `0 ↦ g`, `1 ↦ x`. -/
abbrev Gen := Fin 2

/-- The `g` generator inside the free algebra. -/
noncomputable abbrev fg : FreeAlgebra ℂ Gen := FreeAlgebra.ι ℂ (0 : Fin 2)

/-- The `x` generator inside the free algebra. -/
noncomputable abbrev fx : FreeAlgebra ℂ Gen := FreeAlgebra.ι ℂ (1 : Fin 2)

/-- The defining relations of `A`: `gx + xg = 0`, `x² = 0`, `g² = 1`. -/
inductive Rel : FreeAlgebra ℂ Gen → FreeAlgebra ℂ Gen → Prop
  | anticomm : Rel (fg * fx + fx * fg) 0
  | xsq : Rel (fx * fx) 0
  | gsq : Rel (fg * fg) 1

/-- The algebra of Problem 9.3.2. -/
noncomputable abbrev A : Type := RingQuot Rel

/-- The canonical algebra map from the free algebra onto `A`. -/
noncomputable def mk : FreeAlgebra ℂ Gen →ₐ[ℂ] A := RingQuot.mkAlgHom ℂ Rel

/-- The image of `g` in `A`. -/
noncomputable def g : A := mk fg

/-- The image of `x` in `A`. -/
noncomputable def x : A := mk fx

@[simp] lemma anticomm_rel : g * x + x * g = 0 := by
  have h := RingQuot.mkAlgHom_rel ℂ Rel.anticomm
  simp only [map_add, map_mul, map_zero] at h
  exact h

@[simp] lemma xsq_rel : x * x = 0 := by
  have h := RingQuot.mkAlgHom_rel ℂ Rel.xsq
  simp only [map_mul, map_zero] at h
  exact h

@[simp] lemma gsq_rel : g * g = 1 := by
  have h := RingQuot.mkAlgHom_rel ℂ Rel.gsq
  simp only [map_mul, map_one] at h
  exact h

/-! ## Representations of `A`

A representation of `A` on a `ℂ`-vector space `V` is the same as a pair of endomorphisms
`G, X` satisfying the three defining relations. We package this via the universal property
of the free algebra and `RingQuot`. -/

section Rep

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The algebra map `A →ₐ[ℂ] Module.End ℂ V` determined by sending `g ↦ G`, `x ↦ X`,
given that `G, X` satisfy the defining relations of `A`. -/
noncomputable def repHom (G X : Module.End ℂ V)
    (hgx : G * X + X * G = 0) (hxx : X * X = 0) (hgg : G * G = 1) :
    A →ₐ[ℂ] Module.End ℂ V :=
  RingQuot.liftAlgHom ℂ ⟨FreeAlgebra.lift ℂ ![G, X], by
    intro a b r
    induction r with
    | anticomm =>
        simp only [map_add, map_mul, map_zero, FreeAlgebra.lift_ι_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact hgx
    | xsq =>
        simp only [map_mul, map_zero, FreeAlgebra.lift_ι_apply,
          Matrix.cons_val_one, Matrix.head_cons]
        exact hxx
    | gsq =>
        simp only [map_mul, map_one, FreeAlgebra.lift_ι_apply, Matrix.cons_val_zero]
        exact hgg⟩

@[simp] lemma repHom_g (G X : Module.End ℂ V)
    (hgx : G * X + X * G = 0) (hxx : X * X = 0) (hgg : G * G = 1) :
    repHom G X hgx hxx hgg g = G := by
  simp only [repHom, g, mk, RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
    Matrix.cons_val_zero]

@[simp] lemma repHom_x (G X : Module.End ℂ V)
    (hgx : G * X + X * G = 0) (hxx : X * X = 0) (hgg : G * G = 1) :
    repHom G X hgx hxx hgg x = X := by
  simp only [repHom, x, mk, RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
    Matrix.cons_val_one, Matrix.cons_val_zero]

/-- A `ℂ`-linear map intertwining the actions of the generators `g` and `x` automatically
intertwines the action of every element of `A`, because `g` and `x` generate `A`. -/
lemma intertwine_all {W : Type u} [AddCommGroup W] [Module ℂ W]
    (ρV : A →ₐ[ℂ] Module.End ℂ V) (ρW : A →ₐ[ℂ] Module.End ℂ W) (φ : V →ₗ[ℂ] W)
    (hg : ∀ v, φ (ρV g v) = ρW g (φ v)) (hx : ∀ v, φ (ρV x v) = ρW x (φ v)) :
    ∀ (a : A) (v : V), φ (ρV a v) = ρW a (φ v) := by
  intro a
  obtain ⟨w, rfl⟩ : ∃ w, mk w = a := RingQuot.mkAlgHom_surjective ℂ Rel a
  induction w with
  | grade0 r =>
      intro v
      have hV : ρV (mk (algebraMap ℂ (FreeAlgebra ℂ Gen) r))
          = algebraMap ℂ (Module.End ℂ V) r := by rw [mk.commutes, ρV.commutes]
      have hW : ρW (mk (algebraMap ℂ (FreeAlgebra ℂ Gen) r))
          = algebraMap ℂ (Module.End ℂ W) r := by rw [mk.commutes, ρW.commutes]
      rw [hV, hW, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | grade1 i =>
      intro v
      fin_cases i
      · exact hg v
      · exact hx v
  | mul a b ha hb =>
      intro v
      simp only [map_mul, Module.End.mul_apply] at *
      rw [ha, hb]
  | add a b ha hb =>
      intro v
      simp only [map_add, LinearMap.add_apply, map_add] at *
      rw [ha, hb]

/-- Promote a `ℂ`-linear map intertwining `g` and `x` to an `A`-linear map, for `A`-module
structures defined through representations `ρV`, `ρW`. -/
noncomputable def mkAlgLinear {W : Type u} [AddCommGroup W] [Module ℂ W]
    [Module A V] [Module A W]
    (ρV : A →ₐ[ℂ] Module.End ℂ V) (ρW : A →ₐ[ℂ] Module.End ℂ W)
    (hV : ∀ (a : A) (v : V), a • v = ρV a v) (hW : ∀ (a : A) (w : W), a • w = ρW a w)
    (φ : V →ₗ[ℂ] W) (hg : ∀ v, φ (ρV g v) = ρW g (φ v)) (hx : ∀ v, φ (ρV x v) = ρW x (φ v)) :
    V →ₗ[A] W where
  toFun := φ
  map_add' := φ.map_add
  map_smul' a v := by
    simp only [hV, hW, RingHom.id_apply, intertwine_all ρV ρW φ hg hx a v]

end Rep

/-! ## The two one-dimensional simple modules `S₊` and `S₋` -/

/-- Carrier of the sign representation `S₊`: a copy of `ℂ` on which `g` acts as `+1` and
`x` acts as `0`. -/
def Splus : Type := ℂ

instance : AddCommGroup Splus := inferInstanceAs (AddCommGroup ℂ)
instance : Module ℂ Splus := inferInstanceAs (Module ℂ ℂ)
instance : Nontrivial Splus := inferInstanceAs (Nontrivial ℂ)

/-- The representation defining `S₊`: `g ↦ 1`, `x ↦ 0`. -/
noncomputable def ρplus : A →ₐ[ℂ] Module.End ℂ Splus :=
  repHom (1 : Module.End ℂ Splus) 0 (by simp) (by simp) (by simp)

noncomputable instance : Module A Splus := Module.compHom Splus ρplus.toRingHom

lemma Splus.smul_def (a : A) (v : Splus) : a • v = ρplus a v := rfl

@[simp] lemma Splus.g_smul (v : Splus) : g • v = v := by
  simp only [Splus.smul_def, ρplus, repHom_g, Module.End.one_apply]

@[simp] lemma Splus.x_smul (v : Splus) : x • v = 0 := by
  simp only [Splus.smul_def, ρplus, repHom_x, LinearMap.zero_apply]

/-- Carrier of the sign representation `S₋`: a copy of `ℂ` on which `g` acts as `-1` and
`x` acts as `0`. -/
def Sminus : Type := ℂ

instance : AddCommGroup Sminus := inferInstanceAs (AddCommGroup ℂ)
instance : Module ℂ Sminus := inferInstanceAs (Module ℂ ℂ)
instance : Nontrivial Sminus := inferInstanceAs (Nontrivial ℂ)
instance : NoZeroSMulDivisors ℂ Sminus := inferInstanceAs (NoZeroSMulDivisors ℂ ℂ)

/-- The representation defining `S₋`: `g ↦ -1`, `x ↦ 0`. -/
noncomputable def ρminus : A →ₐ[ℂ] Module.End ℂ Sminus :=
  repHom (-1 : Module.End ℂ Sminus) 0 (by simp) (by simp) (by simp)

noncomputable instance : Module A Sminus := Module.compHom Sminus ρminus.toRingHom

lemma Sminus.smul_def (a : A) (v : Sminus) : a • v = ρminus a v := rfl

@[simp] lemma Sminus.g_smul (v : Sminus) : g • v = -v := by
  simp only [Sminus.smul_def, ρminus, repHom_g]
  simp

@[simp] lemma Sminus.x_smul (v : Sminus) : x • v = 0 := by
  simp only [Sminus.smul_def, ρminus, repHom_x, LinearMap.zero_apply]

/-! ### `S₊` and `S₋` are simple and non-isomorphic -/

instance : IsScalarTower ℂ A Splus :=
  ⟨fun c a v => by show ρplus (c • a) v = c • ρplus a v; rw [map_smul]; rfl⟩

instance : IsScalarTower ℂ A Sminus :=
  ⟨fun c a v => by show ρminus (c • a) v = c • ρminus a v; rw [map_smul]; rfl⟩

/-- `S₊` is a simple `A`-module: a one-dimensional `ℂ`-space has only the trivial
`ℂ`-subspaces, and every `A`-submodule is in particular a `ℂ`-subspace. -/
instance : IsSimpleModule A Splus := by
  have hsimp : IsSimpleModule ℂ Splus :=
    isSimpleModule_iff_finrank_eq_one.mpr (Module.finrank_self ℂ)
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun N => ?_ }
  rcases hsimp.eq_bot_or_eq_top (N.restrictScalars ℂ) with h | h
  · refine Or.inl (Submodule.restrictScalars_injective ℂ A Splus ?_)
    rw [h, Submodule.restrictScalars_bot]
  · refine Or.inr (Submodule.restrictScalars_injective ℂ A Splus ?_)
    rw [h, Submodule.restrictScalars_top]

/-- `S₋` is a simple `A`-module. -/
instance : IsSimpleModule A Sminus := by
  have hsimp : IsSimpleModule ℂ Sminus :=
    isSimpleModule_iff_finrank_eq_one.mpr (Module.finrank_self ℂ)
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun N => ?_ }
  rcases hsimp.eq_bot_or_eq_top (N.restrictScalars ℂ) with h | h
  · refine Or.inl (Submodule.restrictScalars_injective ℂ A Sminus ?_)
    rw [h, Submodule.restrictScalars_bot]
  · refine Or.inr (Submodule.restrictScalars_injective ℂ A Sminus ?_)
    rw [h, Submodule.restrictScalars_top]

/-- `S₊` and `S₋` are non-isomorphic: `g` acts as `+1` on `S₊` and as `-1` on `S₋`, so any
`A`-linear isomorphism would force `φ v = -φ v`, hence `φ = 0`. -/
theorem splus_not_iso_sminus : IsEmpty (Splus ≃ₗ[A] Sminus) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨a, ha⟩ := exists_ne (0 : Splus)
  have h1 : φ (g • a) = g • φ a := φ.map_smul g a
  rw [Splus.g_smul, Sminus.g_smul] at h1
  have h2 : (2 : ℂ) • φ a = 0 := by
    rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel _
  rcases smul_eq_zero.mp h2 with h | h
  · exact (two_ne_zero h).elim
  · exact ha (φ.injective (by rw [h, map_zero]))

/-! ## The projective indecomposable `P₊` and the nonsplit extension `0 → S₋ → P₊ → S₊ → 0` -/

/-- Carrier of `P₊`: `ℂ²`, on which `g = diag(1, -1)` and `x = [[0,0],[1,0]]`. -/
abbrev Pplus : Type := Fin 2 → ℂ

/-- The action of `g` on `P₊`, the diagonal matrix `diag(1, -1)`. -/
noncomputable def PG : Module.End ℂ Pplus := Matrix.toLinAlgEquiv' !![1, 0; 0, -1]

/-- The action of `x` on `P₊`, the nilpotent matrix `[[0,0],[1,0]]`. -/
noncomputable def PX : Module.End ℂ Pplus := Matrix.toLinAlgEquiv' !![0, 0; 1, 0]

lemma PG_apply (v : Pplus) : PG v = ![v 0, -v 1] := by
  funext i
  fin_cases i <;>
    simp [PG, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma PX_apply (v : Pplus) : PX v = ![0, v 0] := by
  funext i
  fin_cases i <;>
    simp [PX, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The representation defining `P₊`. -/
noncomputable def ρP : A →ₐ[ℂ] Module.End ℂ Pplus :=
  repHom PG PX
    (by simp only [PG, PX, ← map_mul, ← map_add]
        rw [show !![(1 : ℂ), 0; 0, -1] * !![0, 0; 1, 0] + !![0, 0; 1, 0] * !![1, 0; 0, -1]
              = (0 : Matrix (Fin 2) (Fin 2) ℂ) by
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [Matrix.mul_apply, Fin.sum_univ_two]]
        rw [map_zero])
    (by simp only [PX, ← map_mul]
        rw [show !![(0 : ℂ), 0; 1, 0] * !![0, 0; 1, 0] = (0 : Matrix (Fin 2) (Fin 2) ℂ) by
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [Matrix.mul_apply, Fin.sum_univ_two]]
        rw [map_zero])
    (by simp only [PG, ← map_mul]
        rw [show !![(1 : ℂ), 0; 0, -1] * !![1, 0; 0, -1] = (1 : Matrix (Fin 2) (Fin 2) ℂ) by
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]]
        rw [map_one])

noncomputable instance : Module A Pplus := Module.compHom Pplus ρP.toRingHom

lemma Pplus.smul_def (a : A) (v : Pplus) : a • v = ρP a v := rfl

@[simp] lemma Pplus.g_smul (v : Pplus) : g • v = ![v 0, -v 1] := by
  rw [Pplus.smul_def, ρP, repHom_g, PG_apply]

@[simp] lemma Pplus.x_smul (v : Pplus) : x • v = ![0, v 0] := by
  rw [Pplus.smul_def, ρP, repHom_x, PX_apply]

/-- The `ℂ`-linear inclusion of the socle of `P₊`: `c ↦ (0, c)`. -/
def φf : Sminus →ₗ[ℂ] Pplus where
  toFun c := ![0, c]
  map_add' a b := by funext j; fin_cases j <;> simp
  map_smul' r c := by funext j; fin_cases j <;> simp

/-- The `ℂ`-linear projection of `P₊` onto its top: `(a, b) ↦ a`. -/
def φg : Pplus →ₗ[ℂ] Splus := LinearMap.proj 0

@[simp] lemma φf_apply (c : Sminus) : φf c = ![0, c] := rfl

@[simp] lemma φg_apply (v : Pplus) : φg v = v 0 := rfl

/-- The socle inclusion `S₋ ↪ P₊` as an `A`-linear map. -/
noncomputable def fSES : Sminus →ₗ[A] Pplus :=
  mkAlgLinear ρminus ρP Sminus.smul_def Pplus.smul_def φf
    (by intro v
        rw [← Sminus.smul_def, ← Pplus.smul_def, Sminus.g_smul, Pplus.g_smul]
        simp only [φf_apply]
        funext j; fin_cases j <;> simp)
    (by intro v
        rw [← Sminus.smul_def, ← Pplus.smul_def, Sminus.x_smul, Pplus.x_smul]
        simp only [φf_apply]
        funext j; fin_cases j <;> simp)

/-- The top projection `P₊ ↠ S₊` as an `A`-linear map. -/
noncomputable def gSES : Pplus →ₗ[A] Splus :=
  mkAlgLinear ρP ρplus Pplus.smul_def Splus.smul_def φg
    (by intro v
        rw [← Pplus.smul_def, ← Splus.smul_def, Pplus.g_smul, Splus.g_smul]
        simp only [φg_apply, Matrix.cons_val_zero])
    (by intro v
        rw [← Pplus.smul_def, ← Splus.smul_def, Pplus.x_smul, Splus.x_smul]
        simp only [φg_apply, Matrix.cons_val_zero])

@[simp] lemma fSES_apply (c : Sminus) : fSES c = ![0, c] := φf_apply c

@[simp] lemma gSES_apply (v : Pplus) : gSES v = v 0 := rfl

lemma gSES_comp_fSES : gSES.comp fSES = 0 := by
  ext c; simp [fSES_apply]

/-- Exactness `ker gSES = range fSES` at the middle term. -/
lemma fSES_gSES_exact : Function.Exact fSES gSES := by
  rw [LinearMap.exact_iff]
  ext v
  simp only [LinearMap.mem_ker, gSES_apply, LinearMap.mem_range]
  constructor
  · intro hv
    exact ⟨v 1, by funext j; fin_cases j <;> simp [fSES_apply, hv]⟩
  · rintro ⟨c, rfl⟩
    simp [fSES_apply]

lemma fSES_injective : Function.Injective fSES := by
  intro a b hab
  have := congrFun hab 1
  simpa [fSES_apply] using this

lemma gSES_surjective : Function.Surjective gSES := fun s => ⟨![s, 0], rfl⟩

/-- The short exact sequence `0 → S₋ → P₊ → S₊ → 0` of `A`-modules. -/
noncomputable def ses : ShortComplex (ModuleCat.{0} A) :=
  ModuleCat.shortComplexOfCompEqZero fSES gSES gSES_comp_fSES

lemma ses_shortExact : ses.ShortExact :=
  ModuleCat.shortComplex_shortExact ses fSES_gSES_exact fSES_injective gSES_surjective

/-! ## `Ext¹(S₊, S₋) ≠ 0`: the extension does not split -/

/-- The extension `0 → S₋ → P₊ → S₊ → 0` does not split: its `Ext`-class is nonzero.
A section `S₊ → P₊` of `g` would send the generator to a vector with first coordinate `1`
(the section condition) but with `x`-image zero forcing that coordinate to be `0`. -/
theorem extClass_ne_zero : ses_shortExact.extClass ≠ 0 := by
  intro heq
  -- The covariant LES of `Ext(S₊, -)`: if the class vanishes, the identity of `S₊` lifts
  -- through `g`, i.e. `g` has a section.
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ ses.X₃ ses_shortExact
    (Abelian.Ext.mk₀ (𝟙 ses.X₃)) (n₁ := 1) rfl (by rw [heq, Abelian.Ext.comp_zero])
  obtain ⟨h, rfl⟩ := (Abelian.Ext.mk₀_bijective ses.X₃ ses.X₂).surjective x₂
  rw [Abelian.Ext.mk₀_comp_mk₀] at hx₂
  have hsec : h ≫ ses.g = 𝟙 ses.X₃ := (Abelian.Ext.mk₀_bijective _ _).injective hx₂
  -- A section forces every element of `S₊` to vanish, contradicting nontriviality.
  have allzero : ∀ s : Splus, s = 0 := by
    intro s
    have key : gSES (h.hom s) = s := by
      have h2 := congrArg (fun φ : ses.X₃ ⟶ ses.X₃ => φ.hom s) hsec
      simpa [ses, ModuleCat.shortComplexOfCompEqZero, ModuleCat.hom_comp,
        ModuleCat.hom_id, ModuleCat.hom_ofHom] using h2
    -- `A`-linearity of `h`: `h (x · s) = x · h s`, and `x · s = 0`, forcing `(h s) 0 = 0`.
    have hx1 : h.hom (x • s) = x • h.hom s := h.hom.map_smul x s
    rw [Splus.x_smul, map_zero, Pplus.x_smul] at hx1
    have hzero : (h.hom s) 0 = 0 := by
      have h3 := congrFun hx1 1
      simp only [Matrix.cons_val_one, Matrix.head_cons] at h3
      exact h3.symm
    rw [gSES_apply, hzero] at key
    exact key.symm
  obtain ⟨a, b, hab⟩ := exists_pair_ne Splus
  exact hab (by rw [allzero a, allzero b])

/-- `S₊` and `S₋` are directly `Ext¹`-linked: `Ext¹(S₊, S₋) ≠ 0`. -/
theorem directlyExtLinked :
    Etingof.DirectlyExtLinked A (ModuleCat.of A Splus) (ModuleCat.of A Sminus) :=
  nontrivial_of_ne _ _ extClass_ne_zero

/-- **The algebra of Problem 9.3.2 has a single block.** Its two simple modules `S₊` and
`S₋` are `Etingof.AreLinked`, via the nonsplit extension `0 → S₋ → P₊ → S₊ → 0`.
This is Etingof Example 9.5.2 (iii). -/
theorem areLinked :
    Etingof.AreLinked A (ModuleCat.of A Splus) (ModuleCat.of A Sminus) :=
  Relation.EqvGen.rel _ _ (Or.inl (Or.inl directlyExtLinked))

end Etingof.Problem932

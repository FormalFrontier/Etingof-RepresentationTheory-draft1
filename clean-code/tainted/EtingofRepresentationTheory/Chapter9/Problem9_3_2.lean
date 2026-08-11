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
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Algebra.Bilinear
import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import EtingofRepresentationTheory.Chapter9.Definition9_3_1
import EtingofRepresentationTheory.Chapter9.Definition9_5_1
import EtingofRepresentationTheory.Chapter9.Theorem9_2_1

set_option backward.isDefEq.respectTransparency false

/-!
# Problem 9.3.2: a four-dimensional algebra with a single block

Etingof's Problem 9.3.2 asks to study the `ℂ`-algebra

  `A = ℂ⟨g, x⟩ / (gx + xg, x², g² - 1)`,

a four-dimensional algebra (basis `1, g, x, gx`). Its two simple modules are the two
one-dimensional "sign" representations `S₊` (with `g = +1`, `x = 0`) and `S₋`
(with `g = -1`, `x = 0`); they are non-isomorphic. The algebra is not semisimple:
`x` is a nonzero nilpotent in the radical, and the two simples are linked by a
nonsplit extension

  `0 → S₋ → P₊ → S₊ → 0`,

where `P₊ = ℂ²` carries `g = diag(1, -1)`, `x = [[0,0],[1,0]]`. This witnesses
`Ext¹(S₊, S₋) ≠ 0`, so `S₊` and `S₋` are `Etingof.AreLinked`: the algebra has a single
block. This is the content of Etingof Example 9.5.2 (iii).

The Ext nonvanishing is proved homologically rather than by hand: the covariant long
exact sequence of `Ext(S₊, -)` applied to the displayed short exact sequence shows that
the connecting class (the `extClass` of the sequence) is nonzero, because the sequence
has no section `S₊ → P₊` (any such section would force `x · (section 1) = 0`, while
the section condition forces its first coordinate to be `1`).
-/

universe u v

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
          Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hgx
    | xsq =>
        simp only [map_mul, map_zero, FreeAlgebra.lift_ι_apply,
          Matrix.cons_val_one]
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
lemma intertwine_all {W : Type v} [AddCommGroup W] [Module ℂ W]
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
noncomputable def mkAlgLinear {W : Type v} [AddCommGroup W] [Module ℂ W]
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

/-- Scalars from `ℂ` act on an `A`-module through `A`, so `A`-submodules are `ℂ`-stable. -/
lemma smul_mem_complex {M : Type u} [AddCommGroup M] [Module ℂ M] [Module A M]
    [IsScalarTower ℂ A M] (N : Submodule A M) (c : ℂ) {v : M} (hv : v ∈ N) : c • v ∈ N := by
  have h := N.smul_mem (algebraMap ℂ A c) hv
  rwa [algebraMap_smul] at h

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
  ⟨fun c a v => by change ρplus (c • a) v = c • ρplus a v; rw [map_smul]; rfl⟩

instance : IsScalarTower ℂ A Sminus :=
  ⟨fun c a v => by change ρminus (c • a) v = c • ρminus a v; rw [map_smul]; rfl⟩

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

/-- Carrier of `P₊`: `ℂ²`, on which `g = diag(1, -1)` and `x = [[0,0],[1,0]]`.

This is a `def` rather than an `abbrev` on purpose. `P₊` and `P₋` have the *same* underlying
vector space `ℂ²` but carry *different* `A`-actions, so their carriers must be distinct types
for the two `Module A` instances to coexist: with reducible `abbrev`s, instance resolution sees
one type `Fin 2 → ℂ` with two `Module A` instances and silently picks whichever was declared
last. Distinct carriers are what makes the indexed family `Pfam` of the two projectives — and
hence the Cartan matrix of Definition 9.3.1 — expressible at all. -/
def Pplus : Type := Fin 2 → ℂ

namespace Pplus

instance : AddCommGroup Pplus := inferInstanceAs (AddCommGroup (Fin 2 → ℂ))
instance : Module ℂ Pplus := inferInstanceAs (Module ℂ (Fin 2 → ℂ))
instance : Nontrivial Pplus := inferInstanceAs (Nontrivial (Fin 2 → ℂ))
instance : Module.Finite ℂ Pplus := inferInstanceAs (Module.Finite ℂ (Fin 2 → ℂ))

/-! ### Coordinate API for `P₊`

Because `Pplus` is a semireducible `def`, Mathlib's `Pi.*_apply` simp lemmas no longer fire on
`P₊`-valued expressions (simp matches up to reducible transparency). These `rfl` lemmas restore
the pointwise calculus. -/

@[ext] lemma ext {u v : Pplus} (h : ∀ i, u i = v i) : u = v := funext h

@[simp] lemma add_apply (u v : Pplus) (i : Fin 2) : (u + v) i = u i + v i := rfl
@[simp] lemma sub_apply (u v : Pplus) (i : Fin 2) : (u - v) i = u i - v i := rfl
@[simp] lemma neg_apply (v : Pplus) (i : Fin 2) : (-v) i = -v i := rfl
@[simp] lemma zero_apply (i : Fin 2) : (0 : Pplus) i = 0 := rfl
@[simp] lemma complex_smul_apply (c : ℂ) (v : Pplus) (i : Fin 2) : (c • v) i = c * v i := rfl

/-- The generator `e₀ = (1, 0)` of `P₊`. It generates `P₊` over `A` (its `x`-image is `e₁`)
and lifts the generator of the top `S₊`. -/
def e0 : Pplus := ![1, 0]

/-- The socle vector `e₁ = (0, 1)` of `P₊`, spanning the copy of `S₋` inside `P₊`. -/
def e1 : Pplus := ![0, 1]

@[simp] lemma e0_zero : e0 0 = 1 := rfl
@[simp] lemma e0_one : e0 1 = 0 := rfl
@[simp] lemma e1_zero : e1 0 = 0 := rfl
@[simp] lemma e1_one : e1 1 = 1 := rfl

/-- Coordinate expansion of a vector of `P₊` in the basis `e₀, e₁`. -/
lemma eq_smul_e0_add_smul_e1 (v : Pplus) : v = v 0 • e0 + v 1 • e1 := by
  refine ext fun i => ?_
  fin_cases i <;> simp

end Pplus

/-- The action of `g` on `P₊`, the diagonal matrix `diag(1, -1)`. -/
def PG : Module.End ℂ Pplus where
  toFun v := ![v 0, -v 1]
  map_add' u v := by refine Pplus.ext fun i => ?_; fin_cases i <;> simp ; ring
  map_smul' c v := by refine Pplus.ext fun i => ?_; fin_cases i <;> simp [mul_neg]

/-- The action of `x` on `P₊`, the nilpotent matrix `[[0,0],[1,0]]`. -/
def PX : Module.End ℂ Pplus where
  toFun v := ![0, v 0]
  map_add' u v := by refine Pplus.ext fun i => ?_; fin_cases i <;> simp
  map_smul' c v := by refine Pplus.ext fun i => ?_; fin_cases i <;> simp

lemma PG_apply (v : Pplus) : PG v = ![v 0, -v 1] := rfl

lemma PX_apply (v : Pplus) : PX v = ![0, v 0] := rfl

/-- `PG` is the action of the matrix `diag(1, -1)` of the book's presentation. -/
lemma PG_eq_mulVec (v : Pplus) :
    PG v = Matrix.mulVec !![(1 : ℂ), 0; 0, -1] (v : Fin 2 → ℂ) := by
  refine Pplus.ext fun i => ?_
  fin_cases i <;> simp [PG_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `PX` is the action of the nilpotent matrix `[[0,0],[1,0]]` of the book's presentation. -/
lemma PX_eq_mulVec (v : Pplus) :
    PX v = Matrix.mulVec !![(0 : ℂ), 0; 1, 0] (v : Fin 2 → ℂ) := by
  refine Pplus.ext fun i => ?_
  fin_cases i <;> simp [PX_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The representation defining `P₊`. -/
noncomputable def ρP : A →ₐ[ℂ] Module.End ℂ Pplus :=
  repHom PG PX
    (by refine LinearMap.ext fun v => ?_
        simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
        refine Pplus.ext fun i => ?_
        fin_cases i <;> simp [PG_apply, PX_apply])
    (by refine LinearMap.ext fun v => ?_
        simp only [Module.End.mul_apply, LinearMap.zero_apply]
        refine Pplus.ext fun i => ?_
        fin_cases i <;> simp [PX_apply])
    (by refine LinearMap.ext fun v => ?_
        simp only [Module.End.mul_apply, Module.End.one_apply]
        refine Pplus.ext fun i => ?_
        fin_cases i <;> simp [PG_apply])

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
      simp only [Matrix.cons_val_one] at h3
      exact h3.symm
    rw [gSES_apply, hzero] at key
    exact key.symm
  obtain ⟨a, b, hab⟩ := exists_pair_ne Splus
  exact hab (by rw [allzero a, allzero b])

/-! ## `P₊` is projective

`A ≅ A·e₊ ⊕ A·e₋` as a left module for the idempotent `e₊ = (1 + g)/2`, and
`P₊ ≅ A·e₊`. Concretely: the `A`-linear surjection `A ↠ P₊`, `a ↦ a • (1,0)`, is split by
the `A`-linear section `(a, b) ↦ a • e₊ + b • (x·e₊)`, exhibiting `P₊` as a direct summand
of the free module `A`. Hence `P₊` is projective. -/

instance : IsScalarTower ℂ A Pplus :=
  ⟨fun c a v => by change ρP (c • a) v = c • ρP a v; rw [map_smul]; rfl⟩

/-- The idempotent `e₊ = (1 + g)/2 ∈ A` (a generator of the summand `A·e₊ ≅ P₊`). -/
noncomputable def eplus : A := (2⁻¹ : ℂ) • (1 + g)

/-- The socle generator `x·e₊ = (x - g·x)/2 ∈ A` of the summand `A·e₊ ≅ P₊`. -/
noncomputable def xeplus : A := (2⁻¹ : ℂ) • (x - g * x)

lemma g_mul_eplus : g * eplus = eplus := by
  rw [eplus, mul_smul_comm]
  congr 1
  rw [mul_add, mul_one, gsq_rel]
  exact add_comm g 1

lemma x_mul_eplus : x * eplus = xeplus := by
  rw [eplus, xeplus, mul_smul_comm]
  congr 1
  rw [mul_add, mul_one]
  have hxg : x * g = -(g * x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact anticomm_rel
  rw [hxg, ← sub_eq_add_neg]

lemma g_mul_xeplus : g * xeplus = -xeplus := by
  rw [xeplus, mul_smul_comm]
  have hinner : g * (x - g * x) = -(x - g * x) := by
    rw [mul_sub, ← mul_assoc, gsq_rel, one_mul, neg_sub]
  exact (congrArg ((2⁻¹ : ℂ) • ·) hinner).trans (smul_neg _ _)

lemma x_mul_xeplus : x * xeplus = 0 := by
  have h : x * (x - g * x) = 0 := by
    have hxg : x * g = -(g * x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact anticomm_rel
    calc
      x * (x - g * x) = x * x - x * (g * x) := mul_sub _ _ _
      _ = x * x - (x * g) * x := by rw [← mul_assoc]
      _ = 0 - (-(g * x)) * x := by rw [xsq_rel, hxg]
      _ = 0 - -((g * x) * x) := congrArg (0 - ·) (neg_mul (g * x) x)
      _ = 0 := by rw [mul_assoc, xsq_rel, mul_zero, neg_zero, sub_zero]
  rw [xeplus, mul_smul_comm, h, smul_zero]

lemma eplus_smul_e0 : eplus • Pplus.e0 = Pplus.e0 := by
  have h : eplus • Pplus.e0
      = (2⁻¹ : ℂ) • (Pplus.e0 + g • Pplus.e0) := by
    rw [eplus, smul_assoc, add_smul, one_smul]
  rw [h, Pplus.g_smul]
  refine Pplus.ext fun i => ?_
  fin_cases i <;> simp ; norm_num

lemma xeplus_smul_e0 : xeplus • Pplus.e0 = Pplus.e1 := by
  rw [← x_mul_eplus, mul_smul, eplus_smul_e0, Pplus.x_smul]
  refine Pplus.ext fun i => ?_
  fin_cases i <;> simp

/-- The `ℂ`-linear map `P₊ → A`, `(a, b) ↦ a • e₊ + b • (x·e₊)`, underlying the section. -/
noncomputable def φiPlus : Pplus →ₗ[ℂ] A where
  toFun v := v 0 • eplus + v 1 • xeplus
  map_add' u v := by
    simp only [Pplus.add_apply, add_smul]; abel
  map_smul' c v := by
    simp only [Pplus.complex_smul_apply, RingHom.id_apply, mul_smul, smul_add]

@[simp] lemma φiPlus_apply (v : Pplus) : φiPlus v = v 0 • eplus + v 1 • xeplus := rfl

/-- The `A`-linear section `P₊ → A` of the retraction `a ↦ a • (1,0)`, landing in `A·e₊`. -/
noncomputable def iPlus : Pplus →ₗ[A] A :=
  mkAlgLinear ρP (Algebra.lmul ℂ A) Pplus.smul_def (fun a b => by
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', smul_eq_mul])
    φiPlus
    (by intro v
        rw [← Pplus.smul_def, Pplus.g_smul]
        simp only [φiPlus_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', neg_smul]
        rw [mul_add, mul_smul_comm, mul_smul_comm, g_mul_eplus, g_mul_xeplus]
        module)
    (by intro v
        rw [← Pplus.smul_def, Pplus.x_smul]
        simp only [φiPlus_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          zero_smul, zero_add, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
        rw [mul_add, mul_smul_comm, mul_smul_comm, x_mul_eplus, x_mul_xeplus, smul_zero, add_zero])

/-- The `A`-linear retraction `A ↠ P₊`, `a ↦ a • (1,0)`. -/
noncomputable def rPlus : A →ₗ[A] Pplus := LinearMap.toSpanSingleton A Pplus Pplus.e0

/-- The retraction is split by the section: `rPlus ∘ iPlus = id`, so `P₊` is a summand of `A`. -/
lemma rPlus_comp_iPlus : rPlus.comp iPlus = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  change rPlus (iPlus v) = v
  have hiv : iPlus v = v 0 • eplus + v 1 • xeplus := rfl
  rw [rPlus, LinearMap.toSpanSingleton_apply, hiv, add_smul, smul_assoc, smul_assoc,
    eplus_smul_e0, xeplus_smul_e0]
  funext i; fin_cases i <;> simp

/-- **`P₊` is a projective `A`-module.** It is a direct summand of the free module `A`. -/
instance projective_Pplus : Module.Projective A Pplus :=
  Module.Projective.of_split iPlus rPlus rPlus_comp_iPlus


/-! ### `P₊` is indecomposable and is a projective cover of `S₊`

The submodule lattice of `P₊` is the chain `0 ⊂ ℂ·(0,1) ⊂ P₊`: any nonzero submodule contains
the socle vector `(0,1)`, and any submodule containing a vector with nonzero first coordinate is
everything. Both facts follow from `x · (a, b) = (0, a)`. -/

/-- Every nonzero `A`-submodule of `P₊` contains the socle vector `(0, 1)`. -/
lemma socle_mem_of_ne_bot_Pplus (N : Submodule A Pplus) (hN : N ≠ ⊥) :
    Pplus.e1 ∈ N := by
  obtain ⟨v, hvN, hv⟩ := (Submodule.ne_bot_iff N).mp hN
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      exact hv (Pplus.ext fun j => by fin_cases j <;> simp [h0, h1])
    have hmem := smul_mem_complex N (v 1)⁻¹ hvN
    have heq : (v 1)⁻¹ • v = Pplus.e1 := by
      refine Pplus.ext fun j => ?_
      fin_cases j <;> simp [h0, inv_mul_cancel₀ h1]
    rwa [heq] at hmem
  · have hx : x • v ∈ N := N.smul_mem x hvN
    have hmem := smul_mem_complex N (v 0)⁻¹ hx
    have heq : (v 0)⁻¹ • (x • v) = Pplus.e1 := by
      rw [Pplus.x_smul]
      refine Pplus.ext fun j => ?_
      fin_cases j <;> simp [inv_mul_cancel₀ h0]
    rwa [heq] at hmem

/-- An `A`-submodule of `P₊` containing a vector with nonzero first coordinate is all of `P₊`. -/
lemma eq_top_of_mem_Pplus (N : Submodule A Pplus) {v : Pplus} (hvN : v ∈ N) (h0 : v 0 ≠ 0) :
    N = ⊤ := by
  have hsoc : Pplus.e1 ∈ N :=
    socle_mem_of_ne_bot_Pplus N (Submodule.ne_bot_iff N |>.mpr
      ⟨v, hvN, fun h => h0 (by rw [h]; rfl)⟩)
  have he0 : Pplus.e0 ∈ N := by
    have hsub : v - v 1 • Pplus.e1 ∈ N :=
      N.sub_mem hvN (smul_mem_complex N (v 1) hsoc)
    have hmem := smul_mem_complex N (v 0)⁻¹ hsub
    have heq : (v 0)⁻¹ • (v - v 1 • Pplus.e1) = Pplus.e0 := by
      refine Pplus.ext fun j => ?_
      fin_cases j <;> simp [inv_mul_cancel₀ h0]
    rwa [heq] at hmem
  refine Submodule.eq_top_iff'.mpr fun w => ?_
  rw [Pplus.eq_smul_e0_add_smul_e1 w]
  exact N.add_mem (smul_mem_complex N _ he0) (smul_mem_complex N _ hsoc)

/-- **`P₊` is indecomposable.** Every nonzero submodule contains the socle vector `(0, 1)`, so
two nonzero submodules can never be disjoint. -/
theorem isIndecomposable_Pplus : Etingof.IsIndecomposable A Pplus := by
  refine ⟨inferInstance, fun M N hMN => ?_⟩
  by_contra hc
  obtain ⟨hM, hN⟩ := not_or.mp hc
  have hmem : Pplus.e1 ∈ M ⊓ N :=
    ⟨socle_mem_of_ne_bot_Pplus M hM, socle_mem_of_ne_bot_Pplus N hN⟩
  rw [hMN.inf_eq_bot, Submodule.mem_bot] at hmem
  have hone : Pplus.e1 1 = (0 : Pplus) 1 := by rw [hmem]
  simp at hone

/-- The kernel of `P₊ ↠ S₊` is superfluous: no proper submodule of `P₊` complements it. -/
theorem ker_gSES_superfluous (N : Submodule A Pplus)
    (h : N ⊔ LinearMap.ker gSES = ⊤) : N = ⊤ := by
  have hmem : Pplus.e0 ∈ N ⊔ LinearMap.ker gSES := h ▸ Submodule.mem_top
  obtain ⟨n, hn, k, hk, hnk⟩ := Submodule.mem_sup.mp hmem
  have hk0 : k 0 = 0 := hk
  refine eq_top_of_mem_Pplus N hn ?_
  have hsum : n 0 + k 0 = (1 : ℂ) := by
    have := congrArg (fun w : Pplus => w 0) hnk
    simpa using this
  rw [hk0, add_zero] at hsum
  rw [hsum]
  exact one_ne_zero

/-- **`P₊ ↠ S₊` is a projective cover of `S₊`.** `P₊` is projective, the map is surjective, and
its kernel `S₋` is superfluous in `P₊`. -/
theorem isProjectiveCover_Pplus :
    Module.Projective A Pplus ∧ Function.Surjective gSES ∧
      ∀ N : Submodule A Pplus, N ⊔ LinearMap.ker gSES = ⊤ → N = ⊤ :=
  ⟨projective_Pplus, gSES_surjective, ker_gSES_superfluous⟩

/-! ## The mirror projective `P₋` and the mirror extension `0 → S₊ → P₋ → S₋ → 0`

`P₋` is the second projective indecomposable: `ℂ²` with `g = diag(-1, 1)` and
`x = [[0,0],[1,0]]`. Its top is `S₋` and its socle is `S₊`, giving the mirror short exact
sequence `0 → S₊ → P₋ → S₋ → 0`. Together with `0 → S₋ → P₊ → S₊ → 0` this exhibits the
2-periodic syzygies `Ω(S₊) ≅ S₋`, `Ω(S₋) ≅ S₊` used in Problem 9.4.5(ii). -/

/-- Carrier of `P₋`: `ℂ²`, on which `g = diag(-1, 1)` and `x = [[0,0],[1,0]]`.

A `def`, not an `abbrev`, for the same reason as `Pplus`: the two projectives share the
underlying space `ℂ²` and must be distinct types so that their `Module A` instances coexist. -/
def Pminus : Type := Fin 2 → ℂ

namespace Pminus

instance : AddCommGroup Pminus := inferInstanceAs (AddCommGroup (Fin 2 → ℂ))
instance : Module ℂ Pminus := inferInstanceAs (Module ℂ (Fin 2 → ℂ))
instance : Nontrivial Pminus := inferInstanceAs (Nontrivial (Fin 2 → ℂ))
instance : Module.Finite ℂ Pminus := inferInstanceAs (Module.Finite ℂ (Fin 2 → ℂ))

/-! ### Coordinate API for `P₋` (see the `Pplus` coordinate API for why these are needed) -/

@[ext] lemma ext {u v : Pminus} (h : ∀ i, u i = v i) : u = v := funext h

@[simp] lemma add_apply (u v : Pminus) (i : Fin 2) : (u + v) i = u i + v i := rfl
@[simp] lemma sub_apply (u v : Pminus) (i : Fin 2) : (u - v) i = u i - v i := rfl
@[simp] lemma neg_apply (v : Pminus) (i : Fin 2) : (-v) i = -v i := rfl
@[simp] lemma zero_apply (i : Fin 2) : (0 : Pminus) i = 0 := rfl
@[simp] lemma complex_smul_apply (c : ℂ) (v : Pminus) (i : Fin 2) : (c • v) i = c * v i := rfl

/-- The generator `e₀ = (1, 0)` of `P₋`, lifting the generator of the top `S₋`. -/
def e0 : Pminus := ![1, 0]

/-- The socle vector `e₁ = (0, 1)` of `P₋`, spanning the copy of `S₊` inside `P₋`. -/
def e1 : Pminus := ![0, 1]

@[simp] lemma e0_zero : e0 0 = 1 := rfl
@[simp] lemma e0_one : e0 1 = 0 := rfl
@[simp] lemma e1_zero : e1 0 = 0 := rfl
@[simp] lemma e1_one : e1 1 = 1 := rfl

/-- Coordinate expansion of a vector of `P₋` in the basis `e₀, e₁`. -/
lemma eq_smul_e0_add_smul_e1 (v : Pminus) : v = v 0 • e0 + v 1 • e1 := by
  refine ext fun i => ?_
  fin_cases i <;> simp

end Pminus

/-- The action of `g` on `P₋`, the diagonal matrix `diag(-1, 1)`. -/
def PGm : Module.End ℂ Pminus where
  toFun v := ![-v 0, v 1]
  map_add' u v := by refine Pminus.ext fun i => ?_; fin_cases i <;> simp ; ring
  map_smul' c v := by refine Pminus.ext fun i => ?_; fin_cases i <;> simp [mul_neg]

/-- The action of `x` on `P₋`, the nilpotent matrix `[[0,0],[1,0]]`. -/
def PXm : Module.End ℂ Pminus where
  toFun v := ![0, v 0]
  map_add' u v := by refine Pminus.ext fun i => ?_; fin_cases i <;> simp
  map_smul' c v := by refine Pminus.ext fun i => ?_; fin_cases i <;> simp

lemma PGm_apply (v : Pminus) : PGm v = ![-v 0, v 1] := rfl

lemma PXm_apply (v : Pminus) : PXm v = ![0, v 0] := rfl

/-- `PGm` is the action of the matrix `diag(-1, 1)` of the book's presentation. -/
lemma PGm_eq_mulVec (v : Pminus) :
    PGm v = Matrix.mulVec !![(-1 : ℂ), 0; 0, 1] (v : Fin 2 → ℂ) := by
  refine Pminus.ext fun i => ?_
  fin_cases i <;> simp [PGm_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `PXm` is the action of the nilpotent matrix `[[0,0],[1,0]]` of the book's presentation. -/
lemma PXm_eq_mulVec (v : Pminus) :
    PXm v = Matrix.mulVec !![(0 : ℂ), 0; 1, 0] (v : Fin 2 → ℂ) := by
  refine Pminus.ext fun i => ?_
  fin_cases i <;> simp [PXm_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The representation defining `P₋`. -/
noncomputable def ρPm : A →ₐ[ℂ] Module.End ℂ Pminus :=
  repHom PGm PXm
    (by refine LinearMap.ext fun v => ?_
        simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
        refine Pminus.ext fun i => ?_
        fin_cases i <;> simp [PGm_apply, PXm_apply])
    (by refine LinearMap.ext fun v => ?_
        simp only [Module.End.mul_apply, LinearMap.zero_apply]
        refine Pminus.ext fun i => ?_
        fin_cases i <;> simp [PXm_apply])
    (by refine LinearMap.ext fun v => ?_
        simp only [Module.End.mul_apply, Module.End.one_apply]
        refine Pminus.ext fun i => ?_
        fin_cases i <;> simp [PGm_apply])

noncomputable instance : Module A Pminus := Module.compHom Pminus ρPm.toRingHom

lemma Pminus.smul_def (a : A) (v : Pminus) : a • v = ρPm a v := rfl

@[simp] lemma Pminus.g_smul (v : Pminus) : g • v = ![-v 0, v 1] := by
  rw [Pminus.smul_def, ρPm, repHom_g, PGm_apply]

@[simp] lemma Pminus.x_smul (v : Pminus) : x • v = ![0, v 0] := by
  rw [Pminus.smul_def, ρPm, repHom_x, PXm_apply]

instance : IsScalarTower ℂ A Pminus :=
  ⟨fun c a v => by change ρPm (c • a) v = c • ρPm a v; rw [map_smul]; rfl⟩

/-- The `ℂ`-linear inclusion of the socle of `P₋`: `c ↦ (0, c)`. -/
def φfm : Splus →ₗ[ℂ] Pminus where
  toFun c := ![0, c]
  map_add' a b := by funext j; fin_cases j <;> simp
  map_smul' r c := by funext j; fin_cases j <;> simp

/-- The `ℂ`-linear projection of `P₋` onto its top: `(a, b) ↦ a`. -/
def φgm : Pminus →ₗ[ℂ] Sminus := LinearMap.proj 0

@[simp] lemma φfm_apply (c : Splus) : φfm c = ![0, c] := rfl

@[simp] lemma φgm_apply (v : Pminus) : φgm v = v 0 := rfl

/-- The socle inclusion `S₊ ↪ P₋` as an `A`-linear map. -/
noncomputable def fSESm : Splus →ₗ[A] Pminus :=
  mkAlgLinear ρplus ρPm Splus.smul_def Pminus.smul_def φfm
    (by intro v
        rw [← Splus.smul_def, ← Pminus.smul_def, Splus.g_smul, Pminus.g_smul]
        simp only [φfm_apply]
        funext j; fin_cases j <;> simp)
    (by intro v
        rw [← Splus.smul_def, ← Pminus.smul_def, Splus.x_smul, Pminus.x_smul]
        simp only [φfm_apply]
        funext j; fin_cases j <;> simp)

/-- The top projection `P₋ ↠ S₋` as an `A`-linear map. -/
noncomputable def gSESm : Pminus →ₗ[A] Sminus :=
  mkAlgLinear ρPm ρminus Pminus.smul_def Sminus.smul_def φgm
    (by intro v
        rw [← Pminus.smul_def, ← Sminus.smul_def, Pminus.g_smul, Sminus.g_smul]
        simp only [φgm_apply, Matrix.cons_val_zero])
    (by intro v
        rw [← Pminus.smul_def, ← Sminus.smul_def, Pminus.x_smul, Sminus.x_smul]
        simp only [φgm_apply, Matrix.cons_val_zero])

@[simp] lemma fSESm_apply (c : Splus) : fSESm c = ![0, c] := φfm_apply c

@[simp] lemma gSESm_apply (v : Pminus) : gSESm v = v 0 := rfl

lemma gSESm_comp_fSESm : gSESm.comp fSESm = 0 := by
  ext c; simp [fSESm_apply]

/-- Exactness `ker gSESm = range fSESm` at the middle term. -/
lemma fSESm_gSESm_exact : Function.Exact fSESm gSESm := by
  rw [LinearMap.exact_iff]
  ext v
  simp only [LinearMap.mem_ker, gSESm_apply, LinearMap.mem_range]
  constructor
  · intro hv
    exact ⟨v 1, by funext j; fin_cases j <;> simp [fSESm_apply, hv]⟩
  · rintro ⟨c, rfl⟩
    simp [fSESm_apply]

lemma fSESm_injective : Function.Injective fSESm := by
  intro a b hab
  have := congrFun hab 1
  simpa [fSESm_apply] using this

lemma gSESm_surjective : Function.Surjective gSESm := fun s => ⟨![s, 0], rfl⟩

/-- The mirror short exact sequence `0 → S₊ → P₋ → S₋ → 0` of `A`-modules. -/
noncomputable def sesm : ShortComplex (ModuleCat.{0} A) :=
  ModuleCat.shortComplexOfCompEqZero fSESm gSESm gSESm_comp_fSESm

lemma sesm_shortExact : sesm.ShortExact :=
  ModuleCat.shortComplex_shortExact sesm fSESm_gSESm_exact fSESm_injective gSESm_surjective

/-! ### `P₋` is projective -/

/-- The idempotent `e₋ = (1 - g)/2 ∈ A` (a generator of the summand `A·e₋ ≅ P₋`). -/
noncomputable def eminus : A := (2⁻¹ : ℂ) • (1 - g)

/-- The socle generator `x·e₋ = (x + g·x)/2 ∈ A` of the summand `A·e₋ ≅ P₋`. -/
noncomputable def xeminus : A := (2⁻¹ : ℂ) • (x + g * x)

lemma g_mul_eminus : g * eminus = -eminus := by
  rw [eminus, mul_smul_comm]
  have hinner : g * (1 - g) = -(1 - g) := by
    rw [mul_sub, mul_one, gsq_rel, neg_sub]
  exact (congrArg ((2⁻¹ : ℂ) • ·) hinner).trans (smul_neg _ _)

lemma x_mul_eminus : x * eminus = xeminus := by
  rw [eminus, xeminus, mul_smul_comm]
  congr 1
  rw [mul_sub, mul_one]
  have hxg : x * g = -(g * x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact anticomm_rel
  rw [hxg, sub_neg_eq_add]

lemma g_mul_xeminus : g * xeminus = xeminus := by
  rw [xeminus, mul_smul_comm]
  congr 1
  rw [mul_add, ← mul_assoc, gsq_rel, one_mul, add_comm]

lemma x_mul_xeminus : x * xeminus = 0 := by
  have h : x * (x + g * x) = 0 := by
    have hxg : x * g = -(g * x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact anticomm_rel
    calc
      x * (x + g * x) = x * x + x * (g * x) := mul_add _ _ _
      _ = x * x + (x * g) * x := by rw [← mul_assoc]
      _ = 0 + (-(g * x)) * x := by rw [xsq_rel, hxg]
      _ = 0 + -((g * x) * x) := congrArg (0 + ·) (neg_mul (g * x) x)
      _ = 0 := by rw [mul_assoc, xsq_rel, mul_zero, neg_zero, add_zero]
  rw [xeminus, mul_smul_comm, h, smul_zero]

lemma eminus_smul_e0 : eminus • Pminus.e0 = Pminus.e0 := by
  have h : eminus • Pminus.e0
      = (2⁻¹ : ℂ) • (Pminus.e0 - g • Pminus.e0) := by
    rw [eminus, smul_assoc, sub_smul, one_smul]
  rw [h, Pminus.g_smul]
  refine Pminus.ext fun i => ?_
  fin_cases i <;> simp ; norm_num

lemma xeminus_smul_e0 : xeminus • Pminus.e0 = Pminus.e1 := by
  rw [← x_mul_eminus, mul_smul, eminus_smul_e0, Pminus.x_smul]
  refine Pminus.ext fun i => ?_
  fin_cases i <;> simp

/-- The `ℂ`-linear map `P₋ → A`, `(a, b) ↦ a • e₋ + b • (x·e₋)`, underlying the section. -/
noncomputable def φiMinus : Pminus →ₗ[ℂ] A where
  toFun v := v 0 • eminus + v 1 • xeminus
  map_add' u v := by
    simp only [Pminus.add_apply, add_smul]; abel
  map_smul' c v := by
    simp only [Pminus.complex_smul_apply, RingHom.id_apply, mul_smul, smul_add]

@[simp] lemma φiMinus_apply (v : Pminus) : φiMinus v = v 0 • eminus + v 1 • xeminus := rfl

/-- The `A`-linear section `P₋ → A` of the retraction `a ↦ a • (1,0)`, landing in `A·e₋`. -/
noncomputable def iMinus : Pminus →ₗ[A] A :=
  mkAlgLinear ρPm (Algebra.lmul ℂ A) Pminus.smul_def (fun a b => by
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', smul_eq_mul])
    φiMinus
    (by intro v
        rw [← Pminus.smul_def, Pminus.g_smul]
        simp only [φiMinus_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', neg_smul]
        rw [mul_add, mul_smul_comm, mul_smul_comm, g_mul_eminus, g_mul_xeminus]
        module)
    (by intro v
        rw [← Pminus.smul_def, Pminus.x_smul]
        simp only [φiMinus_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          zero_smul, zero_add, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
        rw [mul_add, mul_smul_comm, mul_smul_comm, x_mul_eminus, x_mul_xeminus, smul_zero,
          add_zero])

/-- The `A`-linear retraction `A ↠ P₋`, `a ↦ a • (1,0)`. -/
noncomputable def rMinus : A →ₗ[A] Pminus := LinearMap.toSpanSingleton A Pminus Pminus.e0

/-- The retraction is split by the section: `rMinus ∘ iMinus = id`, so `P₋` is a summand of `A`. -/
lemma rMinus_comp_iMinus : rMinus.comp iMinus = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  change rMinus (iMinus v) = v
  have hiv : iMinus v = v 0 • eminus + v 1 • xeminus := rfl
  rw [rMinus, LinearMap.toSpanSingleton_apply, hiv, add_smul, smul_assoc, smul_assoc,
    eminus_smul_e0, xeminus_smul_e0]
  funext i; fin_cases i <;> simp

/-- **`P₋` is a projective `A`-module.** It is a direct summand of the free module `A`. -/
instance projective_Pminus : Module.Projective A Pminus :=
  Module.Projective.of_split iMinus rMinus rMinus_comp_iMinus

/-- `ses.X₂ = P₊` is a projective object of `ModuleCat A`. Built explicitly (with the
`Module.Projective` witness placed as a local instance) to sidestep the
`Projective ↔ Module.Projective` synthesis loop. Phrased through `ses.X₂` rather than a fresh
`ModuleCat.of A Pplus` to keep the statement literally about the middle term of the short exact
sequence, which is what the downstream `Ext` arguments consume. -/
theorem projective_ses_X₂ : Projective ses.X₂ :=
  @ModuleCat.projective_of_categoryTheory_projective A _ ses.X₂ projective_Pplus

/-- `sesm.X₂ = P₋` is a projective object of `ModuleCat A`. -/
theorem projective_sesm_X₂ : Projective sesm.X₂ :=
  @ModuleCat.projective_of_categoryTheory_projective A _ sesm.X₂ projective_Pminus

/-- `S₊` and `S₋` are directly `Ext¹`-linked: `Ext¹(S₊, S₋) ≠ 0`. -/
theorem directlyExtLinked :
    Etingof.DirectlyExtLinked A (ModuleCat.of A Splus) (ModuleCat.of A Sminus) :=
  nontrivial_of_ne _ _ extClass_ne_zero

/-- **The algebra of Problem 9.3.2 has a single block.** Its two simple modules `S₊` and
`S₋` are `Etingof.AreLinked`, via the nonsplit extension `0 → S₋ → P₊ → S₊ → 0`.
This is Etingof Example 9.5.2 (iii). -/
theorem areLinked :
    Etingof.AreLinked A (ModuleCat.of A Splus) (ModuleCat.of A Sminus) :=
  Relation.EqvGen.rel _ _
    ⟨(inferInstance : IsSimpleModule A Splus), (inferInstance : IsSimpleModule A Sminus),
      Or.inl (Or.inl directlyExtLinked)⟩

/-! ### `P₋` is indecomposable and is a projective cover of `S₋` -/

/-- Every nonzero `A`-submodule of `P₋` contains the socle vector `(0, 1)`. -/
lemma socle_mem_of_ne_bot_Pminus (N : Submodule A Pminus) (hN : N ≠ ⊥) :
    Pminus.e1 ∈ N := by
  obtain ⟨v, hvN, hv⟩ := (Submodule.ne_bot_iff N).mp hN
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      exact hv (Pminus.ext fun j => by fin_cases j <;> simp [h0, h1])
    have hmem := smul_mem_complex N (v 1)⁻¹ hvN
    have heq : (v 1)⁻¹ • v = Pminus.e1 := by
      refine Pminus.ext fun j => ?_
      fin_cases j <;> simp [h0, inv_mul_cancel₀ h1]
    rwa [heq] at hmem
  · have hx : x • v ∈ N := N.smul_mem x hvN
    have hmem := smul_mem_complex N (v 0)⁻¹ hx
    have heq : (v 0)⁻¹ • (x • v) = Pminus.e1 := by
      rw [Pminus.x_smul]
      refine Pminus.ext fun j => ?_
      fin_cases j <;> simp [inv_mul_cancel₀ h0]
    rwa [heq] at hmem

/-- An `A`-submodule of `P₋` containing a vector with nonzero first coordinate is all of `P₋`. -/
lemma eq_top_of_mem_Pminus (N : Submodule A Pminus) {v : Pminus} (hvN : v ∈ N) (h0 : v 0 ≠ 0) :
    N = ⊤ := by
  have hsoc : Pminus.e1 ∈ N :=
    socle_mem_of_ne_bot_Pminus N (Submodule.ne_bot_iff N |>.mpr
      ⟨v, hvN, fun h => h0 (by rw [h]; rfl)⟩)
  have he0 : Pminus.e0 ∈ N := by
    have hsub : v - v 1 • Pminus.e1 ∈ N :=
      N.sub_mem hvN (smul_mem_complex N (v 1) hsoc)
    have hmem := smul_mem_complex N (v 0)⁻¹ hsub
    have heq : (v 0)⁻¹ • (v - v 1 • Pminus.e1) = Pminus.e0 := by
      refine Pminus.ext fun j => ?_
      fin_cases j <;> simp [inv_mul_cancel₀ h0]
    rwa [heq] at hmem
  refine Submodule.eq_top_iff'.mpr fun w => ?_
  rw [Pminus.eq_smul_e0_add_smul_e1 w]
  exact N.add_mem (smul_mem_complex N _ he0) (smul_mem_complex N _ hsoc)

/-- **`P₋` is indecomposable.** -/
theorem isIndecomposable_Pminus : Etingof.IsIndecomposable A Pminus := by
  refine ⟨inferInstance, fun M N hMN => ?_⟩
  by_contra hc
  obtain ⟨hM, hN⟩ := not_or.mp hc
  have hmem : Pminus.e1 ∈ M ⊓ N :=
    ⟨socle_mem_of_ne_bot_Pminus M hM, socle_mem_of_ne_bot_Pminus N hN⟩
  rw [hMN.inf_eq_bot, Submodule.mem_bot] at hmem
  have hone : Pminus.e1 1 = (0 : Pminus) 1 := by rw [hmem]
  simp at hone

/-- The kernel of `P₋ ↠ S₋` is superfluous: no proper submodule of `P₋` complements it. -/
theorem ker_gSESm_superfluous (N : Submodule A Pminus)
    (h : N ⊔ LinearMap.ker gSESm = ⊤) : N = ⊤ := by
  have hmem : Pminus.e0 ∈ N ⊔ LinearMap.ker gSESm := h ▸ Submodule.mem_top
  obtain ⟨n, hn, k, hk, hnk⟩ := Submodule.mem_sup.mp hmem
  have hk0 : k 0 = 0 := hk
  refine eq_top_of_mem_Pminus N hn ?_
  have hsum : n 0 + k 0 = (1 : ℂ) := by
    have := congrArg (fun w : Pminus => w 0) hnk
    simpa using this
  rw [hk0, add_zero] at hsum
  rw [hsum]
  exact one_ne_zero

/-- **`P₋ ↠ S₋` is a projective cover of `S₋`.** -/
theorem isProjectiveCover_Pminus :
    Module.Projective A Pminus ∧ Function.Surjective gSESm ∧
      ∀ N : Submodule A Pminus, N ⊔ LinearMap.ker gSESm = ⊤ → N = ⊤ :=
  ⟨projective_Pminus, gSESm_surjective, ker_gSESm_superfluous⟩

/-! ## Classification of the simple modules

Every simple `A`-module is isomorphic to `S₊` or to `S₋`, and not to both. The argument is the
standard one: the ideal `A x = x A` is two-sided with square zero, so it annihilates any simple
module; the quotient `A / A x ≅ ℂ[g]/(g² - 1) ≅ ℂ × ℂ` is commutative and split semisimple, so
`g` acts by `+1` or by `-1`; and then every `ℂ`-subspace is an `A`-submodule, forcing the module
to be one-dimensional. -/

/-- `x` normalises `A` on the left: for every `a : A` there is `b : A` with `x * a = b * x`.
Equivalently `x A ⊆ A x`, i.e. `A x` is a two-sided ideal. -/
lemma exists_mul_eq_mul_x (a : A) : ∃ b : A, x * a = b * x := by
  obtain ⟨w, rfl⟩ : ∃ w, mk w = a := RingQuot.mkAlgHom_surjective ℂ Rel a
  induction w with
  | grade0 r =>
      refine ⟨algebraMap ℂ A r, ?_⟩
      rw [mk.commutes]
      exact (Algebra.commutes r x).symm
  | grade1 i =>
      fin_cases i
      · refine ⟨-g, ?_⟩
        change x * g = -g * x
        have h2 : x * g = -(g * x) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]; exact anticomm_rel
        exact h2.trans (neg_mul g x).symm
      · exact ⟨0, by change x * x = 0 * x; rw [xsq_rel, zero_mul]⟩
  | mul p q hp hq =>
      obtain ⟨bp, hbp⟩ := hp
      obtain ⟨bq, hbq⟩ := hq
      refine ⟨bp * bq, ?_⟩
      calc x * mk (p * q) = (x * mk p) * mk q := by rw [map_mul, mul_assoc]
        _ = bp * (x * mk q) := by rw [hbp, mul_assoc]
        _ = bp * bq * x := by rw [hbq, mul_assoc]
  | add p q hp hq =>
      obtain ⟨bp, hbp⟩ := hp
      obtain ⟨bq, hbq⟩ := hq
      exact ⟨bp + bq, by rw [map_add, mul_add, hbp, hbq, add_mul]⟩

section Classification

variable (S : Type u) [AddCommGroup S] [Module A S]

/-- The `x`-annihilator `{s | x • s = 0}` of an `A`-module, as an `A`-submodule. It is a
submodule because `x A ⊆ A x` (`exists_mul_eq_mul_x`). -/
def xAnnihilator : Submodule A S where
  carrier := {s : S | x • s = 0}
  add_mem' := by
    intro a b ha hb
    change x • (a + b) = 0
    rw [smul_add, show x • a = 0 from ha, show x • b = 0 from hb, add_zero]
  zero_mem' := by change x • (0 : S) = 0; rw [smul_zero]
  smul_mem' := by
    intro c s hs
    obtain ⟨b, hb⟩ := exists_mul_eq_mul_x c
    change x • (c • s) = 0
    rw [smul_smul, hb, ← smul_smul]
    change b • (x • s) = 0
    rw [show x • s = 0 from hs, smul_zero]

variable {S}

@[simp] lemma mem_xAnnihilator {s : S} : s ∈ xAnnihilator S ↔ x • s = 0 := Iff.rfl

/-- **`x` annihilates every simple `A`-module.** The ideal `A x` has square zero, so the
`x`-annihilator of a simple module is a nonzero submodule, hence everything. -/
theorem x_smul_eq_zero_of_isSimpleModule [IsSimpleModule A S] (s : S) : x • s = 0 := by
  by_cases h : ∀ t : S, x • t = 0
  · exact h s
  · obtain ⟨t, ht⟩ := not_forall.mp h
    have hmem : x • t ∈ xAnnihilator S := by
      change x • (x • t) = 0
      rw [smul_smul, xsq_rel, zero_smul]
    have hne : xAnnihilator S ≠ ⊥ := fun hb => ht (by simpa [hb] using hmem)
    have htop : xAnnihilator S = ⊤ := (eq_bot_or_eq_top (xAnnihilator S)).resolve_left hne
    exact mem_xAnnihilator.mp (htop ▸ Submodule.mem_top)

variable [Module ℂ S] [IsScalarTower ℂ A S]

/-- If `x` acts as zero then every `g`-stable `ℂ`-subspace is stable under all of `A`, because
`g` and `x` generate `A` as a `ℂ`-algebra. -/
lemma smul_mem_of_g_stable (W : Submodule ℂ S)
    (hx : ∀ t : S, x • t = 0) (hg : ∀ w ∈ W, g • w ∈ W) (a : A) :
    ∀ w ∈ W, a • w ∈ W := by
  obtain ⟨v, rfl⟩ : ∃ v, mk v = a := RingQuot.mkAlgHom_surjective ℂ Rel a
  induction v with
  | grade0 r =>
      intro w hw
      rw [mk.commutes, algebraMap_smul]
      exact W.smul_mem r hw
  | grade1 i =>
      intro w hw
      fin_cases i
      · exact hg w hw
      · change x • w ∈ W
        rw [hx w]
        exact W.zero_mem
  | mul p q hp hq =>
      intro w hw
      rw [map_mul, mul_smul]
      exact hp _ (hq w hw)
  | add p q hp hq =>
      intro w hw
      rw [map_add, add_smul]
      exact W.add_mem (hp w hw) (hq w hw)

/-- The `+1`-eigenspace of `g`, as a `ℂ`-subspace. -/
noncomputable def gPlusEigenspace : Submodule ℂ S :=
  LinearMap.ker (Algebra.lsmul ℂ ℂ S g - 1)

lemma mem_gPlusEigenspace {s : S} : s ∈ (gPlusEigenspace : Submodule ℂ S) ↔ g • s = s := by
  simp [gPlusEigenspace, sub_eq_zero, Algebra.lsmul_coe]

omit [Module ℂ S] [IsScalarTower ℂ A S] in
lemma g_smul_g_smul (s : S) : g • (g • s) = s := by
  rw [smul_smul, gsq_rel, one_smul]

/-- **On a simple `A`-module, `g` acts as the scalar `+1` or as the scalar `-1`.** The `+1`
eigenspace of the involution `g` is an `A`-submodule (using that `x` acts as zero), so it is all
of the module or zero; in the second case `s + g • s = 0` for every `s`. -/
theorem g_smul_eq_self_or_neg [IsSimpleModule A S] :
    (∀ s : S, g • s = s) ∨ (∀ s : S, g • s = -s) := by
  have hx : ∀ t : S, x • t = 0 := x_smul_eq_zero_of_isSimpleModule
  have hgst : ∀ w ∈ (gPlusEigenspace : Submodule ℂ S), g • w ∈ gPlusEigenspace := by
    intro w hw
    rw [mem_gPlusEigenspace] at hw ⊢
    rw [hw]; exact hw
  let N : Submodule A S :=
    { carrier := (gPlusEigenspace : Submodule ℂ S)
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun c s hs => smul_mem_of_g_stable _ hx hgst c s hs }
  rcases eq_bot_or_eq_top N with hb | ht
  · refine Or.inr fun s => ?_
    have hmem : s + g • s ∈ N := by
      change s + g • s ∈ (gPlusEigenspace : Submodule ℂ S)
      rw [mem_gPlusEigenspace, smul_add, g_smul_g_smul, add_comm]
    have hz : s + g • s = 0 := by simpa [hb] using hmem
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hz
  · refine Or.inl fun s => ?_
    have hs : s ∈ N := ht ▸ Submodule.mem_top
    exact mem_gPlusEigenspace.mp hs

/-- A simple `A`-module is simple as a `ℂ`-vector space: once `x` acts as zero and `g` acts as a
scalar, *every* `ℂ`-subspace is an `A`-submodule. -/
theorem isSimpleModule_complex [IsSimpleModule A S] : IsSimpleModule ℂ S := by
  have hx : ∀ t : S, x • t = 0 := x_smul_eq_zero_of_isSimpleModule
  have hgstab : ∀ W : Submodule ℂ S, ∀ w ∈ W, g • w ∈ W := by
    rcases g_smul_eq_self_or_neg (S := S) with h | h
    · intro W w hw; rw [h w]; exact hw
    · intro W w hw; rw [h w]; exact W.neg_mem hw
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun W => ?_ }
  let N : Submodule A S :=
    { carrier := (W : Set S)
      add_mem' := fun ha hb => W.add_mem ha hb
      zero_mem' := W.zero_mem
      smul_mem' := fun c s hs => smul_mem_of_g_stable W hx (hgstab W) c s hs }
  rcases eq_bot_or_eq_top N with hb | ht
  · refine Or.inl (le_antisymm (fun s hs => ?_) bot_le)
    have hsN : s ∈ N := hs
    simpa [hb] using hsN
  · refine Or.inr (le_antisymm le_top fun s _ => ?_)
    have hs : s ∈ N := ht ▸ Submodule.mem_top
    exact hs

/-- Every simple `A`-module is one-dimensional over `ℂ`. -/
theorem finrank_eq_one_of_isSimpleModule [IsSimpleModule A S] : Module.finrank ℂ S = 1 :=
  isSimpleModule_iff_finrank_eq_one.mp isSimpleModule_complex

end Classification

/-! ### Every simple module is `S₊` or `S₋` -/

section Exhaustive

variable {S : Type u} [AddCommGroup S] [Module ℂ S] [Module A S] [IsScalarTower ℂ A S]

/-- `S₊` has carrier `ℂ`; this is the identity, used to view a vector of `S₊` as a scalar. -/
def Splus.toℂ (c : Splus) : ℂ := c

/-- `S₋` has carrier `ℂ`; this is the identity, used to view a vector of `S₋` as a scalar. -/
def Sminus.toℂ (c : Sminus) : ℂ := c

/-- In a simple `A`-module, scaling a fixed nonzero vector is a `ℂ`-linear bijection `ℂ ≃ S`:
injective because `ℂ` is a field, surjective because a nonzero vector spans. -/
lemma smul_singleton_bijective [IsSimpleModule A S] {s₀ : S} (hs₀ : s₀ ≠ 0) :
    Function.Bijective (fun c : ℂ => c • s₀) := by
  have : IsSimpleModule ℂ S := isSimpleModule_complex
  constructor
  · intro a b hab
    have hz : (a - b) • s₀ = 0 := by
      simp only at hab
      rw [sub_smul, hab, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hs₀)
  · intro t
    have hmem : t ∈ (ℂ ∙ s₀) :=
      (IsSimpleModule.span_singleton_eq_top ℂ hs₀) ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc⟩

/-- The `ℂ`-linear map `S₊ → S` sending the scalar `c` to `c • s₀`. -/
noncomputable def spanMapPlus (s₀ : S) : Splus →ₗ[ℂ] S where
  toFun c := c.toℂ • s₀
  map_add' a b := add_smul a.toℂ b.toℂ s₀
  map_smul' r c := mul_smul r c.toℂ s₀

omit [Module A S] [IsScalarTower ℂ A S] in
@[simp] lemma spanMapPlus_apply (s₀ : S) (c : Splus) : spanMapPlus s₀ c = c.toℂ • s₀ := rfl

/-- The `ℂ`-linear map `S₋ → S` sending the scalar `c` to `c • s₀`. -/
noncomputable def spanMapMinus (s₀ : S) : Sminus →ₗ[ℂ] S where
  toFun c := c.toℂ • s₀
  map_add' a b := add_smul a.toℂ b.toℂ s₀
  map_smul' r c := mul_smul r c.toℂ s₀

omit [Module A S] [IsScalarTower ℂ A S] in
@[simp] lemma spanMapMinus_apply (s₀ : S) (c : Sminus) : spanMapMinus s₀ c = c.toℂ • s₀ := rfl

/-- If `g` acts as `+1` on a simple `A`-module `S`, then `S₊ ≅ S`. -/
noncomputable def equivSplusOfGSmulEqSelf [IsSimpleModule A S]
    {s₀ : S} (hs₀ : s₀ ≠ 0) (h : ∀ s : S, g • s = s) : Splus ≃ₗ[A] S :=
  LinearEquiv.ofBijective
    (mkAlgLinear ρplus (Algebra.lsmul ℂ ℂ S) Splus.smul_def (fun _ _ => rfl) (spanMapPlus s₀)
      (by intro v
          simp only [ρplus, repHom_g, Module.End.one_apply, Algebra.lsmul_coe,
            spanMapPlus_apply]
          rw [smul_comm, h s₀])
      (by intro v
          simp only [ρplus, repHom_x, LinearMap.zero_apply, Algebra.lsmul_coe,
            spanMapPlus_apply, map_zero]
          rw [smul_comm, x_smul_eq_zero_of_isSimpleModule s₀, smul_zero]))
    (by exact smul_singleton_bijective hs₀)

/-- If `g` acts as `-1` on a simple `A`-module `S`, then `S₋ ≅ S`. -/
noncomputable def equivSminusOfGSmulEqNeg [IsSimpleModule A S]
    {s₀ : S} (hs₀ : s₀ ≠ 0) (h : ∀ s : S, g • s = -s) : Sminus ≃ₗ[A] S :=
  LinearEquiv.ofBijective
    (mkAlgLinear ρminus (Algebra.lsmul ℂ ℂ S) Sminus.smul_def (fun _ _ => rfl) (spanMapMinus s₀)
      (by intro v
          simp only [ρminus, repHom_g, LinearMap.neg_apply, Module.End.one_apply,
            Algebra.lsmul_coe, map_neg, spanMapMinus_apply]
          rw [smul_comm, h s₀, smul_neg])
      (by intro v
          simp only [ρminus, repHom_x, LinearMap.zero_apply, Algebra.lsmul_coe,
            spanMapMinus_apply, map_zero]
          rw [smul_comm, x_smul_eq_zero_of_isSimpleModule s₀, smul_zero]))
    (by exact smul_singleton_bijective hs₀)

/-- **Exhaustiveness of the classification of simple modules (Problem 9.3.2, part 1).**
Every simple `A`-module is isomorphic to `S₊` or to `S₋`. -/
theorem nonempty_linearEquiv_splus_or_sminus (S : Type u) [AddCommGroup S] [Module ℂ S]
    [Module A S] [IsScalarTower ℂ A S] [IsSimpleModule A S] :
    Nonempty (S ≃ₗ[A] Splus) ∨ Nonempty (S ≃ₗ[A] Sminus) := by
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  rcases g_smul_eq_self_or_neg (S := S) with h | h
  · exact Or.inl ⟨(equivSplusOfGSmulEqSelf hs₀ h).symm⟩
  · exact Or.inr ⟨(equivSminusOfGSmulEqNeg hs₀ h).symm⟩

/-- The two cases are mutually exclusive: no `A`-module is isomorphic to both `S₊` and `S₋`. -/
theorem not_linearEquiv_splus_and_sminus (S : Type u) [AddCommGroup S] [Module A S] :
    ¬(Nonempty (S ≃ₗ[A] Splus) ∧ Nonempty (S ≃ₗ[A] Sminus)) := by
  rintro ⟨⟨e₁⟩, ⟨e₂⟩⟩
  exact splus_not_iso_sminus.false (e₁.symm.trans e₂)

/-- **The simple `A`-modules are exactly `S₊` and `S₋`.** Every simple `A`-module is isomorphic
to exactly one of them. This is the first part of Problem 9.3.2. -/
theorem simple_module_classification (S : Type u) [AddCommGroup S] [Module ℂ S]
    [Module A S] [IsScalarTower ℂ A S] [IsSimpleModule A S] :
    Xor (Nonempty (S ≃ₗ[A] Splus)) (Nonempty (S ≃ₗ[A] Sminus)) := by
  rcases nonempty_linearEquiv_splus_or_sminus S with h | h
  · exact Or.inl ⟨h, fun h' => not_linearEquiv_splus_and_sminus S ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => not_linearEquiv_splus_and_sminus S ⟨h', h⟩⟩

end Exhaustive

/-! ## The Cartan matrix of `A` (Definition 9.3.1)

The third question of Problem 9.3.2. Each of the four Hom spaces `Hom_A(P_s, P_t)`,
`s, t ∈ {+, -}`, is one-dimensional over `ℂ`, so the Cartan matrix of `A` is `!![1, 1; 1, 1]`.

The computation is uniform. Each `P_s` is generated over `A` by `e₀`, since `e₁ = x · e₀`
(`Pplus.eq_smul_e0`), so an `A`-linear map out of `P_s` is determined by its value on `e₀`
(`Pplus.hom_ext`). That value is constrained by `g`-equivariance: `g · e₀ = ε e₀` with
`ε = +1` on `P₊` and `ε = -1` on `P₋`, so `φ e₀` lies in the `ε`-eigenspace of `g` on the
target. Each eigenspace of the involution `g` on `P_t` is one-dimensional, spanned by `e₀` or
by `e₁` — that is the content of the four `eq_smul_e*_of_g_smul_eq_*` lemmas. Hence each Hom
space is `ℂ · T` for a single explicit generator `T`, and the coefficient map `φ ↦ (φ e₀) k` is
a `ℂ`-linear isomorphism onto `ℂ`. -/

section Cartan

/-! ### `ℂ` is central, so the Hom spaces are `ℂ`-vector spaces -/

instance : SMulCommClass A ℂ Pplus where
  smul_comm a c v := by
    rw [← algebraMap_smul A c v, ← algebraMap_smul A c (a • v), smul_smul, smul_smul,
      Algebra.commutes]

instance : SMulCommClass A ℂ Pminus where
  smul_comm a c v := by
    rw [← algebraMap_smul A c v, ← algebraMap_smul A c (a • v), smul_smul, smul_smul,
      Algebra.commutes]

/-! ### The generators `e₀` generate `P₊` and `P₋` over `A` -/

lemma Pplus.eq_smul_e0 (v : Pplus) :
    v = (algebraMap ℂ A (v 0) + algebraMap ℂ A (v 1) * x) • Pplus.e0 := by
  rw [add_smul, mul_smul, Pplus.x_smul]
  simp only [algebraMap_smul, Pplus.e0_zero]
  refine Pplus.ext fun i => ?_
  fin_cases i <;> simp

lemma Pminus.eq_smul_e0 (v : Pminus) :
    v = (algebraMap ℂ A (v 0) + algebraMap ℂ A (v 1) * x) • Pminus.e0 := by
  rw [add_smul, mul_smul, Pminus.x_smul]
  simp only [algebraMap_smul, Pminus.e0_zero]
  refine Pminus.ext fun i => ?_
  fin_cases i <;> simp

/-- An `A`-linear map out of `P₊` is determined by its value on the generator `e₀`. -/
lemma Pplus.hom_ext {M : Type u} [AddCommGroup M] [Module A M] {φ ψ : Pplus →ₗ[A] M}
    (h : φ Pplus.e0 = ψ Pplus.e0) : φ = ψ := by
  refine LinearMap.ext fun v => ?_
  rw [Pplus.eq_smul_e0 v, map_smul, map_smul, h]

/-- An `A`-linear map out of `P₋` is determined by its value on the generator `e₀`. -/
lemma Pminus.hom_ext {M : Type u} [AddCommGroup M] [Module A M] {φ ψ : Pminus →ₗ[A] M}
    (h : φ Pminus.e0 = ψ Pminus.e0) : φ = ψ := by
  refine LinearMap.ext fun v => ?_
  rw [Pminus.eq_smul_e0 v, map_smul, map_smul, h]

/-! ### The action of the generators on `e₀` and `e₁` -/

lemma Pplus.g_smul_e0 : g • Pplus.e0 = Pplus.e0 := by
  rw [Pplus.g_smul]; refine Pplus.ext fun i => ?_; fin_cases i <;> simp

lemma Pplus.x_smul_e0 : x • Pplus.e0 = Pplus.e1 := by
  rw [Pplus.x_smul]; refine Pplus.ext fun i => ?_; fin_cases i <;> simp

lemma Pminus.g_smul_e0 : g • Pminus.e0 = -Pminus.e0 := by
  rw [Pminus.g_smul]; refine Pminus.ext fun i => ?_; fin_cases i <;> simp

lemma Pminus.x_smul_e0 : x • Pminus.e0 = Pminus.e1 := by
  rw [Pminus.x_smul]; refine Pminus.ext fun i => ?_; fin_cases i <;> simp

/-- `g` fixes `φ e₀` for any `A`-linear `φ` out of `P₊`, since `g · e₀ = e₀` there. -/
lemma Pplus.g_smul_apply_e0 {M : Type u} [AddCommGroup M] [Module A M] (φ : Pplus →ₗ[A] M) :
    g • φ Pplus.e0 = φ Pplus.e0 := by
  rw [← map_smul, Pplus.g_smul_e0]

/-- `g` negates `φ e₀` for any `A`-linear `φ` out of `P₋`, since `g · e₀ = -e₀` there. -/
lemma Pminus.g_smul_apply_e0 {M : Type u} [AddCommGroup M] [Module A M] (φ : Pminus →ₗ[A] M) :
    g • φ Pminus.e0 = -φ Pminus.e0 := by
  rw [← map_smul, Pminus.g_smul_e0, map_neg]

/-! ### The `g`-eigenspaces of `P₊` and `P₋` are the coordinate lines -/

/-- `g` is an involution, so its eigenvalues are `±1` and the two eigenspaces are transverse:
a scalar fixed up to sign by `g` and equal to its own negative vanishes (`ℂ` has
characteristic `0`). -/
private lemma eq_zero_of_neg_eq {z : ℂ} (h : -z = z) : z = 0 := by
  have h2 : (2 : ℂ) * z = 0 := by
    rw [two_mul]
    calc z + z = -z + z := by rw [h]
      _ = 0 := neg_add_cancel z
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The `+1`-eigenspace of `g` on `P₊` is the line spanned by `e₀`. -/
lemma Pplus.eq_smul_e0_of_g_smul_eq_self {w : Pplus} (h : g • w = w) : w = w 0 • Pplus.e0 := by
  have h1 : w 1 = 0 := by
    have h2 : (![w 0, -w 1] : Pplus) 1 = w 1 := by rw [← Pplus.g_smul, h]
    exact eq_zero_of_neg_eq (z := w 1) h2
  refine Pplus.ext fun i => ?_
  fin_cases i <;> simp [h1]

/-- The `-1`-eigenspace of `g` on `P₊` is the line spanned by the socle vector `e₁`. -/
lemma Pplus.eq_smul_e1_of_g_smul_eq_neg {w : Pplus} (h : g • w = -w) : w = w 1 • Pplus.e1 := by
  have h0 : w 0 = 0 := by
    have h2 : (![w 0, -w 1] : Pplus) 0 = (-w) 0 := by rw [← Pplus.g_smul, h]
    exact eq_zero_of_neg_eq (z := w 0) h2.symm
  refine Pplus.ext fun i => ?_
  fin_cases i <;> simp [h0]

/-- The `+1`-eigenspace of `g` on `P₋` is the line spanned by the socle vector `e₁`. -/
lemma Pminus.eq_smul_e1_of_g_smul_eq_self {w : Pminus} (h : g • w = w) : w = w 1 • Pminus.e1 := by
  have h0 : w 0 = 0 := by
    have h2 : (![-w 0, w 1] : Pminus) 0 = w 0 := by rw [← Pminus.g_smul, h]
    exact eq_zero_of_neg_eq (z := w 0) h2
  refine Pminus.ext fun i => ?_
  fin_cases i <;> simp [h0]

/-- The `-1`-eigenspace of `g` on `P₋` is the line spanned by `e₀`. -/
lemma Pminus.eq_smul_e0_of_g_smul_eq_neg {w : Pminus} (h : g • w = -w) : w = w 0 • Pminus.e0 := by
  have h1 : w 1 = 0 := by
    have h2 : (![-w 0, w 1] : Pminus) 1 = (-w) 1 := by rw [← Pminus.g_smul, h]
    exact eq_zero_of_neg_eq (z := w 1) h2.symm
  refine Pminus.ext fun i => ?_
  fin_cases i <;> simp [h1]

/-! ### The generators of the four Hom spaces

`Hom_A(P₊, P₊)` and `Hom_A(P₋, P₋)` are generated by the identity. The two off-diagonal Hom
spaces are generated by the map `(a, b) ↦ (0, a)`, which sends `e₀` to the socle vector `e₁` and
kills `e₁`. -/

/-- The `ℂ`-linear map `P₊ → P₋`, `(a, b) ↦ (0, a)`, underlying the generator of
`Hom_A(P₊, P₋)`. -/
def φTpm : Pplus →ₗ[ℂ] Pminus where
  toFun v := ![0, v 0]
  map_add' u v := by refine Pminus.ext fun i => ?_; fin_cases i <;> simp
  map_smul' c v := by refine Pminus.ext fun i => ?_; fin_cases i <;> simp

@[simp] lemma φTpm_apply (v : Pplus) : φTpm v = ![0, v 0] := rfl

/-- The `ℂ`-linear map `P₋ → P₊`, `(a, b) ↦ (0, a)`, underlying the generator of
`Hom_A(P₋, P₊)`. -/
def φTmp : Pminus →ₗ[ℂ] Pplus where
  toFun v := ![0, v 0]
  map_add' u v := by refine Pplus.ext fun i => ?_; fin_cases i <;> simp
  map_smul' c v := by refine Pplus.ext fun i => ?_; fin_cases i <;> simp

@[simp] lemma φTmp_apply (v : Pminus) : φTmp v = ![0, v 0] := rfl

/-- **The generator of `Hom_A(P₊, P₋)`**: `e₀ ↦ e₁`, `e₁ ↦ 0`. It is `A`-linear because the
`+1`-eigenline of `g` in `P₋` is spanned by `e₁`, and `x · e₁ = 0`. -/
noncomputable def Tpm : Pplus →ₗ[A] Pminus :=
  mkAlgLinear ρP ρPm Pplus.smul_def Pminus.smul_def φTpm
    (by intro v
        rw [← Pplus.smul_def, ← Pminus.smul_def, Pplus.g_smul, Pminus.g_smul]
        refine Pminus.ext fun i => ?_
        fin_cases i <;> simp)
    (by intro v
        rw [← Pplus.smul_def, ← Pminus.smul_def, Pplus.x_smul, Pminus.x_smul]
        refine Pminus.ext fun i => ?_
        fin_cases i <;> simp)

/-- **The generator of `Hom_A(P₋, P₊)`**: `e₀ ↦ e₁`, `e₁ ↦ 0`. -/
noncomputable def Tmp : Pminus →ₗ[A] Pplus :=
  mkAlgLinear ρPm ρP Pminus.smul_def Pplus.smul_def φTmp
    (by intro v
        rw [← Pminus.smul_def, ← Pplus.smul_def, Pminus.g_smul, Pplus.g_smul]
        refine Pplus.ext fun i => ?_
        fin_cases i <;> simp)
    (by intro v
        rw [← Pminus.smul_def, ← Pplus.smul_def, Pminus.x_smul, Pplus.x_smul]
        refine Pplus.ext fun i => ?_
        fin_cases i <;> simp)

@[simp] lemma Tpm_apply (v : Pplus) : Tpm v = ![0, v 0] := rfl

@[simp] lemma Tmp_apply (v : Pminus) : Tmp v = ![0, v 0] := rfl

lemma Tpm_e0 : Tpm Pplus.e0 = Pminus.e1 := by
  rw [Tpm_apply]; refine Pminus.ext fun i => ?_; fin_cases i <;> simp

lemma Tmp_e0 : Tmp Pminus.e0 = Pplus.e1 := by
  rw [Tmp_apply]; refine Pplus.ext fun i => ?_; fin_cases i <;> simp

/-! ### The four Hom spaces are one-dimensional

For each pair the coefficient map `φ ↦ (φ e₀) k` is a `ℂ`-linear bijection onto `ℂ`, where `k`
is the coordinate of the eigenline containing `φ e₀`. -/

/-- The coefficient of `φ ∈ Hom_A(P₊, P₊)` on the generator `id`. -/
noncomputable def homCoeffPP : (Pplus →ₗ[A] Pplus) →ₗ[ℂ] ℂ where
  toFun φ := (φ Pplus.e0) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficient of `φ ∈ Hom_A(P₊, P₋)` on the generator `Tpm`. -/
noncomputable def homCoeffPM : (Pplus →ₗ[A] Pminus) →ₗ[ℂ] ℂ where
  toFun φ := (φ Pplus.e0) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficient of `φ ∈ Hom_A(P₋, P₊)` on the generator `Tmp`. -/
noncomputable def homCoeffMP : (Pminus →ₗ[A] Pplus) →ₗ[ℂ] ℂ where
  toFun φ := (φ Pminus.e0) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficient of `φ ∈ Hom_A(P₋, P₋)` on the generator `id`. -/
noncomputable def homCoeffMM : (Pminus →ₗ[A] Pminus) →ₗ[ℂ] ℂ where
  toFun φ := (φ Pminus.e0) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma homCoeffPP_bijective : Function.Bijective homCoeffPP := by
  constructor
  · intro φ ψ h
    refine Pplus.hom_ext ?_
    rw [Pplus.eq_smul_e0_of_g_smul_eq_self (Pplus.g_smul_apply_e0 φ),
      Pplus.eq_smul_e0_of_g_smul_eq_self (Pplus.g_smul_apply_e0 ψ)]
    exact congrArg (fun c : ℂ => c • Pplus.e0) h
  · intro c
    refine ⟨c • LinearMap.id, ?_⟩
    change ((c • (LinearMap.id : Pplus →ₗ[A] Pplus)) Pplus.e0) 0 = c
    simp

lemma homCoeffPM_bijective : Function.Bijective homCoeffPM := by
  constructor
  · intro φ ψ h
    refine Pplus.hom_ext ?_
    rw [Pminus.eq_smul_e1_of_g_smul_eq_self (Pplus.g_smul_apply_e0 φ),
      Pminus.eq_smul_e1_of_g_smul_eq_self (Pplus.g_smul_apply_e0 ψ)]
    exact congrArg (fun c : ℂ => c • Pminus.e1) h
  · intro c
    refine ⟨c • Tpm, ?_⟩
    change ((c • Tpm) Pplus.e0) 1 = c
    rw [LinearMap.smul_apply, Tpm_e0]
    simp

lemma homCoeffMP_bijective : Function.Bijective homCoeffMP := by
  constructor
  · intro φ ψ h
    refine Pminus.hom_ext ?_
    rw [Pplus.eq_smul_e1_of_g_smul_eq_neg (Pminus.g_smul_apply_e0 φ),
      Pplus.eq_smul_e1_of_g_smul_eq_neg (Pminus.g_smul_apply_e0 ψ)]
    exact congrArg (fun c : ℂ => c • Pplus.e1) h
  · intro c
    refine ⟨c • Tmp, ?_⟩
    change ((c • Tmp) Pminus.e0) 1 = c
    rw [LinearMap.smul_apply, Tmp_e0]
    simp

lemma homCoeffMM_bijective : Function.Bijective homCoeffMM := by
  constructor
  · intro φ ψ h
    refine Pminus.hom_ext ?_
    rw [Pminus.eq_smul_e0_of_g_smul_eq_neg (Pminus.g_smul_apply_e0 φ),
      Pminus.eq_smul_e0_of_g_smul_eq_neg (Pminus.g_smul_apply_e0 ψ)]
    exact congrArg (fun c : ℂ => c • Pminus.e0) h
  · intro c
    refine ⟨c • LinearMap.id, ?_⟩
    change ((c • (LinearMap.id : Pminus →ₗ[A] Pminus)) Pminus.e0) 0 = c
    simp

/-- `Hom_A(P₊, P₊) ≅ ℂ`, the isomorphism sending `φ` to its coefficient on `id`. -/
noncomputable def homEquivPP : (Pplus →ₗ[A] Pplus) ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective homCoeffPP homCoeffPP_bijective

/-- `Hom_A(P₊, P₋) ≅ ℂ`, the isomorphism sending `φ` to its coefficient on `Tpm`. -/
noncomputable def homEquivPM : (Pplus →ₗ[A] Pminus) ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective homCoeffPM homCoeffPM_bijective

/-- `Hom_A(P₋, P₊) ≅ ℂ`, the isomorphism sending `φ` to its coefficient on `Tmp`. -/
noncomputable def homEquivMP : (Pminus →ₗ[A] Pplus) ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective homCoeffMP homCoeffMP_bijective

/-- `Hom_A(P₋, P₋) ≅ ℂ`, the isomorphism sending `φ` to its coefficient on `id`. -/
noncomputable def homEquivMM : (Pminus →ₗ[A] Pminus) ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective homCoeffMM homCoeffMM_bijective

theorem finrank_hom_Pplus_Pplus : Module.finrank ℂ (Pplus →ₗ[A] Pplus) = 1 := by
  rw [homEquivPP.finrank_eq, Module.finrank_self]

theorem finrank_hom_Pplus_Pminus : Module.finrank ℂ (Pplus →ₗ[A] Pminus) = 1 := by
  rw [homEquivPM.finrank_eq, Module.finrank_self]

theorem finrank_hom_Pminus_Pplus : Module.finrank ℂ (Pminus →ₗ[A] Pplus) = 1 := by
  rw [homEquivMP.finrank_eq, Module.finrank_self]

theorem finrank_hom_Pminus_Pminus : Module.finrank ℂ (Pminus →ₗ[A] Pminus) = 1 := by
  rw [homEquivMM.finrank_eq, Module.finrank_self]

/-! ### The Cartan matrix

The indexed family `Pfam = ![P₊, P₋]` of the two projective indecomposables. This is the input
`Etingof.algebraCartanMatrix` (Definition 9.3.1) consumes, and forming it is exactly what the
distinct carriers of `P₊` and `P₋` make possible. -/

/-- The family of the two projective indecomposables of `A`, indexed as `P₊, P₋`. -/
def Pfam : Fin 2 → Type
  | 0 => Pplus
  | 1 => Pminus

instance : ∀ i, AddCommGroup (Pfam i)
  | 0 => inferInstanceAs (AddCommGroup Pplus)
  | 1 => inferInstanceAs (AddCommGroup Pminus)

noncomputable instance : ∀ i, Module A (Pfam i)
  | 0 => inferInstanceAs (Module A Pplus)
  | 1 => inferInstanceAs (Module A Pminus)

instance : ∀ i, Module ℂ (Pfam i)
  | 0 => inferInstanceAs (Module ℂ Pplus)
  | 1 => inferInstanceAs (Module ℂ Pminus)

instance : ∀ i, SMulCommClass A ℂ (Pfam i)
  | 0 => inferInstanceAs (SMulCommClass A ℂ Pplus)
  | 1 => inferInstanceAs (SMulCommClass A ℂ Pminus)

instance : ∀ i, IsScalarTower ℂ A (Pfam i)
  | 0 => inferInstanceAs (IsScalarTower ℂ A Pplus)
  | 1 => inferInstanceAs (IsScalarTower ℂ A Pminus)

instance : ∀ i, Module.Finite ℂ (Pfam i)
  | 0 => inferInstanceAs (Module.Finite ℂ Pplus)
  | 1 => inferInstanceAs (Module.Finite ℂ Pminus)

instance : ∀ i, Nontrivial (Pfam i)
  | 0 => inferInstanceAs (Nontrivial Pplus)
  | 1 => inferInstanceAs (Nontrivial Pminus)

@[simp] lemma Pfam_zero : Pfam 0 = Pplus := rfl

@[simp] lemma Pfam_one : Pfam 1 = Pminus := rfl

/-- The family carries the intended module structures, not merely the intended carriers: the
off-diagonal entry of the Cartan matrix is *literally* `dim_ℂ Hom_A(P₊, P₋)`, computed with the
`A`-action of `P₊` on the source and that of `P₋` on the target. This is the statement that
could not even be formed while `Pplus` and `Pminus` shared a carrier, since the two `Module A`
instances then collided. -/
lemma algebraCartanMatrix_Pfam_apply_zero_one :
    Etingof.algebraCartanMatrix (k := ℂ) (A := A) Pfam 0 1
      = Module.finrank ℂ (Pplus →ₗ[A] Pminus) := rfl

/-- Every entry of the Cartan matrix of `A` is `1`. -/
theorem algebraCartanMatrix_Pfam_apply (i j : Fin 2) :
    Etingof.algebraCartanMatrix (k := ℂ) (A := A) Pfam i j = 1 := by
  fin_cases i <;> fin_cases j
  · exact finrank_hom_Pplus_Pplus
  · exact finrank_hom_Pplus_Pminus
  · exact finrank_hom_Pminus_Pplus
  · exact finrank_hom_Pminus_Pminus

/-- **The Cartan matrix of the algebra of Problem 9.3.2 is `!![1, 1; 1, 1]`.**

This is the third and last part of Problem 9.3.2. All four entries are `1`: each Hom space
`Hom_A(P_s, P_t)` is the line spanned by a single explicit generator. Equivalently (Proposition
9.2.3) each simple `S_s` occurs exactly once in the Jordan–Hölder series of each `P_t`, which
matches the composition series `0 ⊂ S₋ ⊂ P₊` and `0 ⊂ S₊ ⊂ P₋`. -/
theorem algebraCartanMatrix_Pfam :
    Etingof.algebraCartanMatrix (k := ℂ) (A := A) Pfam = !![1, 1; 1, 1] := by
  refine Matrix.ext fun i j => ?_
  rw [algebraCartanMatrix_Pfam_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- Consistency with Etingof's remark after Definition 9.3.1 that the Cartan matrix has positive
diagonal entries: the general lemma `Etingof.algebraCartanMatrix_diag_pos` applies to this family
(the projectives are nonzero and finite dimensional over `ℂ`), and agrees with the computation. -/
theorem algebraCartanMatrix_Pfam_diag_pos (i : Fin 2) :
    0 < Etingof.algebraCartanMatrix (k := ℂ) (A := A) Pfam i i :=
  Etingof.algebraCartanMatrix_diag_pos Pfam i

end Cartan

/-! ## The left regular module: `A ≅ P₊ ⊕ P₋`

The idempotents `e₊ = (1 + g)/2` and `e₋ = (1 - g)/2` are orthogonal and sum to `1`, so the
left regular module splits as `A = A·e₊ ⊕ A·e₋`. The sections `iPlus`, `iMinus` and the
retractions `rPlus`, `rMinus` already built for projectivity assemble into an isomorphism of
left `A`-modules `P₊ × P₋ ≃ₗ[A] A`.

Only one new ingredient is needed: each retraction kills the *other* summand. `e₋ · e₀⁺ = 0`
because `g` acts as `+1` on `e₀⁺`, so `(1 - g)·e₀⁺ = 0`; and `x·e₋ · e₀⁺ = x · (e₋ · e₀⁺) = 0`
follows. Dually on `P₋`. With that, `rProd ∘ iProd = id`, while `iProd ∘ rProd` is
multiplication by `e₊ + e₋ = 1`.

This makes the four-dimensionality of `A` concrete: `dim_ℂ A = 4`, matching the basis
`1, g, x, gx` asserted in the book. -/

section RegularDecomposition

/-- The two idempotents are complementary: `e₊ + e₋ = 1`. -/
lemma eplus_add_eminus : eplus + eminus = (1 : A) := by
  have h : (1 + g) + (1 - g) = (2 : ℂ) • (1 : A) := by rw [two_smul]; abel
  rw [eplus, eminus, ← smul_add, h, smul_smul, show ((2 : ℂ)⁻¹ * 2) = 1 by norm_num, one_smul]

/-! ### Each retraction kills the other summand -/

/-- `e₋` annihilates the generator of `P₊`: `g` acts as `+1` there, so `(1 - g)·e₀ = 0`. -/
lemma eminus_smul_Pplus_e0 : eminus • Pplus.e0 = 0 := by
  have h : eminus • Pplus.e0 = (2⁻¹ : ℂ) • (Pplus.e0 - g • Pplus.e0) := by
    rw [eminus, smul_assoc, sub_smul, one_smul]
  rw [h, Pplus.g_smul_e0, sub_self, smul_zero]

lemma xeminus_smul_Pplus_e0 : xeminus • Pplus.e0 = 0 := by
  rw [← x_mul_eminus, mul_smul, eminus_smul_Pplus_e0, smul_zero]

/-- `e₊` annihilates the generator of `P₋`: `g` acts as `-1` there, so `(1 + g)·e₀ = 0`. -/
lemma eplus_smul_Pminus_e0 : eplus • Pminus.e0 = 0 := by
  have h : eplus • Pminus.e0 = (2⁻¹ : ℂ) • (Pminus.e0 + g • Pminus.e0) := by
    rw [eplus, smul_assoc, add_smul, one_smul]
  rw [h, Pminus.g_smul_e0, add_neg_cancel, smul_zero]

lemma xeplus_smul_Pminus_e0 : xeplus • Pminus.e0 = 0 := by
  rw [← x_mul_eplus, mul_smul, eplus_smul_Pminus_e0, smul_zero]

@[simp] lemma iPlus_e0 : iPlus Pplus.e0 = eplus := by
  change Pplus.e0 0 • eplus + Pplus.e0 1 • xeplus = eplus
  rw [Pplus.e0_zero, Pplus.e0_one, one_smul, zero_smul, add_zero]

@[simp] lemma iMinus_e0 : iMinus Pminus.e0 = eminus := by
  change Pminus.e0 0 • eminus + Pminus.e0 1 • xeminus = eminus
  rw [Pminus.e0_zero, Pminus.e0_one, one_smul, zero_smul, add_zero]

lemma rPlus_iPlus (u : Pplus) : rPlus (iPlus u) = u :=
  LinearMap.congr_fun rPlus_comp_iPlus u

lemma rMinus_iMinus (v : Pminus) : rMinus (iMinus v) = v :=
  LinearMap.congr_fun rMinus_comp_iMinus v

/-- The retraction onto `P₊` kills the image of `P₋` in `A`. -/
lemma rPlus_iMinus (v : Pminus) : rPlus (iMinus v) = 0 := by
  have hiv : iMinus v = v 0 • eminus + v 1 • xeminus := rfl
  rw [rPlus, LinearMap.toSpanSingleton_apply, hiv, add_smul, smul_assoc, smul_assoc,
    eminus_smul_Pplus_e0, xeminus_smul_Pplus_e0, smul_zero, smul_zero, add_zero]

/-- The retraction onto `P₋` kills the image of `P₊` in `A`. -/
lemma rMinus_iPlus (u : Pplus) : rMinus (iPlus u) = 0 := by
  have hiu : iPlus u = u 0 • eplus + u 1 • xeplus := rfl
  rw [rMinus, LinearMap.toSpanSingleton_apply, hiu, add_smul, smul_assoc, smul_assoc,
    eplus_smul_Pminus_e0, xeplus_smul_Pminus_e0, smul_zero, smul_zero, add_zero]

/-! ### The isomorphism `P₊ × P₋ ≃ₗ[A] A` -/

/-- The `A`-linear map `P₊ × P₋ → A`, `(u, v) ↦ i₊ u + i₋ v`. -/
noncomputable def iProd : (Pplus × Pminus) →ₗ[A] A :=
  iPlus.comp (LinearMap.fst A Pplus Pminus) + iMinus.comp (LinearMap.snd A Pplus Pminus)

/-- The `A`-linear map `A → P₊ × P₋`, `a ↦ (a · e₀⁺, a · e₀⁻)`. -/
noncomputable def rProd : A →ₗ[A] (Pplus × Pminus) := rPlus.prod rMinus

@[simp] lemma iProd_apply (p : Pplus × Pminus) : iProd p = iPlus p.1 + iMinus p.2 := rfl

@[simp] lemma rProd_apply (a : A) : rProd a = (rPlus a, rMinus a) := rfl

lemma iProd_comp_rProd : iProd.comp rProd = LinearMap.id := by
  refine LinearMap.ext fun a => ?_
  change iPlus (rPlus a) + iMinus (rMinus a) = a
  rw [rPlus, rMinus, LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply,
    map_smul, map_smul, iPlus_e0, iMinus_e0, ← smul_add, eplus_add_eminus, smul_eq_mul, mul_one]

lemma rProd_comp_iProd : rProd.comp iProd = LinearMap.id := by
  refine LinearMap.ext fun p => ?_
  change (rPlus (iPlus p.1 + iMinus p.2), rMinus (iPlus p.1 + iMinus p.2)) = p
  rw [map_add, map_add, rPlus_iMinus, rMinus_iPlus, add_zero, zero_add, rPlus_iPlus,
    rMinus_iMinus]

/-- **The left regular module of `A` decomposes as `P₊ ⊕ P₋`.**

Both summands are indecomposable (`isIndecomposable_Pplus`, `isIndecomposable_Pminus`), so this
is *the* Krull-Schmidt decomposition of the regular module, and it is what makes `P₊` and `P₋`
projective. -/
noncomputable def regularEquivProd : (Pplus × Pminus) ≃ₗ[A] A :=
  LinearEquiv.ofLinear iProd rProd iProd_comp_rProd rProd_comp_iProd

@[simp] lemma regularEquivProd_apply (p : Pplus × Pminus) :
    regularEquivProd p = iPlus p.1 + iMinus p.2 := rfl

@[simp] lemma regularEquivProd_symm_apply (a : A) :
    regularEquivProd.symm a = (rPlus a, rMinus a) := rfl

/-! ### `A` is four-dimensional over `ℂ` -/

lemma Pplus.finrank_complex : Module.finrank ℂ Pplus = 2 := by
  change Module.finrank ℂ (Fin 2 → ℂ) = 2
  simp

lemma Pminus.finrank_complex : Module.finrank ℂ Pminus = 2 := by
  change Module.finrank ℂ (Fin 2 → ℂ) = 2
  simp

/-- The `ℂ`-linear form of the decomposition, obtained by restricting scalars. -/
noncomputable def regularEquivProdComplex : (Pplus × Pminus) ≃ₗ[ℂ] A :=
  regularEquivProd.restrictScalars ℂ

instance : FiniteDimensional ℂ A :=
  Module.Finite.equiv regularEquivProdComplex

/-- **`A` is four-dimensional over `ℂ`**, as asserted in the statement of Problem 9.3.2
(basis `1, g, x, gx`). Here it is read off from `A ≅ P₊ ⊕ P₋` with both summands of
dimension `2`. -/
theorem finrank_A : Module.finrank ℂ A = 4 := by
  rw [← regularEquivProdComplex.finrank_eq, Module.finrank_prod, Pplus.finrank_complex,
    Pminus.finrank_complex]

end RegularDecomposition

/-! ## Classification of the indecomposable projectives

This is the second part of Problem 9.3.2: `P₊` and `P₋` are *all* of the indecomposable
projectives. The statement is for finite dimensional modules over `ℂ` (equivalently, finitely
generated over `A`, since `A` is finite dimensional); the unrestricted statement needs
infinite-rank projective machinery the book does not use here.

The argument is the standard projective-cover one, already available in the project as
`Etingof.indecomposable_projective_iso_of_hom` (Fitting's lemma: two indecomposable finitely
generated projectives with nonzero `Hom` to the same simple are isomorphic). What this file
supplies is its inputs for this particular `A`:

* `A` is artinian, because `dim_ℂ A = 4` (`finrank_A`, from `A ≅ P₊ ⊕ P₋` above);
* a nonzero finite dimensional `Q` has a nonzero map to `S₊` or to `S₋`: take a maximal
  submodule, and identify the simple quotient by `nonempty_linearEquiv_splus_or_sminus`;
* `gSES : P₊ ↠ S₊` and `gSESm : P₋ ↠ S₋` are the matching nonzero maps out of the projectives.

The two cases are mutually exclusive (`pplus_not_iso_pminus`), so the classification is by
`Xor`, exactly as for the simples. -/

section ProjectiveClassification

instance isArtinianRing_A : IsArtinianRing A := isArtinian_of_tower ℂ inferInstance

/-- The socle vector of `P₋` is killed by `x` (as `x² = 0`). -/
@[simp] lemma Pminus.x_smul_e1 : x • Pminus.e1 = 0 := by
  rw [Pminus.x_smul]
  refine Pminus.ext fun i => ?_
  fin_cases i <;> simp

/-- `P₊` and `P₋` are not isomorphic. Every `A`-linear map `P₊ → P₋` is a multiple of `Tpm`,
which kills the socle: an `A`-linear `e : P₊ → P₋` sends `e₀` into the `+1`-eigenline `ℂ·e₁` of
`g`, and then `e e₁ = e (x · e₀) = x · e e₀ ∈ x · ℂ·e₁ = 0`, so `e` is not injective. -/
theorem pplus_not_iso_pminus : IsEmpty (Pplus ≃ₗ[A] Pminus) := by
  refine ⟨fun e => ?_⟩
  have h0 : e Pplus.e0 = (e Pplus.e0) 1 • Pminus.e1 :=
    Pminus.eq_smul_e1_of_g_smul_eq_self (Pplus.g_smul_apply_e0 e.toLinearMap)
  have h1 : e Pplus.e1 = 0 := by
    rw [← Pplus.x_smul_e0, map_smul, h0, smul_comm, Pminus.x_smul_e1, smul_zero]
  have h2 : Pplus.e1 = 0 := by
    have := e.injective (h1.trans (map_zero e).symm)
    exact this
  have h3 : (Pplus.e1 : Pplus) 1 = 0 := by rw [h2]; rfl
  rw [Pplus.e1_one] at h3
  exact one_ne_zero h3

lemma gSES_ne_zero : gSES ≠ 0 := by
  intro h
  have h1 : gSES Pplus.e0 = 0 := by rw [h]; rfl
  rw [gSES_apply, Pplus.e0_zero] at h1
  exact one_ne_zero (α := ℂ) h1

lemma gSESm_ne_zero : gSESm ≠ 0 := by
  intro h
  have h1 : gSESm Pminus.e0 = 0 := by rw [h]; rfl
  rw [gSESm_apply, Pminus.e0_zero] at h1
  exact one_ne_zero (α := ℂ) h1

/-- Composing the quotient map by a proper submodule with an isomorphism of the quotient never
gives the zero map: the quotient map is onto and the submodule is not everything. -/
lemma comp_mkQ_ne_zero {Q : Type u} [AddCommGroup Q] [Module A Q] {T : Type v} [AddCommGroup T]
    [Module A T] (N : Submodule A Q) (hN : N ≠ ⊤) (e : (Q ⧸ N) ≃ₗ[A] T) :
    e.toLinearMap.comp N.mkQ ≠ 0 := by
  intro h
  refine hN (Submodule.eq_top_iff'.mpr fun q => ?_)
  have h1 : e (N.mkQ q) = 0 := by have := LinearMap.congr_fun h q; simpa using this
  have h2 : N.mkQ q = 0 := e.injective (h1.trans (map_zero e).symm)
  exact (Submodule.Quotient.mk_eq_zero N).mp h2

/-- Any nonzero finite dimensional `A`-module has a nonzero `A`-linear map to `S₊` or to `S₋`:
it has a maximal submodule, and the resulting simple quotient is one of the two simples. -/
theorem exists_nonzero_hom_to_simple (Q : Type u) [AddCommGroup Q] [Module ℂ Q] [Module A Q]
    [IsScalarTower ℂ A Q] [FiniteDimensional ℂ Q] [Nontrivial Q] :
    (∃ φ : Q →ₗ[A] Splus, φ ≠ 0) ∨ (∃ φ : Q →ₗ[A] Sminus, φ ≠ 0) := by
  haveI : Module.Finite A Q := Module.Finite.of_restrictScalars_finite ℂ A Q
  obtain ⟨N, hN⟩ := Etingof.Theorem921.exists_isCoatom_submodule (R := A) (M := Q)
  haveI : IsSimpleModule A (Q ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  rcases nonempty_linearEquiv_splus_or_sminus (Q ⧸ N) with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨e.toLinearMap.comp N.mkQ, comp_mkQ_ne_zero N hN.1 e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨e.toLinearMap.comp N.mkQ, comp_mkQ_ne_zero N hN.1 e⟩

/-- **Every finite dimensional indecomposable projective `A`-module is `P₊` or `P₋`.**

This is the converse half of the second part of Problem 9.3.2: together with
`projective_Pplus`, `projective_Pminus`, `isIndecomposable_Pplus` and
`isIndecomposable_Pminus`, it says the indecomposable projectives are exactly `P₊` and `P₋`. -/
theorem indecomposable_projective_classification (Q : Type u) [AddCommGroup Q] [Module ℂ Q]
    [Module A Q] [IsScalarTower ℂ A Q] [FiniteDimensional ℂ Q] [Module.Projective A Q]
    (hQ : Etingof.IsIndecomposable A Q) :
    Nonempty (Q ≃ₗ[A] Pplus) ∨ Nonempty (Q ≃ₗ[A] Pminus) := by
  haveI : Nontrivial Q := hQ.1
  rcases exists_nonzero_hom_to_simple Q with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact Or.inl (Etingof.indecomposable_projective_iso_of_hom (k := ℂ) hQ
      isIndecomposable_Pplus φ hφ gSES gSES_ne_zero)
  · exact Or.inr (Etingof.indecomposable_projective_iso_of_hom (k := ℂ) hQ
      isIndecomposable_Pminus φ hφ gSESm gSESm_ne_zero)

/-- **The indecomposable projective `A`-modules are exactly `P₊` and `P₋`** — every finite
dimensional indecomposable projective is isomorphic to exactly one of them.

This is the second part of Problem 9.3.2, in the same `Xor` form as
`simple_module_classification` for the first part. -/
theorem indecomposable_projective_classification_xor (Q : Type u) [AddCommGroup Q] [Module ℂ Q]
    [Module A Q] [IsScalarTower ℂ A Q] [FiniteDimensional ℂ Q] [Module.Projective A Q]
    (hQ : Etingof.IsIndecomposable A Q) :
    Xor (Nonempty (Q ≃ₗ[A] Pplus)) (Nonempty (Q ≃ₗ[A] Pminus)) := by
  have hnot : ¬(Nonempty (Q ≃ₗ[A] Pplus) ∧ Nonempty (Q ≃ₗ[A] Pminus)) := by
    rintro ⟨⟨e₁⟩, ⟨e₂⟩⟩
    exact pplus_not_iso_pminus.false (e₁.symm.trans e₂)
  rcases indecomposable_projective_classification Q hQ with h | h
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩

/-- **Problem 9.3.2, part 2, indexed by the family `Pfam = ![P₊, P₋]`.** Every finite
dimensional indecomposable projective is isomorphic to `Pfam i` for exactly one `i`. This is the
same family the Cartan matrix of part 3 is computed over, so parts 2 and 3 speak about the same
two objects. -/
theorem existsUnique_index_of_indecomposable_projective (Q : Type u) [AddCommGroup Q]
    [Module ℂ Q] [Module A Q] [IsScalarTower ℂ A Q] [FiniteDimensional ℂ Q]
    [Module.Projective A Q] (hQ : Etingof.IsIndecomposable A Q) :
    ∃! i : Fin 2, Nonempty (Q ≃ₗ[A] Pfam i) := by
  rcases indecomposable_projective_classification_xor Q hQ with ⟨h, hne⟩ | ⟨h, hne⟩
  · refine ⟨0, h, fun j hj => ?_⟩
    fin_cases j
    · rfl
    · exact absurd hj hne
  · refine ⟨1, h, fun j hj => ?_⟩
    fin_cases j
    · exact absurd hj hne
    · rfl

/-! ### The classification is not vacuous

Its hypotheses are satisfied by the two modules it classifies: `P₊` and `P₋` really are finite
dimensional indecomposable projectives, so instance resolution finds `FiniteDimensional ℂ`,
`Module.Projective A` and `IsScalarTower ℂ A` for them, and the theorem returns the expected
index. -/

theorem indecomposable_projective_classification_Pplus :
    Xor (Nonempty (Pplus ≃ₗ[A] Pplus)) (Nonempty (Pplus ≃ₗ[A] Pminus)) :=
  indecomposable_projective_classification_xor Pplus isIndecomposable_Pplus

theorem indecomposable_projective_classification_Pminus :
    Xor (Nonempty (Pminus ≃ₗ[A] Pplus)) (Nonempty (Pminus ≃ₗ[A] Pminus)) :=
  indecomposable_projective_classification_xor Pminus isIndecomposable_Pminus

end ProjectiveClassification

end Etingof.Problem932

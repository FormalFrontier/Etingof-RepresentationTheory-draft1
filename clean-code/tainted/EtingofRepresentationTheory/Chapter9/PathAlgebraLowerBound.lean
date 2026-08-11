import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import EtingofRepresentationTheory.Chapter9.Definition9_4_3
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Span.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Problem 9.4.6 (i), lower bound: the path algebra of a quiver with an edge is not semisimple

The path algebra `A := PathAlgebra k Q` of a quiver with at least one edge has homological
dimension exactly `1`. The upper bound `HasHomologicalDimensionLE A 1` is the standard
resolution (`Chapter9/Problem9_4_6.lean`). This file supplies the matching lower bound

```
not_hasHomologicalDimensionLE_zero_pathAlgebra :
  ¬ HasHomologicalDimensionLE A 0
```

i.e. `A` is not semisimple: it has a module of positive projective dimension.

## The augmentation module `S_b`

Fix the target vertex `b` of an edge. The augmentation at `b` is the `k`-algebra
homomorphism `ε_b : A → k`, `a ↦ a ⟨b, b, nil⟩` (the coefficient of the trivial path at `b`).
Multiplicativity is the statement that a product of basis paths equals the trivial path `e_b`
only when both factors are `e_b` (`comp_eq_some_nil_iff`). Pulling the regular `k`-module
back along `ε_b` gives the one-dimensional augmentation module `S_b = k` on which every
arrow acts as `0` and `e_b` acts as the identity, the simple module at vertex `b`.

## Why `S_b` is not projective (the template)

Mirror `not_hasHomologicalDimensionLE_zero_polynomial` (`Chapter9/Example9_4_4.lean`). If
`A` had homological dimension `0`, `S_b` would be projective, so the surjection
`A ↠ S_b`, `p ↦ p • 1`, would split by an `A`-linear section `s : S_b → A`. Writing `x` for
the chosen edge `a ⟶ b`, `x` acts as `0` on `S_b`, so `x · s(1) = s(x • 1) = 0` in `A`. But
the coefficient of the basis path `x` in `x · s(1)` equals the coefficient of `e_b` in `s(1)`
(`arrow_mul_apply_arrow`), which is `ε_b(s(1)) = 1` because `s` is a section. So
`x · s(1) ≠ 0`, a contradiction.
-/

universe u

open Etingof CategoryTheory

namespace Etingof.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

/-- **A product of basis paths is the trivial path `e_b` iff both factors are `e_b`.** The
composite `x.comp y` equals the length-`0` path `⟨b, b, nil⟩` precisely when `x` and `y` are
both that trivial path: concatenation adds lengths, so a length-`0` result forces both factors
to have length `0`, and the endpoint bookkeeping pins them to `b`. -/
theorem comp_eq_some_nil_iff (x y : QuiverPathIndex Q) (b : Q) :
    x.comp y = some ⟨b, b, Quiver.Path.nil⟩ ↔
      x = ⟨b, b, Quiver.Path.nil⟩ ∧ y = ⟨b, b, Quiver.Path.nil⟩ := by
  obtain ⟨xa, xb, xp⟩ := x
  obtain ⟨ya, yb, yq⟩ := y
  constructor
  · intro h
    rw [QuiverPathIndex.comp] at h
    split at h
    · rename_i hbc
      subst hbc
      rw [Option.some.injEq] at h
      -- `h : ⟨xa, yb, xp.comp yq⟩ = ⟨b, b, nil⟩`
      have hxa : xa = b := congrArg Sigma.fst h
      have hyb : yb = b := congrArg (fun z => z.2.1) h
      -- length bookkeeping: `(xp.comp yq).length = 0`
      have hlen : (xp.comp yq).length = 0 := by
        have := congrArg (fun z => z.2.2.length) h
        simpa using this
      rw [Quiver.Path.length_comp] at hlen
      have hxl : xp.length = 0 := by omega
      have hyl : yq.length = 0 := by omega
      have hxbb : xb = b := (Quiver.Path.eq_of_length_zero xp hxl).symm.trans hxa
      subst xa; subst yb; subst xb
      rw [Quiver.Path.eq_nil_of_length_zero xp hxl, Quiver.Path.eq_nil_of_length_zero yq hyl]
      exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · rintro ⟨hx, hy⟩
    rw [hx, hy, QuiverPathIndex.comp_eq_some, Quiver.Path.nil_comp]

/-- **A basis path absorbs a trivial right factor onto itself iff that factor is the trivial path
at its target.** `p.comp z = some p` exactly when `z = ⟨tgt p, tgt p, nil⟩`. -/
theorem comp_eq_some_self_iff (p z : QuiverPathIndex Q) :
    p.comp z = some p ↔ z = ⟨p.2.1, p.2.1, Quiver.Path.nil⟩ := by
  obtain ⟨pa, pb, pp⟩ := p
  obtain ⟨za, zb, zq⟩ := z
  constructor
  · intro h
    rw [QuiverPathIndex.comp] at h
    split at h
    · rename_i hbc
      subst hbc
      rw [Option.some.injEq] at h
      -- `h : ⟨pa, zb, pp.comp zq⟩ = ⟨pa, pb, pp⟩`   (`zq : Path pb zb`)
      have hzb : zb = pb := congrArg (fun w => w.2.1) h
      have hlen : (pp.comp zq).length = pp.length := by
        have := congrArg (fun w => w.2.2.length) h
        simpa using this
      rw [Quiver.Path.length_comp] at hlen
      have hzl : zq.length = 0 := by omega
      subst zb
      rw [Quiver.Path.eq_nil_of_length_zero zq hzl]
    · exact absurd h (by simp)
  · intro hz
    rw [hz, QuiverPathIndex.comp_eq_some, Quiver.Path.comp_nil]

/-! ## Coefficient extraction

`A = QuiverPathIndex Q →₀ k` as a `k`-module, but `PathAlgebra` is a semireducible `def` with no
`FunLike` instance, so `a x` does not elaborate for `a : A`. We access coefficients through the
`k`-linear functional `coeffAt x = Finsupp.lapply x`, which applies cleanly to products. -/

/-- The coefficient of `a : A` at a basis path `x`, as a `k`-linear functional. -/
noncomputable def coeffAt (x : QuiverPathIndex Q) : PathAlgebra k Q →ₗ[k] k :=
  Finsupp.lapply x

open Classical in
theorem coeffAt_single (x y : QuiverPathIndex Q) (c : k) :
    coeffAt x (Finsupp.single y c) = if y = x then c else 0 :=
  Finsupp.single_apply

open Classical in
theorem coeffAt_compSingle (x y z : QuiverPathIndex Q) :
    coeffAt z (compSingle x y : PathAlgebra k Q) = if x.comp y = some z then (1 : k) else 0 := by
  rw [compSingle]
  cases h : x.comp y with
  | none => simp
  | some w => rw [Option.elim_some, coeffAt_single]; simp

/-! ## The augmentation ring homomorphism `ε_b : A → k` -/

/-- The augmentation of the path algebra at a vertex `b`: the coefficient of the trivial path
`e_b = ⟨b, b, nil⟩`. As a `k`-algebra homomorphism `A → k`, it sends every arrow (indeed every
path of positive length) to `0` and `e_b` to `1`. -/
noncomputable def augHom [Fintype Q] (b : Q) : PathAlgebra k Q →+* k where
  toFun a := coeffAt ⟨b, b, Quiver.Path.nil⟩ a
  map_one' := by
    rw [one_def, map_sum, Finset.sum_eq_single b]
    · rw [coeffAt_single, if_pos rfl]
    · intro i _ hib
      rw [coeffAt_single, if_neg]
      intro hcon
      exact hib (congrArg Sigma.fst hcon)
    · intro hb; exact absurd (Finset.mem_univ b) hb
  map_mul' a a' := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [add_mul, map_add, map_add, hf, hg, add_mul]
    | single x c =>
      induction a' using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => rw [mul_add, map_add, map_add, hf, hg, mul_add]
      | single y d =>
        rw [single_mul_single, map_smul, coeffAt_compSingle, coeffAt_single, coeffAt_single,
          smul_eq_mul]
        by_cases hx : x = (⟨b, b, Quiver.Path.nil⟩ : QuiverPathIndex Q) <;>
          by_cases hy : y = (⟨b, b, Quiver.Path.nil⟩ : QuiverPathIndex Q) <;>
          simp [hx, hy, comp_eq_some_nil_iff]
  map_zero' := by simp
  map_add' a a' := by simp

@[simp] theorem augHom_apply [Fintype Q] (b : Q) (a : PathAlgebra k Q) :
    augHom b a = coeffAt ⟨b, b, Quiver.Path.nil⟩ a := rfl

/-- The augmentation of the basis element of an edge `e : a ⟶ b` vanishes: a length-`1` path is
not the trivial path `e_b`. -/
theorem augHom_ofPath_arrow [Fintype Q] {a b : Q} (e : a ⟶ b) :
    augHom b (ofPath (⟨a, b, e.toPath⟩ : QuiverPathIndex Q)) = (0 : k) := by
  rw [augHom_apply, ofPath, coeffAt_single]
  apply if_neg
  intro hcon
  have : (e.toPath).length = (Quiver.Path.nil : Quiver.Path b b).length :=
    congrArg (fun w => w.2.2.length) hcon
  rw [Quiver.Path.length_nil, Quiver.Path.length_toPath] at this
  exact one_ne_zero this

/-- **Coefficient extraction.** For an edge `e : a ⟶ b`, the coefficient of the basis path
`⟨a, b, e.toPath⟩` in the product `ofPath ⟨a, b, e.toPath⟩ * w` equals the `e_b`-coefficient of
`w`. This is the key computation behind the contradiction: left-multiplying by the edge shifts
the trivial-path coefficient onto the edge coefficient. -/
theorem arrow_mul_apply_arrow {a b : Q} (e : a ⟶ b) (w : PathAlgebra k Q) :
    coeffAt (⟨a, b, e.toPath⟩ : QuiverPathIndex Q) (ofPath ⟨a, b, e.toPath⟩ * w)
      = coeffAt (⟨b, b, Quiver.Path.nil⟩ : QuiverPathIndex Q) w := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [mul_add, map_add, map_add, hf, hg]
  | single z c =>
    rw [ofPath, single_mul_single, one_mul, map_smul, coeffAt_compSingle, coeffAt_single,
      smul_eq_mul]
    by_cases hz : z = (⟨b, b, Quiver.Path.nil⟩ : QuiverPathIndex Q) <;>
      simp [hz, comp_eq_some_self_iff]

/-! ## The augmentation module `S_b`

`PathAlgebra k Q` lives in `Type (u+1)` (the quiver path type bumps the universe), so the
homological-dimension predicate quantifies over `Type (u+1)`-modules. We therefore realise the
one-dimensional augmentation module on the `ULift`ed carrier `ULift.{u+1} k`. -/

/-- The augmentation module `S_b` at a vertex `b`: the field `k` (universe-lifted to match
`PathAlgebra k Q`) regarded as a left `A = PathAlgebra k Q`-module through the augmentation
`ε_b`, `a • v = ε_b(a) · v`. Only the trivial path at `b` acts as the identity; every arrow acts
as `0`. It is the simple module at vertex `b`, and its positive projective dimension witnesses
non-semisimplicity of `A`. -/
def augModule (k : Type u) (Q : Type u) [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]
    [Fintype Q] (_b : Q) : Type (u + 1) := ULift.{u + 1} k

noncomputable instance [Fintype Q] (b : Q) : AddCommGroup (augModule k Q b) :=
  inferInstanceAs (AddCommGroup (ULift.{u + 1} k))

noncomputable instance [Fintype Q] (b : Q) : Module k (augModule k Q b) :=
  inferInstanceAs (Module k (ULift.{u + 1} k))

noncomputable instance [Fintype Q] (b : Q) : Module (PathAlgebra k Q) (augModule k Q b) :=
  Module.compHom (augModule k Q b) (augHom b)

theorem augModule_smul [Fintype Q] (b : Q) (a : PathAlgebra k Q) (v : augModule k Q b) :
    a • v = augHom b a • v := rfl

/-- The action on the augmentation module, read off on the underlying scalar: `(a • v).down`
is `ε_b(a) · v.down`. -/
theorem augModule_down_smul [Fintype Q] (b : Q) (a : PathAlgebra k Q) (v : augModule k Q b) :
    (a • v).down = augHom b a * v.down := by
  rw [augModule_smul]; rfl

/-- The distinguished generator `1 : k` of the augmentation module. -/
def augGen [Fintype Q] (b : Q) : augModule k Q b := ULift.up (1 : k)

@[simp] theorem augGen_down [Fintype Q] (b : Q) : (augGen (k := k) (Q := Q) b).down = 1 := rfl

/-- An arrow `e : a ⟶ b` acts as `0` on the augmentation module `S_b`: its augmentation is `0`. -/
theorem ofPath_arrow_smul_augModule [Fintype Q] {a b : Q} (e : a ⟶ b) (v : augModule k Q b) :
    (ofPath ⟨a, b, e.toPath⟩ : PathAlgebra k Q) • v = 0 := by
  apply ULift.ext
  rw [augModule_down_smul, augHom_ofPath_arrow e, zero_mul]
  rfl

end Etingof.PathAlgebra

namespace Etingof.Problem946

open Etingof.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]

/-- **Problem 9.4.6 (i), lower bound.** The path algebra of a quiver with at least one edge is
not semisimple: it does not have homological dimension `0`.

The augmentation module `S_b` at the target `b` of an edge `x : a ⟶ b` is not projective. If it
were, the surjection `A ↠ S_b`, `p ↦ p • 1`, would split by a section `s`; then `x • 1 = 0`
forces `x · s(1) = 0` in `A`, yet the `x`-coefficient of `x · s(1)` is the `e_b`-coefficient of
`s(1)`, which is `1` because `s` is a section, a contradiction. -/
theorem not_hasHomologicalDimensionLE_zero_pathAlgebra
    (hQ : ∃ a b : Q, Nonempty (a ⟶ b)) :
    ¬ Etingof.HasHomologicalDimensionLE (Etingof.PathAlgebra k Q) 0 := by
  intro hall
  obtain ⟨a, b, ⟨e⟩⟩ := hQ
  -- The augmentation module `S_b`, as a `ModuleCat` object.
  let MA := ModuleCat.of (PathAlgebra k Q) (augModule k Q b)
  -- Under homological dimension `0` it is projective.
  have hpd : CategoryTheory.HasProjectiveDimensionLE MA 0 := hall MA
  haveI hproj : CategoryTheory.Projective MA :=
    projective_iff_hasProjectiveDimensionLT_one.mpr hpd
  haveI hmod : Module.Projective (PathAlgebra k Q) (augModule k Q b) :=
    (IsProjective.iff_projective (augModule k Q b)).mpr hproj
  -- The surjection `A ↠ S_b`, `p ↦ p • 1`.
  let surj := LinearMap.toSpanSingleton (PathAlgebra k Q) (augModule k Q b) (augGen b)
  have hsurj : Function.Surjective surj := by
    intro v
    refine ⟨Finsupp.single ⟨b, b, Quiver.Path.nil⟩ v.down, ?_⟩
    apply ULift.ext
    simp only [surj, LinearMap.toSpanSingleton_apply, augModule_down_smul, augHom_apply,
      coeffAt_single, if_pos, augGen_down, mul_one]
  -- Projectivity yields an `A`-linear section `s`.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property surj LinearMap.id hsurj
  -- The section value `w := s 1`.
  set w : PathAlgebra k Q := s (augGen b) with hw_def
  -- `s` is a section: `surj (s 1) = 1`, i.e. `ε_b(w) = 1`.
  have hsection : augHom b w = 1 := by
    have hcf := LinearMap.congr_fun hs (augGen b)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hcf
    -- `surj w = augGen b`; read off the underlying scalar.
    have hdown := congrArg ULift.down hcf
    simp only [surj, LinearMap.toSpanSingleton_apply, augModule_down_smul, augGen_down,
      mul_one] at hdown
    exact hdown
  -- The edge `x` acts as `0` on `S_b`, so `x · w = 0` in `A`.
  have hzero : (ofPath ⟨a, b, e.toPath⟩ : PathAlgebra k Q) * w = 0 := by
    have h1 := s.map_smul (ofPath (⟨a, b, e.toPath⟩ : QuiverPathIndex Q)) (augGen b)
    rw [ofPath_arrow_smul_augModule e (augGen b), map_zero] at h1
    -- `h1 : 0 = ofPath x • w`; the regular-module action is multiplication.
    rw [← smul_eq_mul]
    exact h1.symm
  -- But the `x`-coefficient of `x · w` is `ε_b(w) = 1 ≠ 0`.
  have hne : coeffAt (⟨a, b, e.toPath⟩ : QuiverPathIndex Q) (ofPath ⟨a, b, e.toPath⟩ * w) = 1 := by
    rw [arrow_mul_apply_arrow e w, ← augHom_apply]; exact hsection
  rw [hzero, map_zero] at hne
  exact one_ne_zero hne.symm

end Etingof.Problem946

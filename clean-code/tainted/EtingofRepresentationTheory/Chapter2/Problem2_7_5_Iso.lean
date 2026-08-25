import EtingofRepresentationTheory.Chapter2.Problem2_7_5_Family

/-!
# Problem 2.7.5(c): the isomorphism criterion for the family `V(α,β)`

`Problem2_7_5_Family.lean` constructs, for a primitive root of unity `q` of order `n = orderOf q`,
the `n`-dimensional `qWeylAlgebra ℂ q`-module `V(α,β)` with

* `x` acting as the twisted cyclic shift `Xlin`: `x·eⱼ = e_{j+1}`, `x·e_{n-1} = α·e₀`;
* `y` acting diagonally by `Ylin`: `y·eⱼ = β·qʲ·eⱼ`,

and computes its central character `(α, βⁿ)`. This file proves that the central character is a
*complete* invariant of the family:

`V(α,β) ≅ V(α',β')` **iff** `α = α'` and `βⁿ = β'ⁿ`.

## The intertwiner

The backward direction needs an explicit isomorphism. If `βⁿ = β'ⁿ` then `β/β'` is an `n`-th root
of unity, hence a power `qᵐ` of `q` (which is primitive), so `β = β'·qᵐ`. The intertwiner is then
simply the operator `Xᵐ` itself:

* it commutes with `x` because `x` commutes with its own powers;
* it carries the `y`-action of `V(α,β)` to that of `V(α,β')` because conjugating `y` by `x` rescales
  it by `q` (the defining relation `y x = q·x y`), so conjugating by `xᵐ` rescales `β` to `β·q^{-m}
  = β'`.

Concretely `Xᵐ` shifts the index by `m`, and the diagonal `y`-weights `β·qʲ` of `V(α,β)` are exactly
the weights `β'·qʲ` of `V(α,β')` read off `m` steps later. No extra diagonal rescaling is needed.

## Distinguishing the module structures

`V(α,β)` and `V(α',β')` have the *same* underlying space `Fin n → ℂ`, so a bare
`Module (qWeylAlgebra ℂ q) (Fin n → ℂ)` cannot carry both actions at once. `Fam q α β` is a type
synonym for `Fin (orderOf q) → ℂ` with `α, β` as phantom parameters; it lets the two module
structures be genuine instances on genuinely different types, so `≃ₗ[qWeylAlgebra ℂ q]` elaborates
with the intended actions on each side.

## Main results

* `Etingof.QWeyl.toEnd_conj` — a unit intertwining two pairs of generator data conjugates the two
  lifts `qWeylAlgebra k q →ₐ[k] End k V` into each other.
* `Etingof.Problem2_7_5.Fam` — the carrier of `V(α,β)`, with its `qWeylAlgebra ℂ q`-module instance.
* `Etingof.Problem2_7_5.famEquivOfPow` — the explicit isomorphism `V(α,β) ≃ V(α,β')` from `Xᵐ`.
* `Etingof.Problem2_7_5.fam_nonempty_linearEquiv_iff` — **the classification**:
  `Nonempty (V(α,β) ≃ₗ V(α',β')) ↔ α = α' ∧ βⁿ = β'ⁿ`.
-/

/-! ## Conjugating the universal lift -/

namespace Etingof.QWeyl

open Etingof Module

variable {k : Type*} [CommRing k] (q : kˣ)
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Conjugating both generator operators by a unit `E` conjugates every monomial operator
`XⁱYʲ`. -/
theorem op_conj (X Y E : (Module.End k V)ˣ) (i j : ℤ) :
    op (E * X * E⁻¹) (E * Y * E⁻¹) i j = ↑E * op X Y i j * ↑E⁻¹ := by
  have hconj : ∀ u : (Module.End k V)ˣ, E * u * E⁻¹ = MulAut.conj E u := fun _ => rfl
  have key : (E * X * E⁻¹) ^ i * (E * Y * E⁻¹) ^ j = E * (X ^ i * Y ^ j) * E⁻¹ := by
    rw [hconj X, hconj Y, ← map_zpow, ← map_zpow, ← map_mul, hconj]
  have hval := congrArg Units.val key
  simpa [op, mul_assoc] using hval

/-- **Conjugation of the universal lift.** If a unit `E` intertwines the generator data
`(X, Y)` with `(X', Y')`, then it conjugates the lift built from `(X, Y)` into the lift built
from `(X', Y')`. This is the operator-level content of "`E` is a module isomorphism". -/
theorem toEnd_conj (X Y X' Y' E : (Module.End k V)ˣ)
    (hrel : (↑Y : Module.End k V) * ↑X = (q : k) • (↑X * ↑Y))
    (hrel' : (↑Y' : Module.End k V) * ↑X' = (q : k) • (↑X' * ↑Y'))
    (hX : E * X = X' * E) (hY : E * Y = Y' * E) (a : qWeylAlgebra k q) :
    toEnd q X' Y' hrel' a = ↑E * toEnd q X Y hrel a * ↑E⁻¹ := by
  have hX' : X' = E * X * E⁻¹ := by rw [hX, mul_inv_cancel_right]
  have hY' : Y' = E * Y * E⁻¹ := by rw [hY, mul_inv_cancel_right]
  subst hX'
  subst hY'
  have key : (toEnd q (E * X * E⁻¹) (E * Y * E⁻¹) hrel').toLinearMap
      = (LinearMap.mulRight k (↑E⁻¹ : Module.End k V)).comp
          ((LinearMap.mulLeft k (↑E : Module.End k V)).comp
            (toEnd q X Y hrel).toLinearMap) := by
    refine (basis q).ext fun p => ?_
    simp only [basis_apply, AlgHom.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, LinearMap.mulLeft_apply, toEnd_qWeylMono]
    exact op_conj X Y E p.1 p.2
  exact DFunLike.congr_fun key a

end Etingof.QWeyl

/-! ## The isomorphism criterion -/

namespace Etingof.Problem2_7_5

open Etingof Module

/-! ### `q`-power bookkeeping on `Fin N` -/

section QPow

variable (q : ℂˣ) (N : ℕ) [NeZero N]

/-- The `q`-powers attached to indices are multiplicative for subtraction in `Fin N`: the
exponents only matter modulo `N`, and `q` has order `N`. -/
theorem q_pow_val_sub (hqorder : orderOf q = N) (k s : Fin N) :
    (q : ℂ) ^ ((k - s : Fin N) : ℕ) * (q : ℂ) ^ ((s : Fin N) : ℕ)
      = (q : ℂ) ^ ((k : Fin N) : ℕ) := by
  have hmod : ((k - s : Fin N) : ℕ) + ((s : Fin N) : ℕ) ≡ ((k : Fin N) : ℕ) [MOD N] := by
    have h : ((k - s) + s : Fin N) = k := sub_add_cancel k s
    calc ((k - s : Fin N) : ℕ) + ((s : Fin N) : ℕ)
        ≡ (((k - s : Fin N) : ℕ) + ((s : Fin N) : ℕ)) % N [MOD N] := (Nat.mod_modEq _ _).symm
      _ = (((k - s) + s : Fin N) : ℕ) := (Fin.val_add _ _).symm
      _ = ((k : Fin N) : ℕ) := by rw [h]
  have huq : q ^ (((k - s : Fin N) : ℕ) + ((s : Fin N) : ℕ)) = q ^ ((k : Fin N) : ℕ) := by
    rw [pow_eq_pow_iff_modEq, hqorder]; exact hmod
  have hval := congrArg Units.val huq
  push_cast at hval
  simpa [pow_add] using hval

/-- The `m`-step shift has `q`-power `qᵐ`: its index is `m % N`, and `qᴺ = 1`. -/
theorem q_pow_val_nsmul_one (hqorder : orderOf q = N) (m : ℕ) :
    (q : ℂ) ^ (((m • (1 : Fin N) : Fin N) : Fin N) : ℕ) = (q : ℂ) ^ m := by
  rw [val_nsmul_one]
  have huq : q ^ (m % N) = q ^ m := by
    rw [pow_eq_pow_iff_modEq, hqorder]; exact Nat.mod_modEq m N
  have hval := congrArg Units.val huq
  push_cast at hval
  simpa using hval

omit [NeZero N] in
/-- `q` is a primitive `N`-th root of unity exactly because `N` is its order. -/
theorem isPrimitiveRoot_q (hqorder : orderOf q = N) : IsPrimitiveRoot q N :=
  hqorder ▸ IsPrimitiveRoot.orderOf q

/-- **The shift parameter.** If `βᴺ = β'ᴺ` then `β/β'` is an `N`-th root of unity, hence a power
of the primitive root `q`: there is `m` with `β = β'·qᵐ`. -/
theorem exists_pow_shift (β β' : ℂˣ) (hqorder : orderOf q = N)
    (hβ : (β : ℂ) ^ N = (β' : ℂ) ^ N) : ∃ m : ℕ, (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m := by
  have hprim : IsPrimitiveRoot ((q : ℂ)) N :=
    IsPrimitiveRoot.coe_units_iff.mpr (isPrimitiveRoot_q q N hqorder)
  have hξ : ((β : ℂ) / (β' : ℂ)) ^ N = 1 := by
    rw [div_pow, hβ, div_self (pow_ne_zero _ β'.ne_zero)]
  obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one hξ
  exact ⟨m, by rw [hm, mul_div_cancel₀ _ β'.ne_zero]⟩

end QPow

/-! ### `Xᵐ` intertwines the `y`-actions -/

section Intertwine

variable (q α β β' : ℂˣ) (N : ℕ) [NeZero N]

/-- With `β = β'·qᵐ`, the `y`-weight of `V(α,β)` at the index `m` steps back is the `y`-weight of
`V(α,β')` at the index itself. This is the whole content of the intertwining property. -/
theorem wY_shift (hqorder : orderOf q = N) (m : ℕ) (hβ : (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m)
    (k : Fin N) : wY q β N (k - m • (1 : Fin N)) = wY q β' N k := by
  have h := q_pow_val_sub q N hqorder k (m • (1 : Fin N))
  unfold wY
  rw [hβ, ← q_pow_val_nsmul_one q N hqorder m]
  calc ((β' : ℂ) * (q : ℂ) ^ (((m • (1 : Fin N) : Fin N) : Fin N) : ℕ))
        * (q : ℂ) ^ ((k - m • (1 : Fin N) : Fin N) : ℕ)
      = (β' : ℂ) * ((q : ℂ) ^ ((k - m • (1 : Fin N) : Fin N) : ℕ)
          * (q : ℂ) ^ (((m • (1 : Fin N) : Fin N) : Fin N) : ℕ)) := by ring
    _ = (β' : ℂ) * (q : ℂ) ^ ((k : Fin N) : ℕ) := by rw [h]

/-- **The intertwining relation.** When `β = β'·qᵐ`, the operator `Xᵐ` carries the `y`-action of
`V(α,β)` to the `y`-action of `V(α,β')`. -/
theorem Xlin_pow_mul_Ylin (hqorder : orderOf q = N) (m : ℕ)
    (hβ : (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m) :
    (Xlin α N ^ m) * (Ylin q β N) = (Ylin q β' N) * (Xlin α N ^ m) := by
  refine LinearMap.ext fun f => ?_
  funext k
  simp only [Module.End.mul_apply, Ylin, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  rw [Xlin_pow_apply, Xlin_pow_apply, ← wY_shift q β β' N hqorder m hβ k]
  simp only [smul_eq_mul]
  ring

/-- The unit-level form of `Xlin_pow_mul_Ylin`. -/
theorem Xunit_pow_mul_Yunit (hqorder : orderOf q = N) (m : ℕ)
    (hβ : (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m) :
    (Xunit α N ^ m) * (Yunit q β N) = (Yunit q β' N) * (Xunit α N ^ m) := by
  refine Units.ext ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Xunit_val, Yunit_val]
  exact Xlin_pow_mul_Ylin q α β β' N hqorder m hβ

/-- `Xᵐ` commutes with `X`: the `x`-action is preserved on the nose. -/
theorem Xunit_pow_mul_Xunit (m : ℕ) :
    (Xunit α N ^ m) * (Xunit α N) = (Xunit α N) * (Xunit α N ^ m) :=
  (Commute.refl (Xunit α N)).pow_left m

end Intertwine

/-! ### The carrier `Fam q α β` -/

section Carrier

variable (q α β : ℂˣ)

/-- The carrier of the classifying module `V(α,β)`: a type synonym for `Fin (orderOf q) → ℂ`.

The parameters `α` and `β` are phantom — they do not affect the underlying space. Their role is to
separate the `qWeylAlgebra ℂ q`-module structures of `V(α,β)` and `V(α',β')`, which would otherwise
be two competing instances on one and the same type. -/
def Fam (_q _α _β : ℂˣ) : Type := Fin (orderOf _q) → ℂ

instance : AddCommGroup (Fam q α β) := inferInstanceAs (AddCommGroup (Fin (orderOf q) → ℂ))

instance : Module ℂ (Fam q α β) := inferInstanceAs (Module ℂ (Fin (orderOf q) → ℂ))

variable [NeZero (orderOf q)]

/-- The family carrier is nontrivial because the nonzero order of `q` gives an index. -/
instance : Nontrivial (Fam q α β) := inferInstanceAs (Nontrivial (Fin (orderOf q) → ℂ))

/-- The `qWeylAlgebra ℂ q`-action on `V(α,β)`, transported from `famModule`. -/
noncomputable instance famQWeylModule : Module (qWeylAlgebra ℂ q) (Fam q α β) :=
  famModule q α β (orderOf q) rfl

/-- The complex and q-Weyl scalar actions on the family form a scalar tower. -/
instance : IsScalarTower ℂ (qWeylAlgebra ℂ q) (Fam q α β) :=
  famModule_isScalarTower q α β (orderOf q) rfl

/-- The action on `V(α,β)` is the one produced by the universal property. -/
theorem fam_smul (a : qWeylAlgebra ℂ q) (f : Fam q α β) :
    a • f = Etingof.QWeyl.toEnd q (Xunit α (orderOf q)) (Yunit q β (orderOf q))
      (famRel_unit q α β (orderOf q) rfl) a f := rfl

omit [NeZero (orderOf q)] in
/-- `V(α,β)` has dimension `n = orderOf q` over `ℂ`, matching the dimension theorem of
`Problem2_7_5.lean`. In particular the carrier is not degenerate. -/
theorem fam_finrank : Module.finrank ℂ (Fam q α β) = orderOf q :=
  famModule_finrank (orderOf q)

/-- The generator `x` acts on `V(α,β)` as the twisted cyclic shift. -/
theorem fam_x_smul (f : Fam q α β) :
    (Etingof.QWeyl.qWeylMono q (1, 0)) • f = Xlin α (orderOf q) f :=
  famModule_x_smul q α β (orderOf q) rfl f

/-- The generator `y` acts on `V(α,β)` as the diagonal operator. -/
theorem fam_y_smul (f : Fam q α β) :
    (Etingof.QWeyl.qWeylMono q (0, 1)) • f = Ylin q β (orderOf q) f :=
  famModule_y_smul q α β (orderOf q) rfl f

/-- The central element `xⁿ` acts on `V(α,β)` by the scalar `α`. -/
theorem fam_xpow_smul (f : Fam q α β) :
    (Etingof.QWeyl.qWeylMono q ((orderOf q : ℤ), 0)) • f = (α : ℂ) • f :=
  famModule_xpow_smul q α β (orderOf q) rfl f

/-- The central element `yⁿ` acts on `V(α,β)` by the scalar `βⁿ`. -/
theorem fam_ypow_smul (f : Fam q α β) :
    (Etingof.QWeyl.qWeylMono q (0, (orderOf q : ℤ))) • f = ((β : ℂ) ^ orderOf q) • f :=
  famModule_ypow_smul q α β (orderOf q) rfl f

end Carrier

/-! ### The explicit isomorphism -/

section Equiv

variable (q α β β' : ℂˣ) [NeZero (orderOf q)]

/-- `Xᵐ` as an invertible operator on the space underlying `V(α,β)`. -/
noncomputable def shiftUnit (m : ℕ) : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ :=
  Xunit α (orderOf q) ^ m

/-- Applying the inverse shift after the forward shift fixes every vector. -/
theorem shiftUnit_inv_apply (m : ℕ) (g : Fin (orderOf q) → ℂ) :
    (((shiftUnit q α m)⁻¹ : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ))
      (((shiftUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ)) g) = g := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rfl

/-- Applying the forward shift after the inverse shift fixes every vector. -/
theorem shiftUnit_apply_inv (m : ℕ) (g : Fin (orderOf q) → ℂ) :
    ((shiftUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ))
      ((((shiftUnit q α m)⁻¹ : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ)) g) = g := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rfl

/-- **The intertwiner.** When `β = β'·qᵐ`, the operator `Xᵐ` is an isomorphism of
`qWeylAlgebra ℂ q`-modules `V(α,β) ≃ V(α,β')`. -/
noncomputable def famEquivOfPow (m : ℕ) (hβ : (β : ℂ) = (β' : ℂ) * (q : ℂ) ^ m) :
    Fam q α β ≃ₗ[qWeylAlgebra ℂ q] Fam q α β' where
  toFun f := ((shiftUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
    Module.End ℂ (Fin (orderOf q) → ℂ)) f
  invFun f := (((shiftUnit q α m)⁻¹ : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
    Module.End ℂ (Fin (orderOf q) → ℂ)) f
  map_add' f g := map_add _ f g
  map_smul' a f := by
    have hconj := Etingof.QWeyl.toEnd_conj q (Xunit α (orderOf q)) (Yunit q β (orderOf q))
      (Xunit α (orderOf q)) (Yunit q β' (orderOf q)) (shiftUnit q α m)
      (famRel_unit q α β (orderOf q) rfl) (famRel_unit q α β' (orderOf q) rfl)
      (Xunit_pow_mul_Xunit α (orderOf q) m)
      (Xunit_pow_mul_Yunit q α β β' (orderOf q) rfl m hβ) a
    change ((shiftUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
        Module.End ℂ (Fin (orderOf q) → ℂ))
        (Etingof.QWeyl.toEnd q (Xunit α (orderOf q)) (Yunit q β (orderOf q))
          (famRel_unit q α β (orderOf q) rfl) a f)
      = Etingof.QWeyl.toEnd q (Xunit α (orderOf q)) (Yunit q β' (orderOf q))
          (famRel_unit q α β' (orderOf q) rfl) a
          (((shiftUnit q α m : (Module.End ℂ (Fin (orderOf q) → ℂ))ˣ) :
            Module.End ℂ (Fin (orderOf q) → ℂ)) f)
    rw [hconj]
    simp only [Module.End.mul_apply, shiftUnit_inv_apply]
  left_inv f := shiftUnit_inv_apply q α m f
  right_inv f := shiftUnit_apply_inv q α m f

end Equiv

/-! ### The classification -/

section Classification

variable (q α β α' β' : ℂˣ) [NeZero (orderOf q)]

/-- Two `qWeylAlgebra`-linearly equivalent members of the family have the same central character:
the scalars by which the central elements `xⁿ`, `yⁿ` act must agree. -/
theorem eq_of_famEquiv (e : Fam q α β ≃ₗ[qWeylAlgebra ℂ q] Fam q α' β') :
    α = α' ∧ (β : ℂ) ^ orderOf q = (β' : ℂ) ^ orderOf q := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Fam q α β)
  have hev : e v ≠ 0 := fun h => hv (e.map_eq_zero_iff.mp h)
  constructor
  · have h1 : e ((Etingof.QWeyl.qWeylMono q ((orderOf q : ℤ), 0)) • v)
        = (Etingof.QWeyl.qWeylMono q ((orderOf q : ℤ), 0)) • e v := e.map_smul _ _
    rw [fam_xpow_smul, fam_xpow_smul, LinearMapClass.map_smul_of_tower e] at h1
    have h2 : ((α : ℂ) - (α' : ℂ)) • e v = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact Units.ext (sub_eq_zero.mp h)
    · exact absurd h hev
  · have h1 : e ((Etingof.QWeyl.qWeylMono q (0, (orderOf q : ℤ))) • v)
        = (Etingof.QWeyl.qWeylMono q (0, (orderOf q : ℤ))) • e v := e.map_smul _ _
    rw [fam_ypow_smul, fam_ypow_smul, LinearMapClass.map_smul_of_tower e] at h1
    have h2 : ((β : ℂ) ^ orderOf q - (β' : ℂ) ^ orderOf q) • e v = 0 := by
      rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hev

/-- **Problem 2.7.5(c): the isomorphism criterion.** With `n = orderOf q`, two members of the
classifying family are isomorphic exactly when they share a central character:

`V(α,β) ≅ V(α',β')` iff `α = α'` and `βⁿ = β'ⁿ`. -/
theorem fam_nonempty_linearEquiv_iff :
    Nonempty (Fam q α β ≃ₗ[qWeylAlgebra ℂ q] Fam q α' β')
      ↔ α = α' ∧ (β : ℂ) ^ orderOf q = (β' : ℂ) ^ orderOf q := by
  constructor
  · rintro ⟨e⟩
    exact eq_of_famEquiv q α β α' β' e
  · rintro ⟨rfl, hβ⟩
    obtain ⟨m, hm⟩ := exists_pow_shift q (orderOf q) β β' rfl hβ
    exact ⟨famEquivOfPow q α β β' m hm⟩

end Classification

end Etingof.Problem2_7_5

-- The leaf names follow Mathlib conventions; the underscores come solely from the
-- book-number namespace `Problem2_7_5`, which is part of this project's public API.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_7_5.instAddCommGroupFam
  Etingof.Problem2_7_5.instModuleComplexFam Etingof.Problem2_7_5.famQWeylModule
  Etingof.Problem2_7_5.shiftUnit Etingof.Problem2_7_5.famEquivOfPow

-- `Fam q α β` is deliberately parameter-indexed although its carrier is constant: the
-- parameters select different module instances used by the classification.
attribute [nolint defsWithUnderscore unusedArguments] Etingof.Problem2_7_5.Fam

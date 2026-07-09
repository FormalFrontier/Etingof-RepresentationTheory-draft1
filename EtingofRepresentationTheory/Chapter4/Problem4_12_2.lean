import Mathlib

/-!
# Problem 4.12.2: representations of the Heisenberg group over `𝔽_p`

**Problem 4.12.2.** Let `p` be a prime. Let `G` be the group of `3 × 3` matrices over `𝔽_p`
which are upper triangular and have `1`'s on the diagonal, under multiplication (its order is
`p³`). It is called the **Heisenberg group**. For any complex number `z` such that `z^p = 1`,
we define a representation of `G` on the space `V` of complex functions on `𝔽_p` by
`(ρ x f)(t) = f(t - 1)` for the generator `x = ⟨1,0,0⟩` and `(ρ y f)(t) = z^t · f(t)` for the
generator `y = ⟨0,1,0⟩`.

(a) Show that such a representation exists and is unique, and compute `ρ(g)` for all `g ∈ G`.

(b) Denote this representation by `R_z`. Show that `R_z` is irreducible if and only if `z ≠ 1`.

(c) Classify all `1`-dimensional representations of `G`. Show that `R_1` decomposes into a
direct sum of `1`-dimensional representations, where each of them occurs exactly once.

(d) Use (a)–(c) and the "sum of squares" formula to classify all irreducible representations
of `G`.

## Formalization

We model the Heisenberg group by the triples `⟨a, b, c⟩ : ZMod p` encoding the unitriangular
matrix `[[1,a,c],[0,1,b],[0,0,1]]`; matrix multiplication is
`⟨a,b,c⟩ * ⟨a',b',c'⟩ = ⟨a+a', b+b', c+c'+a·b'⟩`, giving a group of order `p³`. The two
generators are `xGen = ⟨1,0,0⟩` and `yGen = ⟨0,1,0⟩`, and `V = ZMod p → ℂ`.

Statements (faithful signatures, `sorry` proofs — a statement pass):

* **(a)** `exists_unique_rep`: for `z^p = 1` there is a *unique* representation `ρ` of `G` on
  `V` acting on the two generators by the shift and the multiplication operators. (Uniqueness
  holds because `xGen, yGen` generate `G`; this also determines `ρ(g)` for every `g`.)
* **(b)** `irreducible_iff`: any such `R_z` is irreducible iff `z ≠ 1`.
* **(c)** `one_dim_reps_card`: there are exactly `p²` one-dimensional representations (group
  homomorphisms `G → ℂˣ`, since `G^{ab} ≅ (ZMod p)²`); `R1_decomposes`: `R_1` is an internal
  direct sum of `p` one-dimensional `G`-invariant subspaces (each of the `p` distinct
  characters of the cyclic quotient occurs exactly once).
* **(d)** `irreducible_dim`: every irreducible complex representation of `G` has dimension `1`
  or `p`. Together with (c) and the sum-of-squares formula
  `p²·1² + (p-1)·p² = p³ = |G|`, the irreducibles are the `p²` characters and the `p-1`
  representations `R_z` (`z ≠ 1`) of dimension `p`.
-/

noncomputable section

namespace Etingof.Problem4_12_2

/-- The Heisenberg group over `𝔽_p`: the unitriangular matrix `[[1,a,c],[0,1,b],[0,0,1]]` is
encoded by its three free entries `(a, b, c)`. -/
@[ext]
structure Heisenberg (p : ℕ) where
  a : ZMod p
  b : ZMod p
  c : ZMod p

namespace Heisenberg

variable {p : ℕ}

instance : Mul (Heisenberg p) :=
  ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩⟩

instance : One (Heisenberg p) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (Heisenberg p) :=
  ⟨fun x => ⟨-x.a, -x.b, -x.c + x.a * x.b⟩⟩

@[simp] theorem mul_a (x y : Heisenberg p) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : Heisenberg p) : (x * y).b = x.b + y.b := rfl
@[simp] theorem mul_c (x y : Heisenberg p) : (x * y).c = x.c + y.c + x.a * y.b := rfl
@[simp] theorem one_a : (1 : Heisenberg p).a = 0 := rfl
@[simp] theorem one_b : (1 : Heisenberg p).b = 0 := rfl
@[simp] theorem one_c : (1 : Heisenberg p).c = 0 := rfl
@[simp] theorem inv_a (x : Heisenberg p) : x⁻¹.a = -x.a := rfl
@[simp] theorem inv_b (x : Heisenberg p) : x⁻¹.b = -x.b := rfl
@[simp] theorem inv_c (x : Heisenberg p) : x⁻¹.c = -x.c + x.a * x.b := rfl

instance : Group (Heisenberg p) where
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by ext <;> simp

/-- The `x`-generator `⟨1,0,0⟩` of the Heisenberg group. -/
def xGen (p : ℕ) : Heisenberg p := ⟨1, 0, 0⟩

/-- The `y`-generator `⟨0,1,0⟩` of the Heisenberg group. -/
def yGen (p : ℕ) : Heisenberg p := ⟨0, 1, 0⟩

/-- The bijection `Heisenberg p ≃ (ZMod p)³` used to transport finiteness. -/
def equivProd (p : ℕ) : Heisenberg p ≃ ZMod p × ZMod p × ZMod p where
  toFun x := (x.a, x.b, x.c)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv x := by cases x; rfl
  right_inv t := by rfl

instance : DecidableEq (Heisenberg p) := (equivProd p).decidableEq

instance [NeZero p] : Fintype (Heisenberg p) := Fintype.ofEquiv _ (equivProd p).symm

/-- The Heisenberg group has order `p³`. -/
theorem card_eq [NeZero p] : Fintype.card (Heisenberg p) = p ^ 3 := by
  rw [Fintype.card_congr (equivProd p)]
  simp only [Fintype.card_prod, ZMod.card]
  ring

/-- Powers of the `x`-generator: `xGen ^ n = ⟨n, 0, 0⟩`. -/
theorem xGen_pow (n : ℕ) : (xGen p) ^ n = ⟨(n : ZMod p), 0, 0⟩ := by
  induction n with
  | zero => ext <;> simp [xGen]
  | succ k ih =>
    rw [pow_succ, ih]
    refine Heisenberg.ext ?_ ?_ ?_ <;> simp [xGen]

/-- Powers of the `y`-generator: `yGen ^ n = ⟨0, n, 0⟩`. -/
theorem yGen_pow (n : ℕ) : (yGen p) ^ n = ⟨0, (n : ZMod p), 0⟩ := by
  induction n with
  | zero => ext <;> simp [yGen]
  | succ k ih =>
    rw [pow_succ, ih]
    refine Heisenberg.ext ?_ ?_ ?_ <;> simp [yGen]

/-- Powers of the central generator `⟨0,0,1⟩ = [xGen, yGen]`. -/
theorem centralGen_pow (n : ℕ) :
    (⟨0, 0, 1⟩ : Heisenberg p) ^ n = ⟨0, 0, (n : ZMod p)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ k ih =>
    rw [pow_succ, ih]
    refine Heisenberg.ext ?_ ?_ ?_ <;> simp

/-- The central element `⟨0,0,1⟩` is the commutator `[xGen, yGen]`, written with positive
powers `xGen ^ (p-1) = xGen⁻¹`, `yGen ^ (p-1) = yGen⁻¹`. This expresses it as a word in the
two generators using only the monoid structure. -/
theorem central_word [Fact p.Prime] :
    (⟨0, 0, 1⟩ : Heisenberg p)
      = xGen p * yGen p * xGen p ^ (p - 1) * yGen p ^ (p - 1) := by
  have hp1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_pred (Fact.out : p.Prime).pos, ZMod.natCast_self]; ring
  rw [xGen_pow, yGen_pow, hp1]
  refine Heisenberg.ext ?_ ?_ ?_ <;> simp [xGen, yGen]

/-- Every element factors as a word in the generators: `⟨a,b,c⟩ = xGen^a · yGen^b · z^(c-ab)`,
where `z = ⟨0,0,1⟩` is the central generator (all powers are the natural `val` powers). -/
theorem eq_gen_prod [NeZero p] (g : Heisenberg p) :
    g = xGen p ^ g.a.val * yGen p ^ g.b.val
          * (⟨0, 0, 1⟩ : Heisenberg p) ^ (g.c - g.a * g.b).val := by
  rw [xGen_pow, yGen_pow, centralGen_pow]
  have hc : ∀ x : ZMod p, ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_rightInverse
  refine Heisenberg.ext ?_ ?_ ?_
  · simp [hc]
  · simp [hc]
  · simp only [mul_a, mul_c, hc, mul_zero, add_zero, zero_add]; ring

end Heisenberg

open Heisenberg

variable {p : ℕ}

/-- Since `z ^ p = 1`, the exponent of `z` only matters modulo `p`. -/
theorem zpow_mod {z : ℂ} (hz : z ^ p = 1) (k : ℕ) : z ^ (k % p) = z ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hz, one_pow, mul_one]

/-- The map `n ↦ z ^ n.val` is a character of the additive group `ZMod p`: it turns addition
into multiplication (this is where `z ^ p = 1` is used). -/
theorem zpow_val_add {z : ℂ} (hz : z ^ p = 1) [NeZero p] (m n : ZMod p) :
    z ^ (m + n).val = z ^ m.val * z ^ n.val := by
  rw [ZMod.val_add, zpow_mod hz, pow_add]

/-- The linear operator `f ↦ (t ↦ z^(b·t - c) · f(t - a))` on `V = ZMod p → ℂ` associated to
`g = ⟨a,b,c⟩`. This is `ρ(g)` for the representation of part (a). -/
def rhoLin (z : ℂ) (g : Heisenberg p) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) where
  toFun f := fun t => z ^ (g.b * t - g.c).val * f (t - g.a)
  map_add' f₁ f₂ := by funext t; simp only [Pi.add_apply]; ring
  map_smul' r f := by
    funext t; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem rhoLin_apply (z : ℂ) (g : Heisenberg p) (f : ZMod p → ℂ) (t : ZMod p) :
    rhoLin z g f t = z ^ (g.b * t - g.c).val * f (t - g.a) := rfl

/-- The representation `R_z` of the Heisenberg group on `V = ZMod p → ℂ`. -/
def rhoHom [NeZero p] (z : ℂ) (hz : z ^ p = 1) :
    Representation ℂ (Heisenberg p) (ZMod p → ℂ) where
  toFun := rhoLin z
  map_one' := by
    refine LinearMap.ext fun f => funext fun t => ?_
    simp [rhoLin_apply]
  map_mul' g g' := by
    refine LinearMap.ext fun f => funext fun t => ?_
    simp only [Module.End.mul_apply, rhoLin_apply, mul_a, mul_b, mul_c]
    rw [← mul_assoc, ← zpow_val_add hz,
      show (g.b + g'.b) * t - (g.c + g'.c + g.a * g'.b)
          = (g.b * t - g.c) + (g'.b * (t - g.a) - g'.c) from by ring,
      show t - (g.a + g'.a) = t - g.a - g'.a from by ring]

@[simp] theorem rhoHom_apply [NeZero p] (z : ℂ) (hz : z ^ p = 1) (g : Heisenberg p) :
    rhoHom z hz g = rhoLin z g := rfl

theorem rhoHom_xGen [NeZero p] (z : ℂ) (hz : z ^ p = 1) (f : ZMod p → ℂ) (t : ZMod p) :
    rhoHom z hz (xGen p) f t = f (t - 1) := by
  simp [rhoHom_apply, rhoLin_apply, xGen]

theorem rhoHom_yGen [NeZero p] (z : ℂ) (hz : z ^ p = 1) (f : ZMod p → ℂ) (t : ZMod p) :
    rhoHom z hz (yGen p) f t = z ^ t.val * f t := by
  simp [rhoHom_apply, rhoLin_apply, yGen]

/-- **Part (a).** For any `z` with `z^p = 1`, there is a *unique* representation `ρ` of the
Heisenberg group on `V = ZMod p → ℂ` acting on the generators by
`(ρ xGen f)(t) = f(t-1)` and `(ρ yGen f)(t) = z^t · f(t)`. Uniqueness holds because `xGen`
and `yGen` generate `G`, so this data determines `ρ(g)` for every `g`. -/
theorem exists_unique_rep [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) :
    ∃! ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ),
      (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1)) ∧
      (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = z ^ t.val * f t) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨rhoHom z hz, ⟨fun f t => rhoHom_xGen z hz f t, fun f t => rhoHom_yGen z hz f t⟩, ?_⟩
  rintro ρ' ⟨hx', hy'⟩
  -- `ρ'` agrees with `rhoHom z hz` on the two generators, as linear maps.
  have ex : ρ' (xGen p) = rhoHom z hz (xGen p) := by
    refine LinearMap.ext fun f => funext fun t => ?_
    rw [hx' f t, rhoHom_xGen]
  have ey : ρ' (yGen p) = rhoHom z hz (yGen p) := by
    refine LinearMap.ext fun f => funext fun t => ?_
    rw [hy' f t, rhoHom_yGen]
  -- Hence they agree on the central generator `⟨0,0,1⟩`, which is a word in the generators.
  have ez : ρ' (⟨0, 0, 1⟩ : Heisenberg p) = rhoHom z hz ⟨0, 0, 1⟩ := by
    rw [central_word]
    simp only [map_mul, map_pow, ex, ey]
  -- and therefore on every group element, via `eq_gen_prod`.
  refine MonoidHom.ext fun g => ?_
  rw [eq_gen_prod g]
  simp only [map_mul, map_pow, ex, ey, ez]

/-- **Part (b).** The representation `R_z` (any `ρ` satisfying the generator conditions with a
`p`-th root of unity `z`) is irreducible if and only if `z ≠ 1`. -/
theorem irreducible_iff [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hx : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1))
    (hy : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = z ^ t.val * f t) :
    IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) ρ.asModule ↔ z ≠ 1 := by
  sorry

/-- **Part (c), classification of `1`-dimensional representations.** The one-dimensional
complex representations of the Heisenberg group are its group homomorphisms to `ℂˣ`, and there
are exactly `p²` of them (the abelianization is `(ZMod p)²`). -/
theorem one_dim_reps_card [Fact p.Prime] :
    Nat.card (Heisenberg p →* ℂˣ) = p ^ 2 := by
  sorry

/-- **Part (c), decomposition of `R_1`.** When `z = 1` the representation `R_1` decomposes as
an internal direct sum of `p` one-dimensional `G`-invariant subspaces (the `p` distinct
characters of the cyclic quotient, each occurring exactly once). -/
theorem R1_decomposes [Fact p.Prime]
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hx : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1))
    (hy : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = f t) :
    ∃ S : Fin p → Submodule ℂ (ZMod p → ℂ),
      (∀ i, ∀ (g : Heisenberg p), ∀ v ∈ S i, ρ g v ∈ S i) ∧
      (∀ i, Module.finrank ℂ (S i) = 1) ∧
      DirectSum.IsInternal S := by
  sorry

/-- **Part (d).** Every irreducible complex representation of the Heisenberg group has
dimension `1` or `p`. (Combined with (c) and the sum-of-squares formula
`p²·1² + (p-1)·p² = p³`, the irreducibles are exactly the `p²` characters together with the
`p-1` representations `R_z` for `z ≠ 1`, each of dimension `p`.) -/
theorem irreducible_dim [Fact p.Prime]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Heisenberg p) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) σ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = p := by
  sorry

end Etingof.Problem4_12_2

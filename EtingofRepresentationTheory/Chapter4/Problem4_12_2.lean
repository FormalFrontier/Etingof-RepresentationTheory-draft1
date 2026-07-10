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

/-- The two generators `xGen`, `yGen` generate the Heisenberg group as a monoid: their submonoid
closure is everything. This uses `eq_gen_prod` and `central_word`, which express every element as
a product of positive powers of `xGen` and `yGen`. -/
theorem closure_gens_eq_top [Fact p.Prime] :
    Submonoid.closure ({xGen p, yGen p} : Set (Heisenberg p)) = ⊤ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine eq_top_iff.mpr fun g _ => ?_
  have hx : xGen p ∈ Submonoid.closure ({xGen p, yGen p} : Set (Heisenberg p)) :=
    Submonoid.subset_closure (by simp)
  have hy : yGen p ∈ Submonoid.closure ({xGen p, yGen p} : Set (Heisenberg p)) :=
    Submonoid.subset_closure (by simp)
  have hcentral : (⟨0, 0, 1⟩ : Heisenberg p) ∈
      Submonoid.closure ({xGen p, yGen p} : Set (Heisenberg p)) := by
    rw [central_word]
    exact mul_mem (mul_mem (mul_mem hx hy) (pow_mem hx _)) (pow_mem hy _)
  rw [eq_gen_prod g]
  exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (pow_mem hcentral _)

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
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hNTV : Nontrivial (ZMod p → ℂ) :=
    ⟨fun _ => 0, fun _ => 1, fun h => zero_ne_one (congrFun h (0 : ZMod p))⟩
  -- Reduce simplicity of the `ℂ[G]`-module to simplicity of the lattice of subrepresentations.
  rw [isSimpleModule_iff,
    ← (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).isSimpleOrder_iff]
  -- The shift generator sends the indicator of `s` to the indicator of `s + 1`.
  have X_single : ∀ s : ZMod p,
      ρ (xGen p) (Pi.single s (1 : ℂ)) = Pi.single (s + 1) (1 : ℂ) := by
    intro s
    funext t
    rw [hx]
    simp only [Pi.single_apply]
    by_cases h : t - 1 = s
    · rw [if_pos h, if_pos (sub_eq_iff_eq_add.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (sub_eq_iff_eq_add.mpr hc))]
  constructor
  · -- `IsSimpleOrder → z ≠ 1`.  Contrapositive: if `z = 1`, the constant line is a proper
    -- nonzero subrepresentation.
    intro hsimple hz1
    set c0 : ZMod p → ℂ := fun _ => 1 with hc0
    have hXc : ρ (xGen p) c0 = c0 := by funext t; simp [hx, hc0]
    have hYc : ρ (yGen p) c0 = c0 := by funext t; simp [hy, hz1, hc0]
    set W₀ : Submodule ℂ (ZMod p → ℂ) := Submodule.span ℂ {c0} with hW₀
    have hfix : ∀ (op : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)), op c0 = c0 →
        ∀ v ∈ W₀, op v ∈ W₀ := by
      intro op hop v hv
      have hle : W₀ ≤ W₀.comap op := by
        rw [hW₀, Submodule.span_le]
        intro x hx'
        rw [Set.mem_singleton_iff] at hx'; subst hx'
        simp only [SetLike.mem_coe, Submodule.mem_comap, hop]
        exact Submodule.mem_span_singleton_self c0
      exact hle hv
    have hXW := hfix (ρ (xGen p)) hXc
    have hYW := hfix (ρ (yGen p)) hYc
    -- The constant line is invariant under all of `G`.
    have hinv : ∀ (g : Heisenberg p) ⦃v : ZMod p → ℂ⦄, v ∈ W₀ → ρ g v ∈ W₀ := by
      let S : Submonoid (Heisenberg p) :=
        { carrier := {g | ∀ v ∈ W₀, ρ g v ∈ W₀}
          one_mem' := by intro v hv; rw [map_one]; simpa using hv
          mul_mem' := by
            intro a b ha hb v hv
            rw [map_mul]
            exact ha _ (hb v hv) }
      have hSle : Submonoid.closure ({xGen p, yGen p} : Set (Heisenberg p)) ≤ S :=
        Submonoid.closure_le.mpr (by
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl
          · exact hXW
          · exact hYW)
      intro g v hv
      have hgS : g ∈ S :=
        hSle (by rw [Heisenberg.closure_gens_eq_top]; exact Submonoid.mem_top g)
      exact hgS v hv
    let σ₀ : Subrepresentation ρ := ⟨W₀, hinv⟩
    rcases hsimple.eq_bot_or_eq_top σ₀ with hbot | htop
    · -- `σ₀ = ⊥` would force the constant vector to be zero.
      have h0 : W₀ = ⊥ := congrArg Subrepresentation.toSubmodule hbot
      have hc0mem : c0 ∈ W₀ := Submodule.mem_span_singleton_self c0
      rw [h0, Submodule.mem_bot] at hc0mem
      have : (1 : ℂ) = 0 := by simpa [hc0] using congrFun hc0mem 0
      exact one_ne_zero this
    · -- `σ₀ = ⊤` would force the indicator `e₀` to be a constant, impossible for `p ≥ 2`.
      have hW₀top : W₀ = ⊤ := congrArg Subrepresentation.toSubmodule htop
      have hmem : Pi.single (0 : ZMod p) (1 : ℂ) ∈ W₀ := by rw [hW₀top]; exact Submodule.mem_top
      rw [hW₀, Submodule.mem_span_singleton] at hmem
      obtain ⟨a, ha⟩ := hmem
      have e0 : a = 1 := by
        simpa [hc0, Pi.smul_apply, smul_eq_mul, Pi.single_apply] using congrFun ha 0
      have e1 : a = 0 := by
        have h := congrFun ha 1
        simp only [hc0, Pi.smul_apply, smul_eq_mul, mul_one, Pi.single_apply] at h
        rwa [if_neg (one_ne_zero : (1 : ZMod p) ≠ 0)] at h
      rw [e0] at e1
      exact one_ne_zero e1
  · -- `z ≠ 1 → IsSimpleOrder`.
    intro hzne
    have hc : ∀ x : ZMod p, ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_rightInverse
    -- `z` is a primitive `p`-th root of unity, so `t ↦ z ^ t.val` is injective.
    have hdist : ∀ s t : ZMod p, z ^ s.val = z ^ t.val → s = t := by
      intro s t hst
      have horder : orderOf z = p := by
        rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf z)
            (orderOf_dvd_of_pow_eq_one hz) with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hzne
        · exact h
      have hs : s.val < orderOf z := by rw [horder]; exact ZMod.val_lt s
      have ht : t.val < orderOf z := by rw [horder]; exact ZMod.val_lt t
      exact ZMod.val_injective p
        (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hs) (Set.mem_Iio.mpr ht) hst)
    -- A nonzero `Y`-invariant subspace contains some indicator vector.
    have keySingle : ∀ (W : Submodule ℂ (ZMod p → ℂ)),
        (∀ v ∈ W, ρ (yGen p) v ∈ W) → ∀ f ∈ W, f ≠ 0 →
        ∃ t, Pi.single t (1 : ℂ) ∈ W := by
      intro W hYW
      suffices H : ∀ n, ∀ f : ZMod p → ℂ, f ∈ W → f ≠ 0 →
          (Finset.univ.filter (fun t => f t ≠ 0)).card = n → ∃ t, Pi.single t (1 : ℂ) ∈ W by
        intro f hfW hf0; exact H _ f hfW hf0 rfl
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro f hfW hf0 hcard
        set S := Finset.univ.filter (fun t => f t ≠ 0) with hS
        have hSne : S.Nonempty := by
          rw [hS, Finset.filter_nonempty_iff]
          by_contra hcon
          push_neg at hcon
          exact hf0 (funext fun t => hcon t (Finset.mem_univ t))
        rcases eq_or_lt_of_le (Finset.one_le_card.mpr hSne) with h1 | h2
        · -- support is a singleton `{a}`, so `f = f a • e_a` and `e_a ∈ W`.
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1.symm
          refine ⟨a, ?_⟩
          have hfa : f a ≠ 0 := by
            have : a ∈ S := ha ▸ Finset.mem_singleton_self a
            rw [hS, Finset.mem_filter] at this; exact this.2
          have hfeq : Pi.single a (1 : ℂ) = (f a)⁻¹ • f := by
            funext t
            by_cases h : t = a
            · subst h; simp [Pi.single_apply, inv_mul_cancel₀ hfa]
            · have ht0 : f t = 0 := by
                by_contra hne
                have : t ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ t, hne⟩
                rw [ha, Finset.mem_singleton] at this; exact h this
              simp [Pi.single_apply, h, ht0]
          rw [hfeq]
          exact Submodule.smul_mem _ _ hfW
        · -- support has ≥ 2 elements; subtract an eigenvalue to shrink it.
          obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := Finset.one_lt_card.mp h2
          set g : ZMod p → ℂ := ρ (yGen p) f - (z ^ t₂.val) • f with hgdef
          have hgval : ∀ t, g t = (z ^ t.val - z ^ t₂.val) * f t := by
            intro t
            simp only [hgdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hy]
            ring
          have hgW : g ∈ W := Submodule.sub_mem _ (hYW f hfW) (Submodule.smul_mem _ _ hfW)
          have hft₁ : f t₁ ≠ 0 := by rw [hS, Finset.mem_filter] at ht₁; exact ht₁.2
          have hg0 : g ≠ 0 := by
            intro hcon
            have hval : g t₁ = 0 := congrFun hcon t₁
            rw [hgval] at hval
            have hz12 : z ^ t₁.val - z ^ t₂.val ≠ 0 :=
              fun he => hne (hdist _ _ (sub_eq_zero.mp he))
            exact mul_ne_zero hz12 hft₁ hval
          have hsub : Finset.univ.filter (fun t => g t ≠ 0) ⊆ S := by
            intro t ht
            rw [Finset.mem_filter] at ht
            rw [hS, Finset.mem_filter]
            refine ⟨Finset.mem_univ t, fun hf0' => ht.2 ?_⟩
            rw [hgval, hf0', mul_zero]
          have ht₂notin : t₂ ∉ Finset.univ.filter (fun t => g t ≠ 0) := by
            rw [Finset.mem_filter]; push_neg
            intro _
            rw [hgval, sub_self, zero_mul]
          have hlt : (Finset.univ.filter (fun t => g t ≠ 0)).card < n := by
            rw [← hcard]
            exact Finset.card_lt_card
              ((Finset.ssubset_iff_of_subset hsub).mpr ⟨t₂, ht₂, ht₂notin⟩)
          exact ih _ hlt g hgW hg0 rfl
    -- Assemble `IsSimpleOrder`.
    have hNT : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⊥, ⊤, ?_⟩
      intro h
      exact absurd (congrArg Subrepresentation.toSubmodule h) bot_ne_top
    refine { toNontrivial := hNT, eq_bot_or_eq_top := fun σ => ?_ }
    rcases eq_or_ne σ.toSubmodule ⊥ with hbot | hne
    · exact Or.inl (Subrepresentation.toSubmodule_injective hbot)
    · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
      show σ.toSubmodule = ⊤
      obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff _).mp hne
      obtain ⟨t₀, ht₀⟩ :=
        keySingle σ.toSubmodule (fun v hv => σ.apply_mem_toSubmodule (yGen p) hv) f hfW hf0
      -- `X` cyclically permutes indicators, so every indicator lies in `σ`.
      have hall : ∀ s : ZMod p, Pi.single s (1 : ℂ) ∈ σ.toSubmodule := by
        have hpow : ∀ n : ℕ, Pi.single (t₀ + (n : ZMod p)) (1 : ℂ) ∈ σ.toSubmodule := by
          intro n
          induction n with
          | zero => simpa using ht₀
          | succ k ih =>
            have hstep := σ.apply_mem_toSubmodule (xGen p) ih
            rw [X_single] at hstep
            have heq : t₀ + ((k + 1 : ℕ) : ZMod p) = t₀ + (k : ZMod p) + 1 := by push_cast; ring
            rw [heq]; exact hstep
        intro s
        have h := hpow (s - t₀).val
        have heq : t₀ + (s - t₀) = s := by abel
        rwa [hc (s - t₀), heq] at h
      rw [eq_top_iff]
      intro f' _
      have hf'eq : f' = ∑ s : ZMod p, f' s • Pi.single s (1 : ℂ) := by
        funext t
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
          mul_one, mul_zero]
        rw [Finset.sum_ite_eq Finset.univ t f']
        simp
      rw [hf'eq]
      exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (hall s))

/-- The abelianization map `⟨a,b,c⟩ ↦ (a,b)` of the Heisenberg group, written multiplicatively
as a homomorphism to `Multiplicative (ZMod p × ZMod p)`. Its kernel is the center `{⟨0,0,c⟩}`,
which is exactly the commutator subgroup. -/
def abHom (p : ℕ) : Heisenberg p →* Multiplicative (ZMod p × ZMod p) where
  toFun g := Multiplicative.ofAdd (g.a, g.b)
  map_one' := rfl
  map_mul' x y := rfl

@[simp] theorem abHom_apply (p : ℕ) (g : Heisenberg p) :
    abHom p g = Multiplicative.ofAdd (g.a, g.b) := rfl

/-- The abelianization map is surjective. -/
theorem abHom_surjective (p : ℕ) : Function.Surjective (abHom p) := by
  intro y
  exact ⟨⟨(Multiplicative.toAdd y).1, (Multiplicative.toAdd y).2, 0⟩, rfl⟩

/-- The central generator `⟨0,0,1⟩` is the commutator `⁅xGen, yGen⁆`, so it lies in the
commutator subgroup. -/
theorem central_mem_commutator [Fact p.Prime] :
    (⟨0, 0, 1⟩ : Heisenberg p) ∈ commutator (Heisenberg p) := by
  have hcomm : (⟨0, 0, 1⟩ : Heisenberg p)
      = xGen p * yGen p * (xGen p)⁻¹ * (yGen p)⁻¹ := by
    refine Heisenberg.ext ?_ ?_ ?_ <;> simp [xGen, yGen]
  rw [commutator_def, hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Every character `ρ : G →* ℂˣ` kills the kernel of the abelianization map: that kernel is the
center `{⟨0,0,c⟩}`, which lies in the commutator subgroup, and `ℂˣ` is abelian. -/
theorem abHom_ker_le_ker [Fact p.Prime] (ρ : Heisenberg p →* ℂˣ) :
    (abHom p).ker ≤ ρ.ker := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine le_trans ?_ (Abelianization.commutator_subset_ker ρ)
  intro g hg
  rw [MonoidHom.mem_ker, abHom_apply] at hg
  have hab : (g.a, g.b) = (0, 0) := ofAdd_eq_one.mp hg
  have hga : g.a = 0 := (Prod.ext_iff.mp hab).1
  have hgb : g.b = 0 := (Prod.ext_iff.mp hab).2
  have hg_eq : g = (⟨0, 0, 1⟩ : Heisenberg p) ^ g.c.val := by
    rw [centralGen_pow]
    refine Heisenberg.ext hga hgb ?_
    exact (ZMod.natCast_rightInverse g.c).symm
  rw [hg_eq]
  exact pow_mem central_mem_commutator _

/-- **Part (c), classification of `1`-dimensional representations.** The one-dimensional
complex representations of the Heisenberg group are its group homomorphisms to `ℂˣ`, and there
are exactly `p²` of them (the abelianization is `(ZMod p)²`). -/
theorem one_dim_reps_card [Fact p.Prime] :
    Nat.card (Heisenberg p →* ℂˣ) = p ^ 2 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Characters of `G` correspond bijectively to characters of the abelianization `(ZMod p)²`.
  let e : (Multiplicative (ZMod p × ZMod p) →* ℂˣ) ≃ (Heisenberg p →* ℂˣ) :=
    (MonoidHom.liftOfSurjective (abHom p) (abHom_surjective p)).symm.trans
      (Equiv.subtypeUnivEquiv (fun ρ => abHom_ker_le_ker ρ))
  haveI : NeZero ((Monoid.exponent (Multiplicative (ZMod p × ZMod p)) : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  rw [← Nat.card_congr e,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative (ZMod p × ZMod p)) ℂ,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]
  ring

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

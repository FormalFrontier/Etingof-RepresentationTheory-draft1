import Mathlib

/-!
# Problem 4.12.6: representations of the affine group `x ↦ ax + b` over `𝔽_q`

**Problem 4.12.6.** Let `𝔽_q` be a finite field with `q` elements, and let `G` be the group of
nonconstant inhomogeneous linear transformations, `x ↦ ax + b`, over `𝔽_q` (i.e.,
`a ∈ 𝔽_q^×`, `b ∈ 𝔽_q`). Find all irreducible complex representations of `G`, and compute
their characters. Compute the tensor products of irreducible representations.

Hint: Let `V` be the representation of `G` on the space of functions on `𝔽_q` with sum of all
values equal to zero. Show that `V` is an irreducible representation of `G`.

## Formalization

We model `𝔽_q` by an arbitrary finite field `K` (`q = Fintype.card K`) and `G` by the pairs
`⟨a, b⟩` with `a : Kˣ`, `b : K`, encoding the transformation `x ↦ a·x + b`. Composition gives
the multiplication `⟨a,b⟩ * ⟨a',b'⟩ = ⟨a·a', a·b' + b⟩`, so `G = K ⋊ Kˣ` has order `q(q-1)`.

The classification (recorded here; `sorry` proofs — a statement pass):

* `one_dim_reps_card`: the one-dimensional representations are the group homomorphisms
  `G → ℂˣ`, pulled back from the abelianization `G^{ab} ≅ Kˣ`; there are exactly `q-1` of them.
* `zeroSum` is the subspace of functions `K → ℂ` whose values sum to `0`; `zeroSum_invariant`
  and `zeroSum_finrank` show it is a `G`-invariant subspace of dimension `q-1`, and
  `zeroSum_irreducible` shows the corresponding representation `V` is irreducible.
* `irreducible_dim`: every irreducible complex representation of `G` has dimension `1` or
  `q-1`. Together with the sum-of-squares formula `(q-1)·1² + 1·(q-1)² = q(q-1) = |G|`, the
  irreducibles are exactly the `q-1` characters and the single `(q-1)`-dimensional
  representation `V`.

`G` acts on `𝔽_q` by the affine transformation, and hence on functions `K → ℂ` by
`(ρ g f)(x) = f(g⁻¹ · x)`; the irreducibility statements are phrased for any such `ρ`.
-/

noncomputable section

namespace Etingof.Problem4_12_6

variable {K : Type*} [Field K]

/-- The affine group of transformations `x ↦ a·x + b` over `K`, encoded by the pair `⟨a, b⟩`
with `a : Kˣ` and `b : K`. -/
@[ext]
structure Affine (K : Type*) [Field K] where
  a : Kˣ
  b : K

namespace Affine

instance : Mul (Affine K) :=
  ⟨fun g h => ⟨g.a * h.a, (g.a : K) * h.b + g.b⟩⟩

instance : One (Affine K) := ⟨⟨1, 0⟩⟩

instance : Inv (Affine K) :=
  ⟨fun g => ⟨g.a⁻¹, -((g.a⁻¹ : K) * g.b)⟩⟩

@[simp] theorem mul_a (g h : Affine K) : (g * h).a = g.a * h.a := rfl
@[simp] theorem mul_b (g h : Affine K) : (g * h).b = (g.a : K) * h.b + g.b := rfl
@[simp] theorem one_a : (1 : Affine K).a = 1 := rfl
@[simp] theorem one_b : (1 : Affine K).b = 0 := rfl
@[simp] theorem inv_a (g : Affine K) : g⁻¹.a = g.a⁻¹ := rfl
@[simp] theorem inv_b (g : Affine K) : g⁻¹.b = -((g.a⁻¹ : K) * g.b) := rfl

instance : Group (Affine K) where
  mul_assoc g h k := by
    ext
    · simp [mul_assoc]
    · simp; ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    ext
    · simp
    · simp

/-- The affine action of `G` on `K`: `⟨a,b⟩ · x = a·x + b`. -/
def act (g : Affine K) (x : K) : K := (g.a : K) * x + g.b

@[simp] theorem act_one (x : K) : act (1 : Affine K) x = x := by simp [act]

theorem act_mul (g h : Affine K) (x : K) : act (g * h) x = act g (act h x) := by
  simp only [act, mul_a, mul_b, Units.val_mul]; ring

@[simp] theorem act_apply_inv (g : Affine K) (x : K) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

@[simp] theorem act_inv_apply (g : Affine K) (x : K) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- The affine action of `g` viewed as a permutation of `K`. -/
def actEquiv (g : Affine K) : K ≃ K where
  toFun := act g
  invFun := act g⁻¹
  left_inv := act_inv_apply g
  right_inv := act_apply_inv g

theorem act_inv_eq_iff (g : Affine K) (x p : K) : act g⁻¹ x = p ↔ x = act g p := by
  constructor
  · intro h; rw [← h]; exact (act_apply_inv g x).symm
  · intro h; rw [h]; exact act_inv_apply g p

/-- The bijection `Affine K ≃ Kˣ × K` used to transport finiteness. -/
def equivProd (K : Type*) [Field K] : Affine K ≃ Kˣ × K where
  toFun g := (g.a, g.b)
  invFun t := ⟨t.1, t.2⟩
  left_inv g := by cases g; rfl
  right_inv t := by rfl

instance [DecidableEq K] : DecidableEq (Affine K) := (equivProd K).decidableEq

instance [Fintype K] [DecidableEq K] : Fintype (Affine K) := Fintype.ofEquiv _ (equivProd K).symm

/-- The affine group has order `q(q-1)`. -/
theorem card_eq [Fintype K] [DecidableEq K] :
    Fintype.card (Affine K) = Fintype.card K * (Fintype.card K - 1) := by
  rw [Fintype.card_congr (equivProd K), Fintype.card_prod, Fintype.card_units, mul_comm]

end Affine

open Affine

/-- **One-dimensional representations.** They are the group homomorphisms `G → ℂˣ`
(pulled back from `G^{ab} ≅ Kˣ`), and there are exactly `q - 1` of them. -/
theorem one_dim_reps_card [Fintype K] :
    Nat.card (Affine K →* ℂˣ) = Fintype.card K - 1 := by
  sorry

/-- The subspace `V` of functions `K → ℂ` whose values sum to zero. -/
def zeroSum (K : Type*) [Fintype K] : Submodule ℂ (K → ℂ) where
  carrier := {f | ∑ x, f x = 0}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  zero_mem' := by simp
  smul_mem' c f hf := by
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [← Finset.mul_sum, hf, mul_zero]

/-- `V = zeroSum K` is a `G`-invariant subspace of the permutation representation on `K → ℂ`
(where `(ρ g f)(x) = f(g⁻¹ · x)`). -/
theorem zeroSum_invariant [Fintype K]
    (ρ : Representation ℂ (Affine K) (K → ℂ))
    (hρ : ∀ (g : Affine K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x)) :
    ∀ (g : Affine K), ∀ f ∈ zeroSum K, ρ g f ∈ zeroSum K := by
  intro g f hf
  simp only [zeroSum, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at *
  calc ∑ x, (ρ g f) x = ∑ x, f (act g⁻¹ x) := by simp_rw [hρ]
    _ = ∑ x, f (actEquiv g⁻¹ x) := rfl
    _ = ∑ x, f x := Equiv.sum_comp (actEquiv g⁻¹) f
    _ = 0 := hf

/-- The zero-sum representation `V` has dimension `q - 1`. -/
theorem zeroSum_finrank [Fintype K] :
    Module.finrank ℂ (zeroSum K) = Fintype.card K - 1 := by
  classical
  -- The summation functional `L f = ∑ x, f x`; `zeroSum K` is its kernel.
  let L : (K → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∑ x, f x
      map_add' := fun f g => by simp [Finset.sum_add_distrib]
      map_smul' := fun c f => by simp [Finset.mul_sum] }
  have hker : LinearMap.ker L = zeroSum K := by
    ext f
    simp only [LinearMap.mem_ker, L, LinearMap.coe_mk, AddHom.coe_mk, zeroSum,
      Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  have hsurj : Function.Surjective L := by
    intro c
    refine ⟨fun x => if x = 0 then c else 0, ?_⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_ite_eq' Finset.univ (0 : K) (fun _ => c)]
    simp
  have hrange : Module.finrank ℂ (LinearMap.range L) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp [Module.finrank_self]
  have hnull := LinearMap.finrank_range_add_finrank_ker L
  rw [hker, hrange, Module.finrank_pi ℂ] at hnull
  omega

/-- The "spike" function at `t`: value `q - 1` at `t` and `-1` elsewhere, where `q = |K|`.
Equivalently `q · δ_t - 1`; it lies in `zeroSum K` and the `spike`s span `zeroSum K`. -/
def spike (K : Type*) [Fintype K] [DecidableEq K] (t : K) : K → ℂ :=
  (Fintype.card K : ℂ) • Pi.single t (1 : ℂ) - 1

/-- Summing a function over the units `Kˣ` (the nonzero elements) misses the value at `0`. -/
theorem sum_units_eq [Fintype K] [DecidableEq K] (φ : K → ℂ) :
    ∑ a : Kˣ, φ (a : K) = (∑ y : K, φ y) - φ 0 := by
  classical
  let e : Kˣ ≃ {y : K // y ≠ 0} :=
    { toFun := fun u => ⟨(u : K), u.ne_zero⟩
      invFun := fun y => Units.mk0 y.1 y.2
      left_inv := fun u => by ext; simp
      right_inv := fun y => by ext; simp }
  have h1 : ∑ a : Kˣ, φ (a : K) = ∑ y : {y : K // y ≠ 0}, φ (y : K) :=
    Fintype.sum_equiv e _ _ (fun a => rfl)
  have hmem : ∀ x : K, x ∈ Finset.univ.erase (0 : K) ↔ x ≠ 0 := by
    intro x; simp [Finset.mem_erase]
  rw [h1, ← Finset.sum_subtype _ hmem φ, Finset.sum_erase_eq_sub (Finset.mem_univ (0 : K))]

/-- The action permutes the indicator functions: `ρ g (δ_p) = δ_{g·p}`. -/
theorem rho_single [DecidableEq K]
    (ρ : Representation ℂ (Affine K) (K → ℂ))
    (hρ : ∀ (g : Affine K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x))
    (g : Affine K) (p : K) :
    ρ g (Pi.single p (1 : ℂ)) = Pi.single (act g p) (1 : ℂ) := by
  funext x
  rw [hρ, Pi.single_apply, Pi.single_apply]
  simp only [act_inv_eq_iff]

/-- The action fixes the constant function `1`. -/
theorem rho_const
    (ρ : Representation ℂ (Affine K) (K → ℂ))
    (hρ : ∀ (g : Affine K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x))
    (g : Affine K) :
    ρ g (1 : K → ℂ) = 1 := by
  funext x; rw [hρ]; rfl

/-- The action permutes the spikes: `ρ g (spike t) = spike (g·t)`. -/
theorem rho_spike [Fintype K] [DecidableEq K]
    (ρ : Representation ℂ (Affine K) (K → ℂ))
    (hρ : ∀ (g : Affine K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x))
    (g : Affine K) (t : K) :
    ρ g (spike K t) = spike K (act g t) := by
  unfold spike
  rw [map_sub, map_smul, rho_single ρ hρ, rho_const ρ hρ]

/-- **The hint.** The representation `V` of `G` on the zero-sum functions is irreducible:
every `G`-invariant subspace contained in `zeroSum K` is `⊥` or all of `zeroSum K`. -/
theorem zeroSum_irreducible [Fintype K]
    (ρ : Representation ℂ (Affine K) (K → ℂ))
    (hρ : ∀ (g : Affine K) (f : K → ℂ) (x : K), (ρ g f) x = f (act g⁻¹ x))
    (U : Submodule ℂ (K → ℂ)) (hUle : U ≤ zeroSum K)
    (hUinv : ∀ (g : Affine K), ∀ f ∈ U, ρ g f ∈ U) :
    U = ⊥ ∨ U = zeroSum K := by
  classical
  rcases eq_or_ne U ⊥ with hU | hU
  · exact Or.inl hU
  refine Or.inr (le_antisymm hUle ?_)
  -- `q = |K| ≥ 2`, in particular `q ≠ 0` as a complex number.
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  have hqne : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  -- Pick a nonzero `f₀ ∈ U` and a point `p` where it is nonzero.
  obtain ⟨f0, hf0U, hf0ne⟩ := (Submodule.ne_bot_iff U).mp hU
  obtain ⟨p, hp⟩ : ∃ p, f0 p ≠ 0 := by
    by_contra h
    exact hf0ne (funext fun x => by simpa using not_exists.mp h x)
  -- Translate so the nonzero value sits at `0`: `f' = ρ ⟨1,-p⟩ f₀`, `f' 0 = f₀ p`.
  set g0 : Affine K := ⟨1, -p⟩ with hg0
  set f' : K → ℂ := ρ g0 f0 with hf'def
  have hf'U : f' ∈ U := hUinv g0 f0 hf0U
  have hf'0 : f' 0 = f0 p := by
    rw [hf'def, hρ]; simp [act, hg0]
  have hf'0ne : f' 0 ≠ 0 := by rw [hf'0]; exact hp
  have hf'sum : ∑ x, f' x = 0 := hUle hf'U
  -- Average `f'` over the scaling subgroup `{⟨a,0⟩ : a ∈ Kˣ}`.
  set h : K → ℂ := ∑ a : Kˣ, ρ (⟨a, 0⟩ : Affine K) f' with hhdef
  have hhU : h ∈ U := Submodule.sum_mem U (fun a _ => hUinv _ _ hf'U)
  -- Compute: `h = f' 0 • spike 0`.
  have hheq : h = (f' 0) • spike K 0 := by
    funext x
    rw [hhdef, Finset.sum_apply]
    have hval : ∀ a : Kˣ, (ρ (⟨a, 0⟩ : Affine K) f') x = f' ((a : K)⁻¹ * x) := by
      intro a
      rw [hρ]; congr 1
      simp [act, Units.val_inv_eq_inv_val]
    simp_rw [hval]
    by_cases hx : x = 0
    · subst hx
      simp only [mul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_units,
        nsmul_eq_mul, Pi.smul_apply, spike, Pi.sub_apply, Pi.single_eq_same,
        Pi.one_apply, smul_eq_mul, mul_one]
      rw [Nat.cast_sub hq1, Nat.cast_one]
      ring
    · -- reindex the sum over `Kˣ`: `a ↦ a⁻¹ * x` bijects onto the nonzero values.
      have hxu : x ≠ 0 := hx
      have hreindex : ∑ a : Kˣ, f' ((a : K)⁻¹ * x) = ∑ a : Kˣ, f' (a : K) := by
        apply Fintype.sum_equiv ((Equiv.inv Kˣ).trans (Equiv.mulRight (Units.mk0 x hxu)))
        intro a
        simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight]
        congr 1
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [hreindex, sum_units_eq, hf'sum, zero_sub]
      simp only [Pi.smul_apply, spike, Pi.sub_apply, Pi.single_apply, if_neg hx,
        Pi.one_apply, smul_eq_mul, mul_zero, zero_sub, mul_neg, mul_one]
  -- Hence `spike 0 ∈ U`, and by translation every `spike t ∈ U`.
  have hspike0U : spike K 0 ∈ U := by
    have : spike K 0 = (f' 0)⁻¹ • h := by
      rw [hheq, smul_smul, inv_mul_cancel₀ hf'0ne, one_smul]
    rw [this]; exact U.smul_mem _ hhU
  have hspikeU : ∀ t, spike K t ∈ U := by
    intro t
    have h1 : ρ (⟨1, t⟩ : Affine K) (spike K 0) = spike K t := by
      rw [rho_spike ρ hρ]; congr 1; simp [act]
    rw [← h1]; exact hUinv _ _ hspike0U
  -- The spikes span `zeroSum K`: `f = ∑ t, (f t / q) • spike t`.
  intro f hf
  have hfsum : ∑ x, f x = 0 := hf
  have hfeq : f = ∑ t : K, (f t / (Fintype.card K : ℂ)) • spike K t := by
    funext x
    rw [Finset.sum_apply]
    simp_rw [Pi.smul_apply, spike, Pi.sub_apply, Pi.smul_apply, Pi.single_apply,
      Pi.one_apply, smul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib]
    have e1 : ∑ t : K, f t / (Fintype.card K : ℂ) * ((Fintype.card K : ℂ) *
        (if x = t then (1 : ℂ) else 0)) = f x := by
      have key : ∀ t : K, f t / (Fintype.card K : ℂ) * ((Fintype.card K : ℂ) *
          (if x = t then (1 : ℂ) else 0)) = if x = t then f t else 0 := by
        intro t
        by_cases h : x = t
        · rw [if_pos h, if_pos h, mul_one, div_mul_cancel₀ (f t) hqne]
        · rw [if_neg h, if_neg h, mul_zero, mul_zero]
      simp_rw [key]
      rw [Finset.sum_ite_eq]
      simp
    have e2 : ∑ t : K, f t / (Fintype.card K : ℂ) * 1 = 0 := by
      simp_rw [mul_one, ← Finset.sum_div]
      rw [hfsum, zero_div]
    rw [e1, e2, sub_zero]
  rw [hfeq]
  exact Submodule.sum_mem U (fun t _ => U.smul_mem _ (hspikeU t))

/-- **Classification.** Every irreducible complex representation of the affine group `G` has
dimension `1` or `q - 1`. (With the sum-of-squares formula `(q-1)·1² + (q-1)² = q(q-1) = |G|`,
the irreducibles are exactly the `q-1` characters and the single `(q-1)`-dimensional `V`.) -/
theorem irreducible_dim [Fintype K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Affine K) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (Affine K)) σ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = Fintype.card K - 1 := by
  sorry

end Etingof.Problem4_12_6

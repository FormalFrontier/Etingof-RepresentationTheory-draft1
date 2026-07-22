import Mathlib
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Chapter4.Example4_3_FiniteAbelianGroups
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Infrastructure.SimpleModuleCount

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

The classification (fully proved here):

* `one_dim_reps_card`: the one-dimensional representations are the group homomorphisms
  `G → ℂˣ`, pulled back from the abelianization `G^{ab} ≅ Kˣ`; there are exactly `q-1` of them
  when `3 ≤ q`. (For `q = 2`, `G ≅ ℤ/2` is abelian of order `2`, so it has `2 ≠ q-1` characters;
  the `3 ≤ q` hypothesis is required.)
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

open CategoryTheory

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
(pulled back from `G^{ab} ≅ Kˣ`), and there are exactly `q - 1` of them.

The hypothesis `3 ≤ q` (equivalently `Nontrivial Kˣ`) is necessary: for `q = 2` the group
`Kˣ` is trivial, so `G ≅ ℤ/2` is abelian of order `2` and has `2 ≠ q - 1 = 1` characters.
The commutator argument below produces every translation `⟨1,c⟩` as a single commutator
`[⟨a,0⟩, ⟨1,d⟩] = ⟨1,(a-1)d⟩`, which requires a unit `a ≠ 1`; that unit exists exactly when
`3 ≤ q`. -/
theorem one_dim_reps_card [Fintype K] (hK : 3 ≤ Fintype.card K) :
    Nat.card (Affine K →* ℂˣ) = Fintype.card K - 1 := by
  classical
  -- The projection `G → Kˣ`, `⟨a,b⟩ ↦ a`, and its section `Kˣ → G`, `a ↦ ⟨a,0⟩`.
  let projA : Affine K →* Kˣ :=
    { toFun := fun g => g.a, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let s : Kˣ →* Affine K :=
    { toFun := fun a => ⟨a, 0⟩
      map_one' := rfl
      map_mul' := fun a a' => by ext <;> simp }
  -- In the abelian group `ℂˣ`, every commutator is trivial.
  have key : ∀ u v : ℂˣ, u * v * u⁻¹ * v⁻¹ = 1 := fun u v => by
    rw [mul_comm u v]; group
  -- Any character `φ : G → ℂˣ` kills every translation `⟨1,c⟩`: it is a commutator.
  have htrans : ∀ (φ : Affine K →* ℂˣ) (c : K), φ (⟨1, c⟩ : Affine K) = 1 := by
    intro φ c
    -- Pick a unit `a₀ ≠ 1`; possible since `2 ≤ |Kˣ| = q - 1`.
    have hcard : 2 ≤ Fintype.card Kˣ := by rw [Fintype.card_units]; omega
    have : Nontrivial Kˣ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a₀, ha₀⟩ := exists_ne (1 : Kˣ)
    have hu : ((a₀ : K) - 1) ≠ 0 := sub_ne_zero.mpr fun h => ha₀ (Units.ext h)
    -- `⟨1, a·c' - c'⟩ = [⟨a,0⟩, ⟨1,c'⟩]`, so `φ` sends it to `1`.
    have hkey : ∀ (a : Kˣ) (c' : K), φ (⟨1, (a : K) * c' - c'⟩ : Affine K) = 1 := by
      intro a c'
      have ha : (a : K) ≠ 0 := Units.ne_zero a
      have hcomm : (⟨1, (a : K) * c' - c'⟩ : Affine K) =
          ⟨a, 0⟩ * ⟨1, c'⟩ * ⟨a, 0⟩⁻¹ * ⟨1, c'⟩⁻¹ := by
        ext
        · simp
        · simp only [mul_b, mul_a, inv_a, inv_b, Units.val_mul,
            Units.val_inv_eq_inv_val, Units.val_one, inv_one, mul_zero, add_zero, mul_one,
            mul_neg, one_mul]
          field_simp
          ring
      rw [hcomm]
      simp only [map_mul, map_inv]
      exact key _ _
    -- Solve `(a₀ - 1)·c' = c` and read off `φ ⟨1,c⟩ = 1`.
    have h := hkey a₀ (((a₀ : K) - 1)⁻¹ * c)
    have hval : (a₀ : K) * (((a₀ : K) - 1)⁻¹ * c) - ((a₀ : K) - 1)⁻¹ * c = c := by
      field_simp
    rwa [hval] at h
  -- Precomposition with `projA` is a bijection `(Kˣ →* ℂˣ) ≃ (G →* ℂˣ)`.
  let E : (Affine K →* ℂˣ) ≃ (Kˣ →* ℂˣ) :=
    { toFun := fun φ => φ.comp s
      invFun := fun χ => χ.comp projA
      left_inv := fun φ => MonoidHom.ext fun g => by
        -- `((φ.comp s).comp projA) g = φ ⟨g.a, 0⟩` definitionally
        change φ (⟨g.a, 0⟩ : Affine K) = φ g
        have hg : g = (⟨g.a, 0⟩ : Affine K) * ⟨1, (↑g.a)⁻¹ * g.b⟩ := by
          ext
          · simp
          · simp
        conv_rhs => rw [hg]
        rw [map_mul, htrans φ _, mul_one]
      right_inv := fun χ => MonoidHom.ext fun a => rfl }
  rw [Nat.card_congr E]
  -- `|Kˣ →* ℂˣ| = |Kˣ| = q - 1` by duality for finite abelian groups (`ℂ` has all roots of unity).
  haveI : NeZero ((Monoid.exponent Kˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Kˣ ℂ, Nat.card_eq_fintype_card,
    Fintype.card_units]

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

open Module in
/-- Pigeonhole: an injection `c : ι → Fin n` whose image carries the full positive-weight sum
`∑ f j` is surjective. -/
private theorem surj_of_injective_of_sum_eq {n : ℕ} {ι : Type*} [Fintype ι]
    (f : Fin n → ℕ) (hf : ∀ j, 0 < f j) (c : ι → Fin n) (hcinj : Function.Injective c)
    (hsum : ∑ i, f (c i) = ∑ j, f j) : Function.Surjective c := by
  classical
  have himg : ∑ j ∈ Finset.image c Finset.univ, f j = ∑ i, f (c i) :=
    Finset.sum_image (fun a _ b _ hab => hcinj hab)
  have hsplit := Finset.sum_sdiff (f := f) (Finset.subset_univ (Finset.image c Finset.univ))
  rw [himg, hsum] at hsplit
  have hzero : ∑ j ∈ Finset.univ \ Finset.image c Finset.univ, f j = 0 := by omega
  intro j
  have hjmem : j ∈ Finset.image c Finset.univ := by
    by_contra hj
    exact absurd ((Finset.sum_eq_zero_iff.mp hzero) j
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)) (hf j).ne'
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hjmem
  exact ⟨i, hi⟩

/-- The one-dimensional representation on `ℂ` attached to a character `χ : G →* ℂˣ`:
`g` acts by multiplication by `χ g`. -/
def charRep (χ : Affine K →* ℂˣ) : Representation ℂ (Affine K) ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The character of `charRep χ` is `g ↦ χ g`. -/
@[simp] lemma charRep_character (χ : Affine K →* ℂˣ) (g : Affine K) :
    (FDRep.of (charRep χ)).character g = (χ g : ℂ) := by
  have hg : charRep χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (charRep χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp

/-- The one-dimensional `charRep χ` is simple as a `ℂ[G]`-module: its only `ℂ`-subspaces are
`⊥` and `⊤`, and all of them are invariant. -/
lemma charRep_asModule_simple (χ : Affine K →* ℂˣ) :
    IsSimpleModule (MonoidAlgebra ℂ (Affine K)) (charRep χ).asModule := by
  haveI hℂ : IsSimpleModule ℂ ℂ := inferInstance
  rw [isSimpleModule_iff,
    ← (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := charRep χ)).isSimpleOrder_iff]
  haveI : Nontrivial (Subrepresentation (charRep χ)) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have hbt : (⊥ : Submodule ℂ ℂ) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact absurd hbt bot_ne_top
  refine ⟨fun W' => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top W'.toSubmodule with h | h
  · left; exact Subrepresentation.toSubmodule_injective h
  · right; exact Subrepresentation.toSubmodule_injective h

/-- Any one-dimensional `charRep χ` is simple as an object of `FDRep ℂ (Affine K)`. -/
lemma charRep_simple (χ : Affine K →* ℂˣ) :
    Simple (FDRep.of (charRep χ)) :=
  haveI := charRep_asModule_simple χ
  Etingof.simple_fdRepOf_of_isSimpleModule (charRep χ)

/-- The permutation representation of `G` on functions `K → ℂ`: `g` acts by `f ↦ f ∘ (g⁻¹ · -)`. -/
def permRep : Representation ℂ (Affine K) (K → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (act g⁻¹)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext x
    simp only [LinearMap.funLeft_apply, inv_one, act_one, Module.End.one_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext x
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev]
    rw [act_mul]

@[simp] lemma permRep_apply (g : Affine K) (f : K → ℂ) (x : K) :
    permRep g f x = f (act g⁻¹ x) := rfl

/-- The zero-sum subspace as a subrepresentation of `permRep`. -/
def Vsub [Fintype K] : Subrepresentation (permRep (K := K)) where
  toSubmodule := zeroSum K
  apply_mem_toSubmodule g v hv := zeroSum_invariant permRep permRep_apply g v hv

/-- **`V` is irreducible as a `ℂ[G]`-module.** The zero-sum subrepresentation `Vsub`,
viewed as a module over the group algebra, is simple. This repackages `zeroSum_irreducible`
(every invariant subspace of `zeroSum K` is `⊥` or everything) as `IsSimpleModule`. -/
theorem Vrep_isSimpleModule [Fintype K] (hq : 2 ≤ Fintype.card K) :
    IsSimpleModule (MonoidAlgebra ℂ (Affine K)) (Vsub (K := K)).toRepresentation.asModule := by
  classical
  haveI hnt0 : Nontrivial ↥(zeroSum K) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [zeroSum_finrank]; omega
  rw [isSimpleModule_iff,
    ← (Subrepresentation.subrepresentationSubmoduleOrderIso
        (ρ := (Vsub (K := K)).toRepresentation)).isSimpleOrder_iff]
  haveI hntSub : Nontrivial (Subrepresentation (Vsub (K := K)).toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have hbt : (⊥ : Submodule ℂ ↥(zeroSum K)) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact absurd hbt bot_ne_top
  refine ⟨fun W' => ?_⟩
  set U : Submodule ℂ (K → ℂ) := W'.toSubmodule.map (Vsub (K := K)).toSubmodule.subtype with hUdef
  have hUle : U ≤ zeroSum K := by
    rw [hUdef]; rintro x ⟨y, -, rfl⟩; exact y.2
  have hUinv : ∀ (g : Affine K), ∀ f ∈ U, permRep g f ∈ U := by
    intro g f hf
    rw [hUdef, Submodule.mem_map] at hf ⊢
    obtain ⟨y, hy, rfl⟩ := hf
    exact ⟨(Vsub (K := K)).toRepresentation g y, W'.apply_mem_toSubmodule g hy, rfl⟩
  rcases zeroSum_irreducible permRep permRep_apply U hUle hUinv with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    have h2 : W'.toSubmodule.map (Vsub (K := K)).toSubmodule.subtype
        = (⊥ : Submodule ℂ ↥(Vsub (K := K)).toSubmodule).map (Vsub (K := K)).toSubmodule.subtype := by
      rw [Submodule.map_bot, ← hUdef]; exact h
    exact Submodule.map_injective_of_injective
      (Vsub (K := K)).toSubmodule.injective_subtype h2
  · right
    apply Subrepresentation.toSubmodule_injective
    have h2 : W'.toSubmodule.map (Vsub (K := K)).toSubmodule.subtype
        = (⊤ : Submodule ℂ ↥(Vsub (K := K)).toSubmodule).map (Vsub (K := K)).toSubmodule.subtype := by
      rw [Submodule.map_subtype_top, ← hUdef]; exact h
    exact Submodule.map_injective_of_injective
      (Vsub (K := K)).toSubmodule.injective_subtype h2

/-- **Universe transport.** Any finite-dimensional representation with simple `asModule`
yields a simple `FDRep ℂ (Affine K)` object of the same dimension (on a `Type 0` carrier),
so the Wedderburn enumeration applies to it. -/
theorem exists_simpleFDRep [Fintype K] [DecidableEq K]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Affine K) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (Affine K)) ρ.asModule) :
    ∃ (U : FDRep ℂ (Affine K)), Simple U ∧ Module.finrank ℂ U = Module.finrank ℂ V := by
  classical
  haveI : NeZero (Nat.card (Affine K) : ℂ) := by
    refine ⟨?_⟩
    rw [Nat.card_eq_fintype_card, card_eq]
    have h2 : 1 < Fintype.card K := Fintype.one_lt_card
    have hne : Fintype.card K * (Fintype.card K - 1) ≠ 0 :=
      Nat.mul_ne_zero (by omega) (by omega)
    exact_mod_cast hne
  letI M := Representation.asModule ρ
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Affine K)) M := hρ
  haveI : Module.Finite ℂ M := Module.Finite.equiv (Representation.asModuleEquiv ρ).symm
  haveI : Module.Free ℂ M := Module.Free.of_divisionRing ℂ M
  set dM := Module.finrank ℂ M with hdM
  let eM : M ≃ₗ[ℂ] (Fin dM → ℂ) := (Module.finBasis ℂ M).equivFun
  letI modN : Module (MonoidAlgebra ℂ (Affine K)) (Fin dM → ℂ) :=
    Etingof.transportModule (R := MonoidAlgebra ℂ (Affine K)) eM
  haveI towN : IsScalarTower ℂ (MonoidAlgebra ℂ (Affine K)) (Fin dM → ℂ) :=
    Etingof.transportModule_isScalarTower eM
  let eR : M ≃ₗ[MonoidAlgebra ℂ (Affine K)] (Fin dM → ℂ) := Etingof.transportLinearEquiv eM
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Affine K)) (Fin dM → ℂ) :=
    IsSimpleModule.congr eR.symm
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Affine K))
      (Etingof.repOfModule (k := ℂ) (G := Affine K) (Fin dM → ℂ)).asModule :=
    IsSimpleModule.congr (Etingof.repOfModuleAsModuleEquiv (k := ℂ) (G := Affine K) (Fin dM → ℂ))
  refine ⟨FDRep.of (Etingof.repOfModule (k := ℂ) (G := Affine K) (Fin dM → ℂ)),
    Etingof.simple_fdRepOf_of_isSimpleModule (Etingof.repOfModule (k := ℂ) (G := Affine K) (Fin dM → ℂ)), ?_⟩
  have h1 : Module.finrank ℂ (FDRep.of (Etingof.repOfModule (k := ℂ) (G := Affine K) (Fin dM → ℂ))) = dM := by
    show Module.finrank ℂ (Fin dM → ℂ) = dM
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [h1, hdM]
  exact (Representation.asModuleEquiv ρ).finrank_eq

/-- **Classification.** Every irreducible complex representation of the affine group `G` has
dimension `1` or `q - 1`. (With the sum-of-squares formula `(q-1)·1² + (q-1)² = q(q-1) = |G|`,
the irreducibles are exactly the `q-1` characters and the single `(q-1)`-dimensional `V`.) -/
theorem irreducible_dim [Fintype K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Affine K) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (Affine K)) σ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = Fintype.card K - 1 := by
  classical
  -- `K` is a field, so `q = |K| ≥ 2`.
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rcases eq_or_lt_of_le hq2 with hq_eq | hq_gt
  · -- `q = 2`: `Kˣ` is trivial, so `G` is abelian and every irreducible is `1`-dimensional.
    have hcardU : Fintype.card Kˣ = 1 := by rw [Fintype.card_units]; omega
    haveI : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    letI grp : Group (Affine K) := inferInstance
    letI : CommGroup (Affine K) :=
      { grp with
        mul_comm := by
          intro x y
          have hxa : x.a = 1 := Subsingleton.elim _ _
          have hya : y.a = 1 := Subsingleton.elim _ _
          ext
          · simp [hxa, hya]
          · simp only [mul_b, hxa, hya, Units.val_one, one_mul]; ring }
    haveI := hσ
    exact Or.inl (Etingof.Example4_3_FiniteAbelianGroups σ)
  · -- `q ≥ 3`: the sum-of-squares classification.
    have hq3 : 3 ≤ Fintype.card K := hq_gt
    -- `|G| = q(q-1)` is invertible in `ℂ`, so the Wedderburn enumeration applies.
    haveI hNe : NeZero (Nat.card (Affine K) : ℂ) := by
      refine ⟨?_⟩
      rw [Nat.card_eq_fintype_card, card_eq]
      exact_mod_cast Nat.mul_ne_zero (by omega) (by omega)
    -- A complete family `V` of pairwise non-isomorphic simples with `∑ dim² = |G|`.
    obtain ⟨n, V, hVsimple, _hVinj, hVsurj, hVsum⟩ :=
      exists_simples_sum_finrank_sq_eq_card ℂ (Affine K)
    -- There are exactly `q - 1` characters.
    haveI : Finite (Affine K →* ℂˣ) :=
      Nat.finite_of_card_ne_zero (by rw [one_dim_reps_card hq3]; omega)
    haveI : Fintype (Affine K →* ℂˣ) := Fintype.ofFinite _
    have hcardChar : Fintype.card (Affine K →* ℂˣ) = Fintype.card K - 1 := by
      rw [← Nat.card_eq_fintype_card]; exact one_dim_reps_card hq3
    -- The zero-sum representation `V` as a simple `FDRep` of dimension `q - 1`.
    obtain ⟨UV, hUVsimple, hUVfr⟩ :=
      exists_simpleFDRep (Vsub (K := K)).toRepresentation (Vrep_isSimpleModule (by omega))
    have hUVdim : Module.finrank ℂ UV = Fintype.card K - 1 := by
      rw [hUVfr]; exact zeroSum_finrank
    -- The explicit family: the `q - 1` characters (dim `1`) and `V` (dim `q - 1`).
    let E : (Affine K →* ℂˣ) ⊕ Unit → FDRep ℂ (Affine K) :=
      Sum.elim (fun χ => FDRep.of (charRep χ)) (fun _ => UV)
    have hEfinL : ∀ χ : Affine K →* ℂˣ, Module.finrank ℂ (E (Sum.inl χ)) = 1 := fun χ => by
      show Module.finrank ℂ ℂ = 1; exact Module.finrank_self ℂ
    have hEfinR : ∀ u : Unit, Module.finrank ℂ (E (Sum.inr u)) = Fintype.card K - 1 :=
      fun _ => hUVdim
    have hEsimple : ∀ i, Simple (E i) := by
      rintro (χ | u)
      · exact charRep_simple χ
      · exact hUVsimple
    have hEinj : ∀ i j, Nonempty (E i ≅ E j) → i = j := by
      rintro (χ | u) (χ' | u') ⟨α⟩
      · have hχ : χ = χ' := by
          ext g
          have hg := congrFun (FDRep.char_iso α) g
          rw [show E (Sum.inl χ) = FDRep.of (charRep χ) from rfl,
              show E (Sum.inl χ') = FDRep.of (charRep χ') from rfl,
              charRep_character, charRep_character] at hg
          exact hg
        rw [hχ]
      · exfalso
        have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
        rw [hEfinL χ, hEfinR u'] at hfr; omega
      · exfalso
        have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
        rw [hEfinR u, hEfinL χ'] at hfr; omega
      · rw [Subsingleton.elim u u']
    -- Inject the family into the enumeration.
    choose c hc using fun i => hVsurj (E i) (hEsimple i)
    have hc_inj : Function.Injective c := by
      intro i j hij
      obtain ⟨αi⟩ := hc i; obtain ⟨αj⟩ := hc j
      exact hEinj i j ⟨αi ≪≫ eqToIso (congrArg V hij) ≪≫ αj.symm⟩
    have hfinrankc : ∀ i, Module.finrank ℂ (E i) = Module.finrank ℂ (V (c i)) := fun i =>
      LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hc i).some)
    -- Squared dimensions of the family already sum to `|G|`.
    have harith : ∀ r : ℕ, 1 ≤ r → r - 1 + (r - 1) ^ 2 = r * (r - 1) := by
      intro r hr; obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have hEsum : ∑ i, (Module.finrank ℂ (E i)) ^ 2 = Fintype.card (Affine K) := by
      rw [Fintype.sum_sum_type, card_eq]
      have hL : ∑ χ : Affine K →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2
          = Fintype.card K - 1 := by
        have hone : ∀ χ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2 = 1 :=
          fun χ => by rw [hEfinL, one_pow]
        rw [Finset.sum_congr rfl (fun χ _ => hone χ), Finset.sum_const, Finset.card_univ,
          hcardChar, smul_eq_mul, mul_one]
      have hR : ∑ _u : Unit, (Module.finrank ℂ (E (Sum.inr _u))) ^ 2
          = (Fintype.card K - 1) ^ 2 := by simp [hEfinR]
      rw [hL, hR]; exact harith _ (by omega)
    have hVsum' : ∑ j, (Module.finrank ℂ (V j)) ^ 2 = Fintype.card (Affine K) := hVsum
    have hmatch : ∑ i, (Module.finrank ℂ (V (c i))) ^ 2
        = ∑ j, (Module.finrank ℂ (V j)) ^ 2 := by
      rw [hVsum', ← hEsum]
      exact Finset.sum_congr rfl (fun i _ => by rw [hfinrankc i])
    have hVpos : ∀ j, 0 < (Module.finrank ℂ (V j)) ^ 2 := by
      intro j
      haveI : Simple (V j) := hVsimple j
      haveI : IsSimpleModule (MonoidAlgebra ℂ (Affine K)) (Representation.asModule (V j).ρ) :=
        Etingof.isSimpleModule_asModule_of_simple (V j)
      haveI : Nontrivial (Representation.asModule (V j).ρ) :=
        IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Affine K)) (Representation.asModule (V j).ρ)
      haveI : Nontrivial ↥(V j) := (Representation.asModuleEquiv (V j).ρ).symm.toEquiv.nontrivial
      exact pow_pos Module.finrank_pos 2
    have hcsurj : Function.Surjective c :=
      surj_of_injective_of_sum_eq _ hVpos c hc_inj hmatch
    have hEdisj : ∀ i, Module.finrank ℂ (E i) = 1 ∨ Module.finrank ℂ (E i) = Fintype.card K - 1 := by
      rintro (χ | u)
      · exact Or.inl (hEfinL χ)
      · exact Or.inr (hEfinR u)
    -- Transport `σ` into the enumeration and read off its dimension.
    obtain ⟨U, hUsimple, hUfr⟩ := exists_simpleFDRep σ hσ
    obtain ⟨j, hjU⟩ := hVsurj U hUsimple
    obtain ⟨i, hci⟩ := hcsurj j
    have hUEi : Module.finrank ℂ U = Module.finrank ℂ (E i) := by
      rw [LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hjU.some), ← hci, ← hfinrankc i]
    rw [← hUfr, hUEi]
    exact hEdisj i

/-! ## The character of `V` and tensor products of the irreducibles

The book asks to compute the characters of the irreducibles and the tensor products of
irreducible representations. The one-dimensional characters are already `charRep_character`
(`χ_{charRep χ} = χ`). Here we compute the character of the `(q-1)`-dimensional irreducible `V`:
it is the *permutation character minus one*, i.e. `χ_V(g) = #{x : g·x = x} − 1`. This is the
standard fact that the permutation representation on functions `K → ℂ` splits as the trivial
representation (the constants) plus `V` (the zero-sum functions), so its character (the number
of fixed points of `g`) is `χ_triv + χ_V = 1 + χ_V`. -/

/-- The number of points of `K` fixed by the affine transformation `g`, as a `Finset`
cardinality. Solving `a·x + b = x`: it is `q` for the identity, `0` for a nontrivial
translation `⟨1, b⟩` (`b ≠ 0`), and `1` whenever `a ≠ 1`. -/
def affineFixCard [Fintype K] [DecidableEq K] (g : Affine K) : ℕ :=
  (Finset.univ.filter (fun x : K => act g x = x)).card

/-- The fixed-point set of `actEquiv g⁻¹` has cardinality `affineFixCard g` (the fixed points of
`g⁻¹` are exactly the fixed points of `g`). -/
lemma affineFixCard_eq_ncard [Fintype K] [DecidableEq K] (g : Affine K) :
    (Function.fixedPoints (actEquiv g⁻¹)).ncard = affineFixCard g := by
  rw [affineFixCard, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and]
  change act g⁻¹ x = x ↔ act g x = x
  rw [act_inv_eq_iff]
  exact eq_comm

/-- The identity fixes every point: `affineFixCard 1 = q`. -/
@[simp] lemma affineFixCard_one [Fintype K] [DecidableEq K] :
    affineFixCard (1 : Affine K) = Fintype.card K := by
  rw [affineFixCard, Finset.filter_true_of_mem (fun x _ => act_one x)]
  simp

/-- A nontrivial translation `⟨1, b⟩` (`b ≠ 0`) has no fixed point: `affineFixCard ⟨1,b⟩ = 0`. -/
lemma affineFixCard_translation [Fintype K] [DecidableEq K] {b : K} (hb : b ≠ 0) :
    affineFixCard (⟨1, b⟩ : Affine K) = 0 := by
  rw [affineFixCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  simp only [act, Units.val_one, one_mul]
  intro h
  exact hb (add_left_cancel (show x + b = x + 0 by rw [add_zero]; exact h))

/-- When `a ≠ 1`, the transformation `⟨a, b⟩` has a unique fixed point `x₀ = (a−1)⁻¹·(−b)`:
`affineFixCard g = 1`. -/
lemma affineFixCard_of_ne_one [Fintype K] [DecidableEq K] {g : Affine K} (hg : g.a ≠ 1) :
    affineFixCard g = 1 := by
  have hu : (g.a : K) - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hg (Units.ext h))
  rw [affineFixCard, Finset.card_eq_one]
  refine ⟨((g.a : K) - 1)⁻¹ * (-g.b), ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    simp only [act] at h
    have h2 : ((g.a : K) - 1) * x = -g.b := by linear_combination h
    rw [← h2, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  · rintro rfl
    simp only [act]
    field_simp
    ring

/-- The summation functional `f ↦ ∑ x, f x` on `K → ℂ`; `zeroSum K` is its kernel. -/
def sumLM (K : Type*) [Fintype K] : (K → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ x, f x
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

omit [Field K] in
@[simp] lemma sumLM_apply [Fintype K] (f : K → ℂ) : sumLM K f = ∑ x, f x := rfl

omit [Field K] in
lemma mem_zeroSum_iff [Fintype K] (f : K → ℂ) : f ∈ zeroSum K ↔ sumLM K f = 0 := Iff.rfl

/-- `permRep g` is the linear map of the permutation matrix of `actEquiv g⁻¹`. -/
lemma permRep_eq_toLin' [Fintype K] [DecidableEq K] (g : Affine K) :
    (permRep g) = (Equiv.Perm.permMatrix ℂ (actEquiv g⁻¹)).toLin' := by
  apply LinearMap.ext; intro f; funext x
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, permRep_apply]
  rfl

/-- **Permutation character.** The trace of `permRep g` is the number of fixed points of `g`. -/
lemma trace_permRep [Fintype K] [DecidableEq K] (g : Affine K) :
    LinearMap.trace ℂ (K → ℂ) (permRep g) = (affineFixCard g : ℂ) := by
  rw [permRep_eq_toLin', Matrix.trace_toLin'_eq, Matrix.trace_permutation, affineFixCard_eq_ncard]

/-- **Character of `V`.** The character of the `(q-1)`-dimensional irreducible `V` at `g` is the
number of fixed points of `g` on `K`, minus one:
`χ_V(g) = #{x : g·x = x} − 1`. In particular `χ_V(1) = q − 1`, `χ_V(⟨1,b⟩) = −1` for a nontrivial
translation, and `χ_V(⟨a,b⟩) = 0` when `a ≠ 1`. -/
theorem Vrep_character [Fintype K] [DecidableEq K] (g : Affine K) :
    (Vsub (K := K)).toRepresentation.character g = (affineFixCard g : ℂ) - 1 := by
  classical
  have hone_ne : (1 : K → ℂ) ≠ 0 := by
    intro h; have h0 := congrFun h (0 : K); simp at h0
  have hsum1 : sumLM K (1 : K → ℂ) = (Fintype.card K : ℂ) := by
    simp [Finset.card_univ]
  -- The line of constant functions, the trivial subrepresentation of `permRep`.
  set L : Submodule ℂ (K → ℂ) := Submodule.span ℂ {(1 : K → ℂ)} with hLdef
  set N : Fin 2 → Submodule ℂ (K → ℂ) := ![(Vsub (K := K)).toSubmodule, L] with hN
  -- `zeroSum K` and `L` are complementary.
  have hcompl : IsCompl (zeroSum K) L := by
    have hone : Module.finrank ℂ L = 1 := finrank_span_singleton hone_ne
    have hVdim : Module.finrank ℂ (zeroSum K) = Fintype.card K - 1 := zeroSum_finrank
    have hdim : Module.finrank ℂ (K → ℂ) ≤
        Module.finrank ℂ (zeroSum K) + Module.finrank ℂ L := by
      rw [hVdim, hone, Module.finrank_pi ℂ]; omega
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxV hxL
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxL
    have h0 : sumLM K (c • (1 : K → ℂ)) = 0 := (mem_zeroSum_iff _).mp hxV
    rw [map_smul, hsum1, smul_eq_mul] at h0
    have hqne : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    rcases mul_eq_zero.mp h0 with h | h
    · simp [h]
    · exact absurd h hqne
  -- The internal direct sum `K → ℂ = zeroSum K ⊕ L`.
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (by decide : (0 : Fin 2) ≠ 1) huniv).mpr hcompl
  -- `permRep g` preserves each summand.
  have hf0 : Set.MapsTo (permRep g) (N 0) (N 0) := (Vsub (K := K)).apply_mem_toSubmodule g
  have hf1 : Set.MapsTo (permRep g) (N 1) (N 1) := by
    intro x hx
    change x ∈ L at hx
    change permRep g x ∈ L
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, rho_const permRep permRep_apply g]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hf : ∀ i, Set.MapsTo (permRep g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_permRep, Fin.sum_univ_two] at htr
  -- Trace on the zero-sum summand is `χ_V`.
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((permRep g).restrict (hf 0))
      = (Vsub (K := K)).toRepresentation.character g := rfl
  -- Trace on the line of constants is `1` (the trivial character).
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((permRep g).restrict (hf 1)) = 1 := by
    have hid : (permRep g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hx : (x : K → ℂ) ∈ L := x.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
      change permRep g (x : K → ℂ) = (x : K → ℂ)
      rw [← hc, map_smul, rho_const permRep permRep_apply g]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton hone_ne
    rw [hid, LinearMap.trace_id, hfin]
    norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]
  exact htr.symm

/-- The character of `V` at the identity is `q - 1` (its dimension). -/
lemma Vrep_character_one [Fintype K] :
    (Vsub (K := K)).toRepresentation.character (1 : Affine K) = (Fintype.card K : ℂ) - 1 := by
  classical rw [Vrep_character, affineFixCard_one]

/-- The character of `V` at a nontrivial translation `⟨1, b⟩` (`b ≠ 0`) is `-1`. -/
lemma Vrep_character_translation [Fintype K] {b : K} (hb : b ≠ 0) :
    (Vsub (K := K)).toRepresentation.character (⟨1, b⟩ : Affine K) = -1 := by
  classical rw [Vrep_character, affineFixCard_translation hb]; simp

/-- The character of `V` at `⟨a, b⟩` with `a ≠ 1` is `0`. -/
lemma Vrep_character_of_ne_one [Fintype K] {g : Affine K} (hg : g.a ≠ 1) :
    (Vsub (K := K)).toRepresentation.character g = 0 := by
  classical rw [Vrep_character, affineFixCard_of_ne_one hg]; simp

/-! ### Tensor products of the irreducibles

The character is multiplicative under tensor product (`Representation.char_tensor`), so the
tensor products of the irreducibles are computed at the level of characters. Writing `χ, χ'` for
one-dimensional characters and `V` for the `(q-1)`-dimensional irreducible:

* `χ ⊗ χ'` has character `χ·χ'`, i.e. it is the character `charRep (χ * χ')`
  (`charRep_tprod_charRep_character`);
* `χ ⊗ V` has character `g ↦ χ(g)·χ_V(g)` (`charRep_tprod_Vrep_character`); being irreducible
  of dimension `q-1`, it is isomorphic to `V`;
* `V ⊗ V` has character `χ_V²` (`Vrep_tprod_Vrep_character`); by dimension `(q-1)²` it
  decomposes as the sum of all `q-1` characters and `q-2` copies of `V`. -/

/-- The character of the one-dimensional representation `charRep χ` is `χ`. -/
@[simp] lemma charRep_repCharacter (χ : Affine K →* ℂˣ) (g : Affine K) :
    (charRep χ).character g = (χ g : ℂ) := by
  have hg : charRep χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ (charRep χ g) = (χ g : ℂ)
  rw [hg, map_smul, LinearMap.trace_id]
  simp

/-- **`χ ⊗ χ' = χ·χ'`.** The tensor product of the two one-dimensional characters `χ` and `χ'`
has character `g ↦ χ(g)·χ'(g)`, the character of `charRep (χ * χ')`. -/
theorem charRep_tprod_charRep_character (χ χ' : Affine K →* ℂˣ) (g : Affine K) :
    (Representation.tprod (charRep χ) (charRep χ')).character g
      = (charRep (χ * χ')).character g := by
  rw [Representation.char_tensor, Pi.mul_apply, charRep_repCharacter, charRep_repCharacter,
    charRep_repCharacter, MonoidHom.mul_apply, Units.val_mul]

/-- **`χ ⊗ V`.** The tensor product of a one-dimensional character `χ` with `V` has character
`g ↦ χ(g)·χ_V(g)`. Since it is irreducible of dimension `q-1`, it is isomorphic to `V`. -/
theorem charRep_tprod_Vrep_character [Fintype K] (χ : Affine K →* ℂˣ) (g : Affine K) :
    (Representation.tprod (charRep χ) (Vsub (K := K)).toRepresentation).character g
      = (χ g : ℂ) * (Vsub (K := K)).toRepresentation.character g := by
  rw [Representation.char_tensor, Pi.mul_apply, charRep_repCharacter]

/-- **`V ⊗ V`.** The tensor product `V ⊗ V` has character `χ_V²`. By the dimension count
`(q-1)² = (q-1)·1 + (q-2)·(q-1)` it decomposes as the direct sum of all `q-1` one-dimensional
characters together with `q-2` copies of `V`. -/
theorem Vrep_tprod_Vrep_character [Fintype K] (g : Affine K) :
    (Representation.tprod (Vsub (K := K)).toRepresentation
        (Vsub (K := K)).toRepresentation).character g
      = ((Vsub (K := K)).toRepresentation.character g) ^ 2 := by
  rw [Representation.char_tensor, Pi.mul_apply, sq]

/-! ### Column orthogonality and the explicit `V ⊗ V` decomposition

The finer, isomorphism-level tensor decompositions
(`χ ⊗ V ≅ V` and `V ⊗ V ≅ (⊕ all q−1 characters) ⊕ (q−2)·V`) reduce, via character
orthogonality, to the **column orthogonality** of the character group of `G`:

`∑_{χ : G →* ℂˣ} χ(g) = if g.a = 1 then q−1 else 0`.

Every character factors through the abelianization `G^{ab} ≅ Kˣ` (each translation `⟨1,c⟩` is
a commutator, so it is killed), so the sum is `q−1` when `g` is a translation (`g.a = 1`,
all `q−1` characters send `g` to `1`) and `0` otherwise (a character separating `g.a ≠ 1`
exists because `ℂ` has enough roots of unity, and left-translation of the dual group forces
the sum to vanish). From this we obtain the character identity behind
`V ⊗ V ≅ (⊕ characters) ⊕ (q−2)·V`. -/

/-- Every one-dimensional character `φ : G →* ℂˣ` kills the translations `⟨1, c⟩`: each is a
commutator `⟨1, (a−1)c'⟩ = [⟨a,0⟩, ⟨1,c'⟩]`, and `ℂˣ` is abelian. The hypothesis `3 ≤ q`
provides a unit `a ≠ 1`. (This is the `htrans` step of `one_dim_reps_card`, extracted for reuse.) -/
theorem char_translation_eq_one [Fintype K] (hK : 3 ≤ Fintype.card K)
    (φ : Affine K →* ℂˣ) (c : K) : φ (⟨1, c⟩ : Affine K) = 1 := by
  classical
  have key : ∀ u v : ℂˣ, u * v * u⁻¹ * v⁻¹ = 1 := fun u v => by
    rw [mul_comm u v]; group
  have hcard : 2 ≤ Fintype.card Kˣ := by rw [Fintype.card_units]; omega
  have : Nontrivial Kˣ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : Kˣ)
  have hu : ((a₀ : K) - 1) ≠ 0 := sub_ne_zero.mpr fun h => ha₀ (Units.ext h)
  have hkey : ∀ (a : Kˣ) (c' : K), φ (⟨1, (a : K) * c' - c'⟩ : Affine K) = 1 := by
    intro a c'
    have ha : (a : K) ≠ 0 := Units.ne_zero a
    have hcomm : (⟨1, (a : K) * c' - c'⟩ : Affine K) =
        ⟨a, 0⟩ * ⟨1, c'⟩ * ⟨a, 0⟩⁻¹ * ⟨1, c'⟩⁻¹ := by
      ext
      · simp
      · simp only [mul_b, mul_a, inv_a, inv_b, Units.val_mul,
          Units.val_inv_eq_inv_val, Units.val_one, inv_one, mul_zero, add_zero, mul_one,
          mul_neg, one_mul]
        field_simp
        ring
    rw [hcomm]
    simp only [map_mul, map_inv]
    exact key _ _
  have h := hkey a₀ (((a₀ : K) - 1)⁻¹ * c)
  have hval : (a₀ : K) * (((a₀ : K) - 1)⁻¹ * c) - ((a₀ : K) - 1)⁻¹ * c = c := by
    field_simp
  rwa [hval] at h

/-- The projection `G → Kˣ`, `⟨a, b⟩ ↦ a`, onto the abelianization `G^{ab} ≅ Kˣ`. -/
def projUnits : Affine K →* Kˣ where
  toFun g := g.a
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma projUnits_apply (g : Affine K) : projUnits g = g.a := rfl

/-- **Column orthogonality for the character group of `G`.** The sum over all `q − 1`
one-dimensional characters `χ : G →* ℂˣ` of `χ(g)` is `q − 1` when `g` is a translation
(`g.a = 1`) and `0` otherwise. -/
theorem sum_char_affine [Fintype K] [DecidableEq K] [Fintype (Affine K →* ℂˣ)]
    (hK : 3 ≤ Fintype.card K) (g : Affine K) :
    ∑ χ : Affine K →* ℂˣ, (χ g : ℂ)
      = if g.a = 1 then ((Fintype.card K : ℂ) - 1) else 0 := by
  classical
  by_cases hga : g.a = 1
  · -- `g = ⟨1, g.b⟩` is a translation, killed by every character.
    rw [if_pos hga]
    have hval : ∀ χ : Affine K →* ℂˣ, (χ g : ℂ) = 1 := by
      intro χ
      have hg : g = (⟨1, g.b⟩ : Affine K) := by ext <;> simp [hga]
      rw [hg, char_translation_eq_one hK χ g.b, Units.val_one]
    rw [Finset.sum_congr rfl (fun χ _ => hval χ), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    have hcnt : Fintype.card (Affine K →* ℂˣ) = Fintype.card K - 1 := by
      rw [← Nat.card_eq_fintype_card]; exact one_dim_reps_card hK
    rw [hcnt, Nat.cast_sub (by omega), Nat.cast_one]
  · -- `g.a ≠ 1`: a separating character forces the sum to vanish.
    rw [if_neg hga]
    haveI : NeZero ((Monoid.exponent Kˣ : ℕ) : ℂ) :=
      ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
    obtain ⟨ψ₀, hψ₀⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Kˣ ℂ (show g.a ≠ 1 from hga)
    set χ₀ : Affine K →* ℂˣ := ψ₀.comp projUnits with hχ₀
    have hχ₀g : χ₀ g = ψ₀ g.a := rfl
    have hne1 : (χ₀ g : ℂ) ≠ 1 := by
      intro h
      exact hψ₀ (Units.ext (by rw [Units.val_one, ← hχ₀g]; exact h))
    -- `χ₀(g) · S = ∑_χ (χ₀·χ)(g) = S` by reindexing the dual group, and `χ₀(g) ≠ 1`.
    refine eq_zero_of_mul_eq_self_left hne1 ?_
    rw [Finset.mul_sum]
    have hstep : ∀ χ : Affine K →* ℂˣ, (χ₀ g : ℂ) * (χ g : ℂ) = ((χ₀ * χ) g : ℂ) := by
      intro χ; rw [MonoidHom.mul_apply, Units.val_mul]
    simp_rw [hstep]
    exact Fintype.sum_bijective (fun χ => χ₀ * χ) (Group.mulLeft_bijective χ₀) _ _ (fun χ => rfl)

/-- **The `V ⊗ V` decomposition, at the level of characters.** The character identity
`χ_V(g)² = (∑_χ χ(g)) + (q−2)·χ_V(g)` holds, where the sum runs over all `q−1` one-dimensional
characters. This is the character-level content of the decomposition
`V ⊗ V ≅ (⊕ all q−1 one-dimensional characters) ⊕ (q−2)·V`: the multiplicity of each character
`χ` in `V ⊗ V` is `1` and the multiplicity of `V` is `q−2`. -/
theorem Vrep_tprod_Vrep_decomp_character [Fintype K]
    [Fintype (Affine K →* ℂˣ)] (hK : 3 ≤ Fintype.card K) (g : Affine K) :
    ((Vsub (K := K)).toRepresentation.character g) ^ 2
      = (∑ χ : Affine K →* ℂˣ, (χ g : ℂ))
        + ((Fintype.card K : ℂ) - 2) * (Vsub (K := K)).toRepresentation.character g := by
  classical
  rw [Vrep_character g, sum_char_affine hK]
  by_cases hga : g.a = 1
  · rw [if_pos hga]
    by_cases hgb : g.b = 0
    · -- `g = 1`: `(q−1)² = (q−1) + (q−2)(q−1)`.
      have hg1 : g = 1 := by ext <;> simp [hga, hgb]
      rw [hg1, affineFixCard_one]
      ring
    · -- nontrivial translation: `(−1)² = (q−1) + (q−2)(−1)`.
      have hfix : affineFixCard g = 0 := by
        have hg : g = (⟨1, g.b⟩ : Affine K) := by ext <;> simp [hga]
        rw [hg]; exact affineFixCard_translation hgb
      rw [hfix]; push_cast; ring
  · -- `g.a ≠ 1`: `0² = 0 + (q−2)·0`.
    rw [if_neg hga, affineFixCard_of_ne_one hga]
    push_cast; ring

end Etingof.Problem4_12_6

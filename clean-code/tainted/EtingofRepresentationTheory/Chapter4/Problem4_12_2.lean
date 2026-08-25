import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_3_S3
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Infrastructure.SimpleModuleCount

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

The (a)–(d) theorems below are all proved (`sorry`-free):

* **(a)** `exists_unique_rep`: for `z^p = 1` there is a *unique* representation `ρ` of `G` on
  `V` acting on the two generators by the shift and the multiplication operators. (Uniqueness
  holds because `xGen, yGen` generate `G`; this also determines `ρ(g)` for every `g`.)
* **(b)** `irreducible_iff`: any such `R_z` is irreducible iff `z ≠ 1`.
* **(c)** `oneDimRepEquiv`: the explicit bijection `χ ↦ χ ∘ abHom` parametrizing the
  one-dimensional representations (characters `G → ℂˣ`) by characters of the abelianization
  `G^{ab} ≅ (ZMod p)²`; `one_dim_reps_card`: hence there are exactly `p²` of them;
  `R1_decomposes`: `R_1` is an internal direct sum of `p` one-dimensional `G`-invariant
  subspaces (each of the `p` distinct characters of the cyclic quotient occurs exactly once).
* **(d)** `simple_iso_charRep_or_rhoHom`: the full classification — every finite-dimensional
  simple `G`-representation is isomorphic either to a `1`-dimensional character `charRep χ`
  (`χ : G → ℂˣ`) or to a `p`-dimensional `R_z = rhoHom z` (`z ≠ 1` a `p`-th root of unity).
  Uniqueness within each branch is `charRep_iso_iff` (characters iso iff equal) and
  `rhoHom_iso_iff` (`R_z` iso iff the roots agree); the two branches are disjoint by
  `charRep_not_iso_rhoHom` (dimension `1 ≠ p`). `irreducible_dim`: the dimension dichotomy
  read off the classification — every irreducible has dimension `1` or `p`. Together with (c)
  and the sum-of-squares formula `p²·1² + (p-1)·p² = p³ = |G|`, the irreducibles are exactly
  the `p²` characters and the `p-1` representations `R_z` (`z ≠ 1`) of dimension `p`.
  The grand-total headline is `card_irreducibles`: the number of isomorphism classes of
  irreducibles, `Nat.card (Etingof.IrrepClasses ℂ (Heisenberg p))`, equals `p² + (p-1)`; the
  structural enumeration bijection is `nonempty_irrepClasses_equiv`
  (`IrrepClasses ℂ (Heisenberg p) ≃ (Heisenberg p →* ℂˣ) ⊕ {z // zᵖ = 1 ∧ z ≠ 1}`), with the
  supporting counts `card_nontrivial_pthRoots` (`= p-1`) and `sum_sq_dim_eq_card`.
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
open CategoryTheory

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
          push Not at hcon
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
            · subst h; simp [inv_mul_cancel₀ hfa]
            · have ht0 : f t = 0 := by
                by_contra hne
                have : t ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ t, hne⟩
                rw [ha, Finset.mem_singleton] at this; exact h this
              simp [h, ht0]
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
            rw [Finset.mem_filter]; push Not
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
      change σ.toSubmodule = ⊤
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

/-- **Part (c), explicit classification of `1`-dimensional representations.** The one-dimensional
complex representations of the Heisenberg group `G` are its group homomorphisms `G →* ℂˣ`, and
since every such character kills the commutator subgroup they are exactly the pullbacks along the
abelianization map `abHom : G →* (ZMod p)²` of characters of `(ZMod p)²`. This records that
explicit parametrization as a bijection

`(Multiplicative (ZMod p × ZMod p) →* ℂˣ) ≃ (Heisenberg p →* ℂˣ)`, `χ ↦ χ ∘ abHom`,

mirroring the `GL₂` precedent `Etingof.Discussion_1dim_reps.characterCompDetEquiv`. The count
`p²` (`one_dim_reps_card`) is the cardinality of the domain. -/
noncomputable def oneDimRepEquiv (p : ℕ) [Fact p.Prime] :
    (Multiplicative (ZMod p × ZMod p) →* ℂˣ) ≃ (Heisenberg p →* ℂˣ) :=
  (MonoidHom.liftOfSurjective (abHom p) (abHom_surjective p)).symm.trans
    (Equiv.subtypeUnivEquiv (fun ρ => abHom_ker_le_ker ρ))

/-- The classification bijection sends a character `χ` of the abelianization `(ZMod p)²` to the
one-dimensional representation `g ↦ χ (abHom g)` of `G`. -/
@[simp]
theorem oneDimRepEquiv_apply [Fact p.Prime]
    (χ : Multiplicative (ZMod p × ZMod p) →* ℂˣ) :
    oneDimRepEquiv p χ = χ.comp (abHom p) := rfl

/-- **Part (c), count of `1`-dimensional representations.** The one-dimensional
complex representations of the Heisenberg group are its group homomorphisms to `ℂˣ`, and there
are exactly `p²` of them: `oneDimRepEquiv` bijects them with the characters of the abelianization
`(ZMod p)²`. -/
theorem one_dim_reps_card [Fact p.Prime] :
    Nat.card (Heisenberg p →* ℂˣ) = p ^ 2 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero ((Monoid.exponent (Multiplicative (ZMod p × ZMod p)) : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  rw [← Nat.card_congr (oneDimRepEquiv p),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative (ZMod p × ZMod p)) ℂ,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]
  ring

/-- **Part (c), decomposition of `R_1`.** When `z = 1` the representation `R_1` decomposes as
an internal direct sum of `p` one-dimensional `G`-invariant subspaces, and **each occurs
exactly once**: each line `S i` is the isotypic line of a character `χ i : G →* ℂˣ` (so `ρ g`
acts on `S i` as the scalar `χ i g`), and the `p` characters `χ` are pairwise distinct
(`Function.Injective χ`). Thus `R_1` is the multiplicity-free sum of the `p` distinct
characters of the cyclic quotient. -/
theorem R1_decomposes [Fact p.Prime]
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hx : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1))
    (hy : ∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = f t) :
    ∃ S : Fin p → Submodule ℂ (ZMod p → ℂ),
      (∀ i, ∀ (g : Heisenberg p), ∀ v ∈ S i, ρ g v ∈ S i) ∧
      (∀ i, Module.finrank ℂ (S i) = 1) ∧
      DirectSum.IsInternal S ∧
      ∃ χ : Fin p → (Heisenberg p →* ℂˣ),
        Function.Injective χ ∧
        ∀ i, ∀ (g : Heisenberg p), ∀ w ∈ S i, ρ g w = (χ i g : ℂ) • w := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- A primitive `p`-th root of unity `ζ`.
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ p :=
    ⟨_, Complex.isPrimitiveRoot_exp p (NeZero.ne p)⟩
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  -- The `p` characters `χ_j(t) = ζ^{(j·t)}` of the additive group `ZMod p`; these are the
  -- eigenvectors of the shift operator `ρ(xGen)`.
  set chi : ZMod p → (ZMod p → ℂ) := fun j t => ζ ^ (j * t).val with hchi
  -- Each character is nonzero (its value at `0` is `1`).
  have chi_ne_zero : ∀ j : ZMod p, chi j ≠ 0 := by
    intro j hcon
    have h0 : chi j 0 = 0 := by rw [hcon]; rfl
    have h1 : (1 : ℂ) = 0 := by
      calc (1 : ℂ) = ζ ^ (j * 0).val := by rw [mul_zero, ZMod.val_zero, pow_zero]
        _ = chi j 0 := rfl
        _ = 0 := h0
    exact one_ne_zero h1
  -- `ρ(xGen)` scales `χ_j` by `ζ^{-j}`: `χ_j` is an eigenvector.
  have hxeig : ∀ j : ZMod p, ρ (xGen p) (chi j) = (ζ ^ ((-j).val)) • chi j := by
    intro j
    funext t
    rw [hx, Pi.smul_apply, smul_eq_mul]
    change ζ ^ (j * (t - 1)).val = ζ ^ ((-j).val) * ζ ^ (j * t).val
    have he : j * (t - 1) = (-j) + j * t := by ring
    rw [he, zpow_val_add hζp]
  -- `ρ(yGen)` fixes `χ_j` (since `z = 1`).
  have hyeig : ∀ j : ZMod p, ρ (yGen p) (chi j) = chi j := by
    intro j; funext t; rw [hy]
  -- The line `span {χ_j}` is invariant under all of `G`.
  have hinv : ∀ j : ZMod p, ∀ (g : Heisenberg p), ∀ v ∈ Submodule.span ℂ {chi j},
      ρ g v ∈ Submodule.span ℂ {chi j} := by
    intro j
    have hline : ∀ (op : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)),
        op (chi j) ∈ Submodule.span ℂ {chi j} →
        ∀ v ∈ Submodule.span ℂ {chi j}, op v ∈ Submodule.span ℂ {chi j} := by
      intro op hop v hv
      have hle : Submodule.span ℂ {chi j} ≤ (Submodule.span ℂ {chi j}).comap op := by
        rw [Submodule.span_le]
        intro x hx'
        rw [Set.mem_singleton_iff] at hx'; subst hx'
        simpa using hop
      exact hle hv
    have hX : ρ (xGen p) (chi j) ∈ Submodule.span ℂ {chi j} := by
      rw [hxeig]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hY : ρ (yGen p) (chi j) ∈ Submodule.span ℂ {chi j} := by
      rw [hyeig]; exact Submodule.mem_span_singleton_self _
    let Sm : Submonoid (Heisenberg p) :=
      { carrier := {g | ∀ v ∈ Submodule.span ℂ {chi j}, ρ g v ∈ Submodule.span ℂ {chi j}}
        one_mem' := by intro v hv; rw [map_one]; simpa using hv
        mul_mem' := by intro a b ha hb v hv; rw [map_mul]; exact ha _ (hb v hv) }
    have hSle : Submonoid.closure ({xGen p, yGen p} : Set (Heisenberg p)) ≤ Sm :=
      Submonoid.closure_le.mpr (by
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · exact hline _ hX
        · exact hline _ hY)
    intro g v hv
    exact hSle (by rw [Heisenberg.closure_gens_eq_top]; exact Submonoid.mem_top g) v hv
  -- Index the characters by `Fin p`; the eigenvalues are distinct because `ζ` is primitive.
  set v : Fin p → (ZMod p → ℂ) := fun i => chi ((i : ℕ) : ZMod p) with hv_def
  set μ : Fin p → ℂ := fun i => ζ ^ ((-((i : ℕ) : ZMod p)).val) with hμ_def
  have horder : orderOf ζ = p := hζ.eq_orderOf.symm
  have hpow_inj : ∀ s t : ZMod p, ζ ^ s.val = ζ ^ t.val → s = t := by
    intro s t hst
    apply ZMod.val_injective p
    have hs : s.val < orderOf ζ := by rw [horder]; exact ZMod.val_lt s
    have ht : t.val < orderOf ζ := by rw [horder]; exact ZMod.val_lt t
    exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hs) (Set.mem_Iio.mpr ht) hst
  have hμinj : Function.Injective μ := by
    intro i i' h
    have h2 : -(((i : ℕ) : ZMod p)) = -(((i' : ℕ) : ZMod p)) := hpow_inj _ _ h
    have h3 : (((i : ℕ) : ZMod p)) = (((i' : ℕ) : ZMod p)) := neg_injective h2
    apply Fin.ext
    have e1 : (((i : ℕ) : ZMod p)).val = (i : ℕ) := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt i.isLt
    have e2 : (((i' : ℕ) : ZMod p)).val = (i' : ℕ) := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt i'.isLt
    rw [← e1, ← e2, h3]
  have hli : LinearIndependent ℂ v := by
    apply Module.End.eigenvectors_linearIndependent' (ρ (xGen p)) μ hμinj v
    intro i
    rw [Module.End.hasEigenvector_iff]
    exact ⟨Module.End.mem_eigenspace_iff.mpr (hxeig _), chi_ne_zero _⟩
  -- Read the scalar of the `G`-action on each line off the value at `0` (where `v i` is `1`).
  have hv0 : ∀ i : Fin p, v i 0 = 1 := by
    intro i
    change ζ ^ (((i : ℕ) : ZMod p) * 0).val = 1
    rw [mul_zero, ZMod.val_zero, pow_zero]
  have hxeig' : ∀ i : Fin p, ρ (xGen p) (v i) = μ i • v i :=
    fun i => hxeig ((i : ℕ) : ZMod p)
  -- Each `ρ g` is injective (it is invertible in the group representation).
  have hρinj : ∀ (g : Heisenberg p), Function.Injective (ρ g) := by
    intro g
    have hlinv : Function.LeftInverse (ρ g⁻¹) (ρ g) := by
      intro w
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact hlinv.injective
  -- Each line is `ρ g`-stable, so `ρ g (v i) = (ρ g (v i) 0) • v i`.
  have hscale : ∀ (i : Fin p) (g : Heisenberg p), ρ g (v i) = (ρ g (v i) 0) • v i := by
    intro i g
    have hmem : ρ g (v i) ∈ Submodule.span ℂ {v i} :=
      hinv ((i : ℕ) : ZMod p) g (v i) (Submodule.mem_span_singleton_self _)
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    have hval : ρ g (v i) 0 = a := by rw [← ha, Pi.smul_apply, smul_eq_mul, hv0 i, mul_one]
    rw [hval]; exact ha.symm
  have hc_ne : ∀ (i : Fin p) (g : Heisenberg p), ρ g (v i) 0 ≠ 0 := by
    intro i g h0
    have hz : ρ g (v i) = 0 := by rw [hscale i g, h0, zero_smul]
    exact chi_ne_zero ((i : ℕ) : ZMod p) (hρinj g (hz.trans (map_zero (ρ g)).symm))
  -- The scalar is multiplicative in `g`: `g ↦ ρ g (v i) 0` is a character.
  have hmul : ∀ (i : Fin p) (g h : Heisenberg p),
      ρ (g * h) (v i) 0 = ρ g (v i) 0 * ρ h (v i) 0 := by
    intro i g h
    have hgh : ρ (g * h) (v i) = ρ h (v i) 0 • ρ g (v i) := by
      rw [map_mul, Module.End.mul_apply]
      nth_rewrite 1 [hscale i h]
      rw [map_smul]
    rw [hgh, Pi.smul_apply, smul_eq_mul]; ring
  -- The `p` characters carried by the lines.
  let χ : Fin p → (Heisenberg p →* ℂˣ) := fun i =>
    { toFun := fun g => Units.mk0 (ρ g (v i) 0) (hc_ne i g)
      map_one' := by
        apply Units.ext
        change ρ (1 : Heisenberg p) (v i) 0 = 1
        rw [map_one, Module.End.one_apply]; exact hv0 i
      map_mul' := fun g h => by
        apply Units.ext
        change ρ (g * h) (v i) 0 = ρ g (v i) 0 * ρ h (v i) 0
        exact hmul i g h }
  -- On the `xGen` generator the character equals the (pairwise distinct) eigenvalue `μ i`.
  have hχx : ∀ i : Fin p, (χ i (xGen p) : ℂ) = μ i := by
    intro i
    change ρ (xGen p) (v i) 0 = μ i
    rw [hxeig' i, Pi.smul_apply, smul_eq_mul, hv0 i, mul_one]
  refine ⟨fun i => Submodule.span ℂ {v i}, ?_, ?_, ?_, χ, ?_, ?_⟩
  · intro i g w hw
    exact hinv ((i : ℕ) : ZMod p) g w hw
  · intro i
    exact finrank_span_singleton (chi_ne_zero _)
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact hli.iSupIndep_span_singleton
    · have hcard : Fintype.card (Fin p) = Module.finrank ℂ (ZMod p → ℂ) := by
        rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, ZMod.card]
      have hspan_top := hli.span_eq_top_of_card_eq_finrank hcard
      rw [← hspan_top, ← Set.iUnion_singleton_eq_range, Submodule.span_iUnion]
  · -- `χ` is injective: its value at `xGen` is the distinct eigenvalue `μ`.
    intro i i' hii
    apply hμinj
    have key : (χ i (xGen p) : ℂ) = (χ i' (xGen p) : ℂ) := by rw [hii]
    rwa [hχx i, hχx i'] at key
  · -- Each `S i` is the `χ i`-isotypic line: `ρ g` acts on it by the scalar `χ i g`.
    intro i g w hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨a, rfl⟩ := hw
    have hg : ρ g (v i) = (χ i g : ℂ) • v i := hscale i g
    rw [map_smul, hg, smul_comm]

/-- On the central generator `⟨0,0,1⟩`, `R_z` acts by the scalar `z^{(-1).val} = z⁻¹`. -/
theorem rhoHom_central [NeZero p] (z : ℂ) (hz : z ^ p = 1) :
    rhoHom z hz (⟨0, 0, 1⟩ : Heisenberg p) = z ^ ((-1 : ZMod p).val) • LinearMap.id := by
  refine LinearMap.ext fun f => funext fun t => ?_
  rw [rhoHom_apply, rhoLin_apply]
  simp only [zero_mul, zero_sub, sub_zero, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    Pi.smul_apply, smul_eq_mul]

/-- `R_z` is a `p`-dimensional representation. -/
theorem finrank_rhoHom [NeZero p] (z : ℂ) (hz : z ^ p = 1) :
    Module.finrank ℂ (FDRep.of (rhoHom z hz)) = p := by
  change Module.finrank ℂ (ZMod p → ℂ) = p
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card]

/-- The character of `R_z` on the central generator `⟨0,0,1⟩` equals `z^{(-1).val} · p`. This
value determines `z` (see `powNegOneVal_inj`), so it separates the `R_z` from one another. -/
theorem character_rhoHom_central [NeZero p] (z : ℂ) (hz : z ^ p = 1) :
    (FDRep.of (rhoHom z hz)).character (⟨0, 0, 1⟩ : Heisenberg p)
      = z ^ ((-1 : ZMod p).val) * (p : ℂ) := by
  have hc : (FDRep.of (rhoHom z hz)).character (⟨0, 0, 1⟩ : Heisenberg p)
      = LinearMap.trace ℂ _ (rhoHom z hz (⟨0, 0, 1⟩ : Heisenberg p)) := rfl
  rw [hc, rhoHom_central z hz, map_smul, LinearMap.trace_id, smul_eq_mul, finrank_rhoHom z hz]

/-- The exponent map `w ↦ w^{(-1).val}` is injective on `p`-th roots of unity: it equals
`w ↦ w⁻¹` there, since `w^{(-1).val} · w = w^p = 1`. -/
theorem powNegOneVal_inj [NeZero p] {w₁ w₂ : ℂ} (h₁ : w₁ ^ p = 1) (h₂ : w₂ ^ p = 1)
    (h : w₁ ^ ((-1 : ZMod p).val) = w₂ ^ ((-1 : ZMod p).val)) : w₁ = w₂ := by
  have hval : (-1 : ZMod p).val + 1 = p := by
    have hpos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
      rw [Nat.cast_pred hpos, ZMod.natCast_self]; ring
    have hv : (-1 : ZMod p).val = p - 1 := by
      rw [← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega
  have e₁ : w₁ ^ ((-1 : ZMod p).val) * w₁ = 1 := by rw [← pow_succ, hval, h₁]
  have e₂ : w₂ ^ ((-1 : ZMod p).val) * w₂ = 1 := by rw [← pow_succ, hval, h₂]
  rw [h] at e₁
  have hne : w₂ ^ ((-1 : ZMod p).val) ≠ 0 := by
    intro hz; rw [hz, zero_mul] at e₂; exact one_ne_zero e₂.symm
  exact mul_left_cancel₀ hne (e₁.trans e₂.symm)

/-- Pigeonhole: an injection `c : ι → Fin n` whose image carries the full positive-weight sum
`∑ f j` is surjective. -/
theorem surj_of_injective_of_sum_eq {n : ℕ} {ι : Type*} [Fintype ι]
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

/-- **Part (d), full classification.** Every finite-dimensional simple complex representation
`U` of the Heisenberg group is isomorphic to exactly one member of the complete family of
irreducibles: either a one-dimensional character `χ : Heisenberg p →* ℂˣ` (via `charRep`, the
`p²` one-dimensional reps of part (c)), or one of the `p`-dimensional representations `R_z`
for a `p`-th root of unity `z ≠ 1` (via `rhoHom`, the `p-1` irreducibles of part (b)).

The proof exhibits the `p²` one-dimensional characters and the `p-1` representations `R_z`
(`z ≠ 1` a `p`-th root of unity) as a family of pairwise non-isomorphic simples whose squared
dimensions sum to `p²·1 + (p-1)·p² = p³ = |G|`. Since the full sum of squared dimensions over
*all* simples is also `p³` and every term is positive, this family is complete (pigeonhole),
so every simple is isomorphic to one of them. Non-isomorphy of the two branches follows from
their differing dimensions (`1 ≠ p`); within a branch, characters are separated by their value
and the `R_z` by their central character `z^{(-1).val}·p`. -/
theorem simple_iso_charRep_or_rhoHom [Fact p.Prime]
    (U : FDRep ℂ (Heisenberg p)) [hUsimple : Simple U] :
    (∃ χ : Heisenberg p →* ℂˣ,
        Nonempty (U ≅ FDRep.of (Etingof.Example4_3_S3.charRep χ))) ∨
    (∃ z : ℂ, ∃ (hz : z ^ p = 1), z ≠ 1 ∧
        Nonempty (U ≅ FDRep.of (rhoHom z hz))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
  -- `|G| = p³` is invertible in `ℂ`, so the Wedderburn enumeration applies.
  haveI hNe : NeZero (Nat.card (Heisenberg p) : ℂ) := by
    refine ⟨?_⟩
    rw [Nat.card_eq_fintype_card, Heisenberg.card_eq]
    push_cast
    exact pow_ne_zero 3 hpℂ
  -- The complete family of simples with `∑ dim² = |G|`.
  obtain ⟨n, V, hVsimple, _hVinj, hVsurj, hVsum⟩ :=
    exists_simples_sum_finrank_sq_eq_card ℂ (Heisenberg p)
  -- A primitive `p`-th root of unity, indexing the `p-1` representations `R_z` (`z ≠ 1`).
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ p :=
    ⟨_, Complex.isPrimitiveRoot_exp p (NeZero.ne p)⟩
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  let zof : {k : ZMod p // k ≠ 0} → ℂ := fun k => ζ ^ (k.1).val
  have hzof_p : ∀ k, (zof k) ^ p = 1 := fun k => by
    change (ζ ^ (k.1).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hzof_ne1 : ∀ k, zof k ≠ 1 := by
    intro k h
    have h' : ζ ^ (k.1).val = 1 := h
    have hdvd : (p : ℕ) ∣ (k.1).val := (hζ.pow_eq_one_iff_dvd _).mp h'
    have hz0 : (k.1).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt k.1)
    exact k.2 (ZMod.val_injective p (by rw [hz0, ZMod.val_zero]))
  -- Finiteness of the character group, of order `p²` by part (c).
  haveI : Finite (Heisenberg p →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [one_dim_reps_card]; exact pow_ne_zero 2 (by omega))
  haveI : Fintype (Heisenberg p →* ℂˣ) := Fintype.ofFinite _
  have hcardChar : Fintype.card (Heisenberg p →* ℂˣ) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact one_dim_reps_card
  have hcardJ : Fintype.card {k : ZMod p // k ≠ 0} = p - 1 := by
    simp only [ne_eq]
    rw [Fintype.card_subtype_compl (fun k : ZMod p => k = 0), Fintype.card_subtype_eq, ZMod.card]
  -- The exhibited family: the `p²` characters, and the `p-1` representations `R_z`.
  let E : (Heisenberg p →* ℂˣ) ⊕ {k : ZMod p // k ≠ 0} → FDRep ℂ (Heisenberg p) :=
    Sum.elim (fun χ => FDRep.of (Etingof.Example4_3_S3.charRep χ))
      (fun k => FDRep.of (rhoHom (zof k) (hzof_p k)))
  -- Dimensions: `1` for a character, `p` for an `R_z`.
  have hEfinL : ∀ χ : Heisenberg p →* ℂˣ, Module.finrank ℂ (E (Sum.inl χ)) = 1 := by
    intro χ
    change Module.finrank ℂ ℂ = 1
    exact Module.finrank_self ℂ
  have hEfinR : ∀ k : {k : ZMod p // k ≠ 0}, Module.finrank ℂ (E (Sum.inr k)) = p := by
    intro k
    exact finrank_rhoHom (zof k) (hzof_p k)
  -- Each member is simple.
  have hEsimple : ∀ i, Simple (E i) := by
    rintro (χ | k)
    · exact Etingof.Example4_3_S3.charRep_simple χ
    · haveI : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p))
          (rhoHom (zof k) (hzof_p k)).asModule :=
        (irreducible_iff (zof k) (hzof_p k) (rhoHom (zof k) (hzof_p k))
          (rhoHom_xGen (zof k) (hzof_p k)) (rhoHom_yGen (zof k) (hzof_p k))).mpr (hzof_ne1 k)
      exact Etingof.simple_fdRepOf_of_isSimpleModule (rhoHom (zof k) (hzof_p k))
  -- The members are pairwise non-isomorphic (compared via dimension and central character).
  have hEinj : ∀ i j, Nonempty (E i ≅ E j) → i = j := by
    rintro (χ | k) (χ' | k') ⟨α⟩
    · -- two characters: equal characters force `χ = χ'`
      have hχ : χ = χ' := by
        ext g
        have hg := congrFun (FDRep.char_iso α) g
        rw [show E (Sum.inl χ) = FDRep.of (Etingof.Example4_3_S3.charRep χ) from rfl,
            show E (Sum.inl χ') = FDRep.of (Etingof.Example4_3_S3.charRep χ') from rfl,
            Etingof.Example4_3_S3.charRep_character,
            Etingof.Example4_3_S3.charRep_character] at hg
        exact hg
      rw [hχ]
    · -- dimension `1 ≠ p`
      exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinL χ, hEfinR k'] at hfr
      omega
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinR k, hEfinL χ'] at hfr
      omega
    · -- two `R_z`: the central character `z^{(-1).val}·p` forces `z = z'`, hence `k = k'`
      have hg := congrFun (FDRep.char_iso α) (⟨0, 0, 1⟩ : Heisenberg p)
      rw [show E (Sum.inr k) = FDRep.of (rhoHom (zof k) (hzof_p k)) from rfl,
          show E (Sum.inr k') = FDRep.of (rhoHom (zof k') (hzof_p k')) from rfl,
          character_rhoHom_central, character_rhoHom_central] at hg
      have hpow := mul_right_cancel₀ hpℂ hg
      have hzz : zof k = zof k' := powNegOneVal_inj (hzof_p k) (hzof_p k') hpow
      have hzz' : ζ ^ (k.1).val = ζ ^ (k'.1).val := hzz
      have hvv : (k.1).val = (k'.1).val :=
        hζ.pow_inj (ZMod.val_lt k.1) (ZMod.val_lt k'.1) hzz'
      have : k.1 = k'.1 := ZMod.val_injective p hvv
      exact congrArg Sum.inr (Subtype.ext this)
  -- Inject the family into the enumeration.
  choose c hc using fun i => hVsurj (E i) (hEsimple i)
  have hc_inj : Function.Injective c := by
    intro i j hij
    obtain ⟨αi⟩ := hc i; obtain ⟨αj⟩ := hc j
    exact hEinj i j ⟨αi ≪≫ eqToIso (congrArg V hij) ≪≫ αj.symm⟩
  have hfinrankc : ∀ i, Module.finrank ℂ (E i) = Module.finrank ℂ (V (c i)) := fun i =>
    LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hc i).some)
  -- Squared dimensions of the family sum to `p³`.
  have hEsum : ∑ i, (Module.finrank ℂ (E i)) ^ 2 = p ^ 3 := by
    rw [Fintype.sum_sum_type]
    have hL : ∑ χ : Heisenberg p →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2 = p ^ 2 := by
      have hone : ∀ χ : Heisenberg p →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2 = 1 := by
        intro χ; rw [hEfinL χ, one_pow]
      rw [Finset.sum_congr rfl (fun χ _ => hone χ), Finset.sum_const, Finset.card_univ,
        hcardChar, smul_eq_mul, mul_one]
    have hR : ∑ k : {k : ZMod p // k ≠ 0}, (Module.finrank ℂ (E (Sum.inr k))) ^ 2
        = (p - 1) * p ^ 2 := by
      have hpk : ∀ k : {k : ZMod p // k ≠ 0}, (Module.finrank ℂ (E (Sum.inr k))) ^ 2 = p ^ 2 := by
        intro k; rw [hEfinR k]
      rw [Finset.sum_congr rfl (fun k _ => hpk k), Finset.sum_const, Finset.card_univ, hcardJ,
        smul_eq_mul]
    rw [hL, hR]
    have hp1le : 1 ≤ p := hp1.le
    have hstep : (p - 1) * p ^ 2 + p ^ 2 = p * p ^ 2 := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp1le]
    rw [add_comm, hstep]; ring
  -- The full sum of squared dimensions is also `p³`.
  have hVsum3 : ∑ j, (Module.finrank ℂ (V j)) ^ 2 = p ^ 3 := by
    rw [hVsum, Heisenberg.card_eq]
  have hmatch : ∑ i, (Module.finrank ℂ (V (c i))) ^ 2 = ∑ j, (Module.finrank ℂ (V j)) ^ 2 := by
    rw [hVsum3, ← hEsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hfinrankc i])
  -- Every simple has positive dimension, so the injection `c` is surjective.
  have hVpos : ∀ j, 0 < (Module.finrank ℂ (V j)) ^ 2 := by
    intro j
    haveI : Simple (V j) := hVsimple j
    haveI : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) (Representation.asModule (V j).ρ) :=
      Etingof.isSimpleModule_asModule_of_simple (V j)
    haveI : Nontrivial (Representation.asModule (V j).ρ) :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Heisenberg p)) (Representation.asModule (V j).ρ)
    haveI : Nontrivial ↥(V j) := (Representation.asModuleEquiv (V j).ρ).symm.toEquiv.nontrivial
    have hpos : 0 < Module.finrank ℂ (V j) := Module.finrank_pos
    exact pow_pos hpos 2
  have hcsurj : Function.Surjective c :=
    surj_of_injective_of_sum_eq _ hVpos c hc_inj hmatch
  -- `U ≅ V j` for some `j`; surjectivity of `c` gives an `i` with `V (c i) = V j`, hence
  -- `U ≅ E i`.  Reading off which branch `i` lies in gives the classification.
  obtain ⟨j, hjU⟩ := hVsurj U hUsimple
  obtain ⟨i, hci⟩ := hcsurj j
  have hUEi : Nonempty (U ≅ E i) :=
    ⟨hjU.some ≪≫ eqToIso (congrArg V hci).symm ≪≫ (hc i).some.symm⟩
  rcases i with χ | k
  · exact Or.inl ⟨χ, hUEi⟩
  · exact Or.inr ⟨zof k, hzof_p k, hzof_ne1 k, hUEi⟩

/-- The `p²` one-dimensional characters are pairwise non-isomorphic: `FDRep.of (charRep χ)` and
`FDRep.of (charRep χ')` are isomorphic exactly when `χ = χ'`. Together with
`simple_iso_charRep_or_rhoHom` this pins down the character `χ` uniquely. -/
theorem charRep_iso_iff (χ χ' : Heisenberg p →* ℂˣ) :
    Nonempty (FDRep.of (Etingof.Example4_3_S3.charRep χ) ≅
        FDRep.of (Etingof.Example4_3_S3.charRep χ')) ↔ χ = χ' := by
  constructor
  · rintro ⟨α⟩
    ext g
    have hg := congrFun (FDRep.char_iso α) g
    rw [Etingof.Example4_3_S3.charRep_character, Etingof.Example4_3_S3.charRep_character] at hg
    exact hg
  · rintro rfl; exact ⟨Iso.refl _⟩

/-- The `p-1` representations `R_z` (`z ≠ 1`) are pairwise non-isomorphic: `FDRep.of (rhoHom z hz)`
and `FDRep.of (rhoHom z' hz')` are isomorphic exactly when `z = z'`. Together with
`simple_iso_charRep_or_rhoHom` this pins down the root of unity `z` uniquely.

(Distinctness is read off the central character `z^{(-1).val}·p` of `R_z`; the value at the
central generator `⟨0,0,1⟩` recovers `z`.) -/
theorem rhoHom_iso_iff [Fact p.Prime] {z z' : ℂ} (hz : z ^ p = 1) (hz' : z' ^ p = 1) :
    Nonempty (FDRep.of (rhoHom z hz) ≅ FDRep.of (rhoHom z' hz')) ↔ z = z' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
  constructor
  · rintro ⟨α⟩
    have hg := congrFun (FDRep.char_iso α) (⟨0, 0, 1⟩ : Heisenberg p)
    rw [character_rhoHom_central, character_rhoHom_central] at hg
    exact powNegOneVal_inj hz hz' (mul_right_cancel₀ hpℂ hg)
  · rintro rfl; exact ⟨Iso.refl _⟩

/-- A character `R_χ` (dimension `1`) and a representation `R_z` (dimension `p`) are never
isomorphic (`p > 1`), so the two branches of `simple_iso_charRep_or_rhoHom` are disjoint. -/
theorem charRep_not_iso_rhoHom [Fact p.Prime] (χ : Heisenberg p →* ℂˣ) {z : ℂ} (hz : z ^ p = 1) :
    ¬ Nonempty (FDRep.of (Etingof.Example4_3_S3.charRep χ) ≅ FDRep.of (rhoHom z hz)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  rintro ⟨α⟩
  have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
  rw [show Module.finrank ℂ (FDRep.of (Etingof.Example4_3_S3.charRep χ)) = 1 from
      Module.finrank_self ℂ, finrank_rhoHom z hz] at hfr
  omega

/-- **Part (d).** Every irreducible complex representation of the Heisenberg group has
dimension `1` or `p`. (Combined with (c) and the sum-of-squares formula
`p²·1² + (p-1)·p² = p³`, the irreducibles are exactly the `p²` characters together with the
`p-1` representations `R_z` for `z ≠ 1`, each of dimension `p`.)

This is the dimension dichotomy read off the full classification
`simple_iso_charRep_or_rhoHom`: a simple is either a `1`-dimensional character or a
`p`-dimensional `R_z`. -/
theorem irreducible_dim [Fact p.Prime]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Heisenberg p) W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) σ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = p := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Transport `σ` to a representation `U` in `ℂ`'s universe so the classification applies.
  letI M := Representation.asModule σ
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) M := hσ
  haveI : Module.Finite ℂ M := Module.Finite.equiv (Representation.asModuleEquiv σ).symm
  haveI : Module.Free ℂ M := Module.Free.of_divisionRing ℂ M
  set dM := Module.finrank ℂ M with hdM
  let eM : M ≃ₗ[ℂ] (Fin dM → ℂ) := (Module.finBasis ℂ M).equivFun
  letI modN : Module (MonoidAlgebra ℂ (Heisenberg p)) (Fin dM → ℂ) :=
    Etingof.transportModule (R := MonoidAlgebra ℂ (Heisenberg p)) eM
  haveI towN : IsScalarTower ℂ (MonoidAlgebra ℂ (Heisenberg p)) (Fin dM → ℂ) :=
    Etingof.transportModule_isScalarTower eM
  let eR : M ≃ₗ[MonoidAlgebra ℂ (Heisenberg p)] (Fin dM → ℂ) :=
    Etingof.transportLinearEquiv eM
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) (Fin dM → ℂ) :=
    IsSimpleModule.congr eR.symm
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p))
      (Etingof.repOfModule (Fin dM → ℂ)).asModule :=
    IsSimpleModule.congr (Etingof.repOfModuleAsModuleEquiv (Fin dM → ℂ))
  let U : FDRep ℂ (Heisenberg p) := FDRep.of (Etingof.repOfModule (Fin dM → ℂ))
  haveI hUsimple : Simple U :=
    Etingof.simple_fdRepOf_of_isSimpleModule (Etingof.repOfModule (Fin dM → ℂ))
  have hWU : Module.finrank ℂ W = Module.finrank ℂ U := by
    have h1 : Module.finrank ℂ U = dM := by
      change Module.finrank ℂ (Fin dM → ℂ) = dM
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have h2 : dM = Module.finrank ℂ W := by
      rw [hdM]; exact (Representation.asModuleEquiv σ).finrank_eq
    rw [h1, h2]
  rw [hWU]
  rcases simple_iso_charRep_or_rhoHom U with ⟨χ, hχ⟩ | ⟨z, hz, _, hziso⟩
  · left
    rw [LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hχ.some)]
    change Module.finrank ℂ ℂ = 1
    exact Module.finrank_self ℂ
  · right
    rw [LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv hziso.some)]
    exact finrank_rhoHom z hz

/-! ### Part (d) grand-total count headline

The exhaustion trichotomy (`simple_iso_charRep_or_rhoHom`) and the pairwise-non-isomorphism
lemmas (`charRep_iso_iff`, `rhoHom_iso_iff`, `charRep_not_iso_rhoHom`) assemble into an explicit
enumeration of the irreducibles: the isomorphism classes of simple `FDRep ℂ (Heisenberg p)` are
in bijection with `(Heisenberg p →* ℂˣ) ⊕ {z : ℂ // zᵖ = 1 ∧ z ≠ 1}`, i.e. the `p²`
one-dimensional characters together with the `p - 1` `p`-dimensional representations `R_z`
(`z ≠ 1`). Hence the total number of irreducibles is `p² + (p - 1)` — the "sum of squares"
classification of part (d), now exposed as a headline count rather than only as internal
`have`s inside `simple_iso_charRep_or_rhoHom`. -/

/-- The complete index set of irreducibles of the Heisenberg group: the one-dimensional
characters `χ : Heisenberg p →* ℂˣ` (part (c)) together with the `p`-dimensional representations
`R_z` for a `p`-th root of unity `z ≠ 1` (part (b)). -/
abbrev IrrepIndex (p : ℕ) : Type :=
  (Heisenberg p →* ℂˣ) ⊕ {z : ℂ // z ^ p = 1 ∧ z ≠ 1}

/-- There are exactly `p - 1` nontrivial complex `p`-th roots of unity: over `ℂ` the equation
`zᵖ = 1` has exactly `p` solutions (`IsPrimitiveRoot.card_nthRootsFinset`), one of which is `1`.
This counts the `p`-dimensional irreducibles `R_z` (`z ≠ 1`). -/
theorem card_nontrivial_pthRoots [Fact p.Prime] :
    Nat.card {z : ℂ // z ^ p = 1 ∧ z ≠ 1} = p - 1 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ p :=
    ⟨_, Complex.isPrimitiveRoot_exp p (NeZero.ne p)⟩
  -- The finset of `p`-th roots of unity with `1` removed.
  set S : Finset ℂ := (Polynomial.nthRootsFinset p (1 : ℂ)).erase 1 with hS
  have hmem : ∀ z : ℂ, (z ^ p = 1 ∧ z ≠ 1) ↔ z ∈ S := by
    intro z
    rw [hS, Finset.mem_erase, Polynomial.mem_nthRootsFinset hp0]
    tauto
  have hcard : S.card = p - 1 := by
    rw [hS, Finset.card_erase_of_mem (Polynomial.one_mem_nthRootsFinset hp0),
      hζ.card_nthRootsFinset]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_finsetCard, hcard]

/-- Finiteness of the nontrivial `p`-th roots of unity (a subtype of a finite root set). -/
instance [Fact p.Prime] : Finite {z : ℂ // z ^ p = 1 ∧ z ≠ 1} := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  refine Finite.of_injective (β := (Polynomial.nthRootsFinset p (1 : ℂ)))
    (fun z => ⟨z.1, (Polynomial.mem_nthRootsFinset hp0 1).mpr z.2.1⟩) ?_
  intro a b h
  exact Subtype.ext (congrArg (fun s : (Polynomial.nthRootsFinset p (1 : ℂ)) => (s : ℂ)) h)

/-- **Part (d), structural classification.** The isomorphism classes of irreducible complex
representations of the Heisenberg group are in bijection with `IrrepIndex p`: every simple is
isomorphic to exactly one of the `p²` characters `charRep χ` or one of the `p - 1`
representations `R_z` (`z ≠ 1`). Completeness is `simple_iso_charRep_or_rhoHom`; irredundancy is
`charRep_iso_iff` / `rhoHom_iso_iff` / `charRep_not_iso_rhoHom`. -/
theorem nonempty_irrepClasses_equiv [Fact p.Prime] :
    Nonempty (Etingof.IrrepClasses ℂ (Heisenberg p) ≃ IrrepIndex p) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- The full subcategory of simple objects, and the family realizing each index.
  let 𝒮 : ObjectProperty (FDRep ℂ (Heisenberg p)) := fun V => Simple V
  let E : IrrepIndex p → FDRep ℂ (Heisenberg p) :=
    Sum.elim (fun χ => FDRep.of (Etingof.Example4_3_S3.charRep χ))
      (fun z => FDRep.of (rhoHom z.1 z.2.1))
  have hEsimple : ∀ i, Simple (E i) := by
    rintro (χ | ⟨z, hz, hz1⟩)
    · exact Etingof.Example4_3_S3.charRep_simple χ
    · haveI : IsSimpleModule (MonoidAlgebra ℂ (Heisenberg p)) (rhoHom z hz).asModule :=
        (irreducible_iff z hz (rhoHom z hz) (rhoHom_xGen z hz) (rhoHom_yGen z hz)).mpr hz1
      exact Etingof.simple_fdRepOf_of_isSimpleModule (rhoHom z hz)
  -- Irredundancy: the family is injective up to isomorphism.
  have hEinj : ∀ i j, Nonempty (E i ≅ E j) → i = j := by
    rintro (χ | ⟨z, hz, hz1⟩) (χ' | ⟨z', hz', hz1'⟩) hiso
    · exact congrArg Sum.inl ((charRep_iso_iff χ χ').mp hiso)
    · exact absurd hiso (charRep_not_iso_rhoHom χ hz')
    · exact absurd (hiso.map Iso.symm) (charRep_not_iso_rhoHom χ' hz)
    · exact congrArg Sum.inr (Subtype.ext ((rhoHom_iso_iff hz hz').mp hiso))
  -- Package each index as a simple object of the subcategory, then pass to iso classes.
  let P : IrrepIndex p → 𝒮.FullSubcategory := fun i => ⟨E i, hEsimple i⟩
  let f : IrrepIndex p → Etingof.IrrepClasses ℂ (Heisenberg p) :=
    fun i => Quotient.mk (isIsomorphicSetoid _) (P i)
  have hf : Function.Bijective f := by
    constructor
    · -- Injective: equal classes give an iso `E i ≅ E j`, hence `i = j`.
      intro i j hij
      obtain ⟨iso⟩ := Quotient.exact hij
      exact hEinj i j ⟨𝒮.ι.mapIso iso⟩
    · -- Surjective: every simple is iso to some `E i` (`simple_iso_charRep_or_rhoHom`).
      intro c
      induction c using Quotient.inductionOn with
      | h Q =>
        haveI : Simple Q.obj := Q.property
        rcases simple_iso_charRep_or_rhoHom Q.obj with ⟨χ, ⟨α⟩⟩ | ⟨z, hz, hz1, ⟨α⟩⟩
        · exact ⟨Sum.inl χ, Quotient.sound ⟨𝒮.fullyFaithfulι.preimageIso α.symm⟩⟩
        · exact ⟨Sum.inr ⟨z, hz, hz1⟩, Quotient.sound ⟨𝒮.fullyFaithfulι.preimageIso α.symm⟩⟩
  exact ⟨(Equiv.ofBijective f hf).symm⟩

/-- **Part (d), grand-total count headline.** The number of isomorphism classes of irreducible
complex representations of the Heisenberg group is `p² + (p - 1)`: the `p²` one-dimensional
characters of part (c) together with the `p - 1` representations `R_z` of dimension `p` from
part (b). This is the assembled "sum of squares" classification of part (d). -/
theorem card_irreducibles [Fact p.Prime] :
    Nat.card (Etingof.IrrepClasses ℂ (Heisenberg p)) = p ^ 2 + (p - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Finite (Heisenberg p →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by
      rw [one_dim_reps_card]; exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨e⟩ := nonempty_irrepClasses_equiv (p := p)
  rw [Nat.card_congr e]
  change Nat.card ((Heisenberg p →* ℂˣ) ⊕ {z : ℂ // z ^ p = 1 ∧ z ≠ 1}) = p ^ 2 + (p - 1)
  rw [Nat.card_sum, one_dim_reps_card, card_nontrivial_pthRoots]

/-- The "sum of squares" identity underlying the classification: the squared dimensions of the
`p²` one-dimensional irreducibles and the `p - 1` irreducibles of dimension `p` sum to
`p³ = |Heisenberg p|`. -/
theorem sum_sq_dim_eq_card [Fact p.Prime] :
    p ^ 2 * 1 ^ 2 + (p - 1) * p ^ 2 = Fintype.card (Heisenberg p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [Heisenberg.card_eq, one_pow, mul_one, add_comm]
  -- `(p-1)·p² + p² = ((p-1)+1)·p² = p·p² = p³`
  rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp1]; ring

end Etingof.Problem4_12_2

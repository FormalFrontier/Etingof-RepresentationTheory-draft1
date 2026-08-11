import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Problem 3.8.5: periodic and antiperiodic functions

Let `A` be the algebra of real-valued continuous functions on `ℝ` that are periodic with
period `1`, and let `M` be the `A`-module of continuous functions `f` that are
antiperiodic: `f(x + 1) = −f(x)`.

* **(i)** `A` and `M` are indecomposable `A`-modules.
* **(ii)** `A` is not isomorphic to `M`, but `A ⊕ A ≅ M ⊕ M`.

We model `A` as the subalgebra `periodicSubalg` of `C(ℝ, ℝ)` cut out by `f(x+1) = f(x)`,
and `M` as the `A`-submodule `antiperiodicSubmod` of `C(ℝ, ℝ)` cut out by `f(x+1) = −f(x)`.
(`M` is closed under multiplication by a periodic function: if `g(x+1) = g(x)` and
`f(x+1) = −f(x)` then `(gf)(x+1) = −(gf)(x)`.) The regular module `A` and the module `M` are
then `↥periodicSubalg`-modules.

`A ⊕ A ≅ M ⊕ M` reflects that `M ⊗_A M ≅ A` (antiperiodic × antiperiodic = periodic), so `M`
is an invertible module of order `2` in the Picard group of `A`; it is a nontrivial line
bundle on the circle (the Möbius bundle), whence `M ≇ A` yet `M ⊕ M ≅ A ⊕ A`.

Part (i) (`periodic_isIndecomposable`, `antiperiodic_isIndecomposable`) follows from the fact
that the algebra of period-1 functions has no nontrivial idempotents (an idempotent
is pointwise `{0,1}`-valued, hence constant by connectedness of `ℝ`). Part (ii)
(`periodic_not_linearEquiv_antiperiodic`, `periodic_sq_linearEquiv_antiperiodic_sq`):
`A ≇ M` because any generator of `M` is a continuous antiperiodic function, which must vanish
somewhere by the intermediate value theorem; and `A ⊕ A ≅ M ⊕ M` via the rotation
`(f, g) ↦ (cos·f − sin·g, sin·f + cos·g)`, whose inverse is the transpose rotation
(using `cos² + sin² = 1`).
-/

namespace Etingof.Problem3_8_5

open scoped ContinuousMap

/-- The algebra `A` of continuous period-1 functions `ℝ → ℝ`, as a subalgebra of `C(ℝ, ℝ)`.
The carrier is the set of periodic functions; closure under multiplication, addition,
and the algebra map follows from the defining identity `f (x + 1) = f x`. -/
noncomputable def periodicSubalg : Subalgebra ℝ C(ℝ, ℝ) where
  carrier := {f | ∀ x : ℝ, f (x + 1) = f x}
  mul_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.mul_apply, hf x, hg x]
  add_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.add_apply, hf x, hg x]
  algebraMap_mem' := by
    intro r x
    simp

/-- The `A`-module `M` of continuous antiperiodic functions `f(x+1) = −f(x)`, as a submodule
of `C(ℝ, ℝ)` over the algebra `A = periodicSubalg`. Closure under addition and multiplication
by a periodic scalar follows from `f (x + 1) = - f x`. -/
noncomputable def antiperiodicSubmod : Submodule (periodicSubalg) C(ℝ, ℝ) where
  carrier := {f | ∀ x : ℝ, f (x + 1) = - f x}
  add_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.add_apply, hf x, hg x]
    ring
  zero_mem' := by
    intro x
    simp
  smul_mem' := by
    intro c f hf x
    have key : ∀ y : ℝ, (c • f) y = (c : C(ℝ, ℝ)) y * f y := by
      intro y
      rw [Algebra.smul_def]
      rfl
    rw [key (x + 1), key x, hf x, c.2 x]
    ring

/-- The value of a periodic function at a point, as a plain real number. -/
private lemma periodicSubalg_coe_mul (e : periodicSubalg) (x : ℝ) :
    ((e * e : periodicSubalg) : C(ℝ, ℝ)) x = ((e : C(ℝ, ℝ)) x) * ((e : C(ℝ, ℝ)) x) := by
  simp

/-- **Idempotents in `A` are trivial.** An idempotent element `e` of the algebra of
continuous period-1 functions is either `0` or `1`: pointwise `e(x)² = e(x)` forces
`e(x) ∈ {0, 1}`, and since `e` is continuous and `ℝ` is connected, `e` is constant. -/
lemma periodicSubalg_idempotent_eq_zero_or_one (e : periodicSubalg) (he : e * e = e) :
    e = 0 ∨ e = 1 := by
  -- The underlying continuous function.
  set f : C(ℝ, ℝ) := (e : C(ℝ, ℝ)) with hf
  -- Pointwise idempotence: `f x * f x = f x`.
  have hpt : ∀ x, f x * f x = f x := by
    intro x
    have := congrArg (fun z : periodicSubalg => (z : C(ℝ, ℝ)) x) he
    simpa using this
  -- Every value is `0` or `1`.
  have hdich : ∀ x, f x = 0 ∨ f x = 1 := by
    intro x
    have h := hpt x
    have : f x * (f x - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith [sub_eq_zero.mp h1])
  -- The set where `f = 1` is clopen.
  set s : Set ℝ := {x | f x = 1} with hs
  have hclosed : IsClosed s := by
    have : s = f ⁻¹' {1} := rfl
    rw [this]
    exact IsClosed.preimage (map_continuous f) isClosed_singleton
  have hcompl_closed : IsClosed sᶜ := by
    have : sᶜ = f ⁻¹' {0} := by
      ext x
      simp only [hs, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · intro hx; rcases hdich x with h0 | h1
        · exact h0
        · exact absurd h1 hx
      · intro hx; rw [hx]; norm_num
    rw [this]
    exact IsClosed.preimage (map_continuous f) isClosed_singleton
  have hclopen : IsClopen s := ⟨hclosed, isClosed_compl_iff.mp hcompl_closed⟩
  -- In the connected space `ℝ`, `s` is `∅` or `univ`.
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · -- `s = ∅`: `f` is identically `0`, so `e = 0`.
    left
    have hzero : ∀ x, f x = 0 := by
      intro x
      rcases hdich x with h0 | h1
      · exact h0
      · have hmem : x ∈ s := h1
        rw [hempty] at hmem
        simp at hmem
    have : f = 0 := by ext x; simp [hzero x]
    have : (e : C(ℝ, ℝ)) = ((0 : periodicSubalg) : C(ℝ, ℝ)) := by simpa [hf] using this
    exact Subtype.ext this
  · -- `s = univ`: `f` is identically `1`, so `e = 1`.
    right
    have hone : ∀ x, f x = 1 := by
      intro x
      have : x ∈ s := by rw [huniv]; exact Set.mem_univ x
      exact this
    have : f = 1 := by ext x; simp [hone x]
    have : (e : C(ℝ, ℝ)) = ((1 : periodicSubalg) : C(ℝ, ℝ)) := by simpa [hf] using this
    exact Subtype.ext this

/-- **Problem 3.8.5(i).** `A` is indecomposable as an `A`-module: the function algebra of the
circle has no nontrivial idempotents. -/
theorem periodic_isIndecomposable :
    Etingof.IsIndecomposable (periodicSubalg) (periodicSubalg) := by
  refine ⟨inferInstance, ?_⟩
  intro W₁ W₂ hC
  -- `1 = e₁ + e₂` with `e₁ ∈ W₁`, `e₂ ∈ W₂`, from codisjointness.
  have h1 : (1 : periodicSubalg) ∈ W₁ ⊔ W₂ := by rw [hC.sup_eq_top]; trivial
  rw [Submodule.mem_sup] at h1
  obtain ⟨e₁, he₁, e₂, he₂, hsum⟩ := h1
  -- `e₁ * e₂ ∈ W₁ ⊓ W₂ = ⊥`, so `e₁ * e₂ = 0`.
  have hmem12 : e₁ * e₂ ∈ W₁ ⊓ W₂ := by
    refine ⟨?_, ?_⟩
    · rw [mul_comm]
      have := W₁.smul_mem e₂ he₁
      rwa [smul_eq_mul] at this
    · have := W₂.smul_mem e₁ he₂
      rwa [smul_eq_mul] at this
  rw [hC.inf_eq_bot, Submodule.mem_bot] at hmem12
  -- Hence `e₁` is idempotent.
  have hidem : e₁ * e₁ = e₁ := by
    have h : e₁ * (e₁ + e₂) = e₁ * 1 := by rw [hsum]
    rw [mul_add, hmem12, add_zero, mul_one] at h
    exact h
  rcases periodicSubalg_idempotent_eq_zero_or_one e₁ hidem with rfl | rfl
  · -- `e₁ = 0` ⇒ `e₂ = 1` ⇒ `W₂ = ⊤` ⇒ `W₁ = ⊥`.
    left
    have he2 : e₂ = 1 := by rw [zero_add] at hsum; exact hsum
    rw [he2] at he₂
    have hW2 : W₂ = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have := W₂.smul_mem a he₂
      rwa [smul_eq_mul, mul_one] at this
    have := hC.inf_eq_bot
    rwa [hW2, inf_top_eq] at this
  · -- `e₁ = 1` ⇒ `W₁ = ⊤` ⇒ `W₂ = ⊥`.
    right
    have hW1 : W₁ = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have := W₁.smul_mem a he₁
      rwa [smul_eq_mul, mul_one] at this
    have := hC.inf_eq_bot
    rwa [hW1, top_inf_eq] at this

open Real in
/-- The antiperiodic function `x ↦ cos (π x)`. -/
noncomputable def cosπ : C(ℝ, ℝ) := ⟨fun x => Real.cos (π * x), by fun_prop⟩

open Real in
/-- The antiperiodic function `x ↦ sin (π x)`. -/
noncomputable def sinπ : C(ℝ, ℝ) := ⟨fun x => Real.sin (π * x), by fun_prop⟩

@[simp] lemma cosπ_apply (x : ℝ) : cosπ x = Real.cos (Real.pi * x) := rfl
@[simp] lemma sinπ_apply (x : ℝ) : sinπ x = Real.sin (Real.pi * x) := rfl

lemma cosπ_mem : cosπ ∈ antiperiodicSubmod := by
  intro x
  simp only [cosπ_apply, mul_add, mul_one]
  exact Real.cos_add_pi _

lemma sinπ_mem : sinπ ∈ antiperiodicSubmod := by
  intro x
  simp only [sinπ_apply, mul_add, mul_one]
  exact Real.sin_add_pi _

/-- `cos(πx)² + sin(πx)² = 1`, the frame identity for the module `M`. -/
lemma cosπ_sq_add_sinπ_sq (x : ℝ) : cosπ x * cosπ x + sinπ x * sinπ x = 1 := by
  simp only [cosπ_apply, sinπ_apply]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]

/-- `cos(πx)`, `sin(πx)` as elements of the antiperiodic module `M`. -/
noncomputable def cM : antiperiodicSubmod := ⟨cosπ, cosπ_mem⟩
noncomputable def sM : antiperiodicSubmod := ⟨sinπ, sinπ_mem⟩

@[simp] lemma cM_coe : (cM : C(ℝ, ℝ)) = cosπ := rfl
@[simp] lemma sM_coe : (sM : C(ℝ, ℝ)) = sinπ := rfl

/-- The product of two antiperiodic functions is periodic, packaged as an element of `A`. -/
noncomputable def antiMul (f g : antiperiodicSubmod) : periodicSubalg :=
  ⟨(f : C(ℝ, ℝ)) * (g : C(ℝ, ℝ)), by
    intro x
    simp only [ContinuousMap.mul_apply, f.2 x, g.2 x]
    ring⟩

@[simp] lemma antiMul_coe_apply (f g : antiperiodicSubmod) (x : ℝ) :
    ((antiMul f g : periodicSubalg) : C(ℝ, ℝ)) x = (f : C(ℝ, ℝ)) x * (g : C(ℝ, ℝ)) x := rfl

/-- The scalar action of `A` on `C(ℝ, ℝ)` is pointwise multiplication, at the level of values. -/
lemma smul_apply_coe (a : periodicSubalg) (m : antiperiodicSubmod) (x : ℝ) :
    ((a • m : antiperiodicSubmod) : C(ℝ, ℝ)) x = (a : C(ℝ, ℝ)) x * (m : C(ℝ, ℝ)) x := by
  rw [Submodule.coe_smul, Algebra.smul_def]; rfl

/-- **Frame decomposition.** Every antiperiodic `f` is `(cf)·c + (sf)·s`, where `c = cos π·`,
`s = sin π·`, and `cf, sf ∈ A` are the (periodic) products `c·f`, `s·f`. This exhibits `M` as
generated over `A` by the two sections `c`, `s` with `c² + s² = 1`. -/
lemma antiperiodic_frame_decomp (f : antiperiodicSubmod) :
    f = antiMul cM f • cM + antiMul sM f • sM := by
  apply Subtype.ext
  ext x
  simp only [Submodule.coe_add, ContinuousMap.add_apply, smul_apply_coe, antiMul_coe_apply,
    cM_coe, sM_coe]
  have h := cosπ_sq_add_sinπ_sq x
  linear_combination (-((f : C(ℝ, ℝ)) x)) * h

/-- **Problem 3.8.5(i).** `M` is indecomposable as an `A`-module. -/
theorem antiperiodic_isIndecomposable :
    Etingof.IsIndecomposable (periodicSubalg) (antiperiodicSubmod) := by
  refine ⟨⟨⟨0, cM, ?_⟩⟩, ?_⟩
  · -- Nontriviality: `0 ≠ cos π·`, since `cos 0 = 1`.
    intro h
    have := congrArg (fun z : antiperiodicSubmod => (z : C(ℝ, ℝ)) 0) h
    simp [cM_coe, cosπ_apply] at this
  · intro W₁ W₂ hC
    -- The `A`-linear projection onto `W₁` along `W₂`.
    set π := @Submodule.projection (periodicSubalg) _ (antiperiodicSubmod) _ _ W₁ W₂ hC with hπ
    have hleft : ∀ w, w ∈ W₁ → π w = w := by
      intro w hw
      simpa [hπ] using
        (@Submodule.projection_apply_of_mem_left (periodicSubalg) _ (antiperiodicSubmod) _ _
          W₁ W₂ hC w hw)
    have hright : ∀ w, w ∈ W₂ → π w = 0 := by
      intro w hw
      simpa [hπ] using
        (@Submodule.projection_apply_of_mem_right (periodicSubalg) _ (antiperiodicSubmod) _ _
          W₁ W₂ hC w hw)
    have hmem : ∀ g, π g ∈ W₁ := by
      intro g
      have hg : g ∈ W₁ ⊔ W₂ := by rw [hC.sup_eq_top]; trivial
      rw [Submodule.mem_sup] at hg
      obtain ⟨a, ha, b, hb, hab⟩ := hg
      rw [← hab, map_add, hleft a ha, hright b hb, add_zero]
      exact ha
    have hidemπ : ∀ f, π (π f) = π f := fun f => hleft (π f) (hmem f)
    -- The idempotent `e ∈ A` with `π = (e • ·)`.
    set e : periodicSubalg := antiMul cM (π cM) + antiMul sM (π sM) with he_def
    have key : ∀ f, π f = e • f := by
      intro f
      have hpieq : π f = antiMul cM f • π cM + antiMul sM f • π sM := by
        conv_lhs => rw [antiperiodic_frame_decomp f]
        rw [map_add, map_smul, map_smul]
      rw [hpieq]
      apply Subtype.ext
      ext x
      rw [he_def]
      simp only [Submodule.coe_add, Subalgebra.coe_add, ContinuousMap.add_apply, smul_apply_coe,
        antiMul_coe_apply, cM_coe, sM_coe]
      ring
    -- `e` is idempotent: `(e*e)•f = e•f` for all `f`, tested against `c` and `s`.
    have hidem_smul : ∀ f : ↥antiperiodicSubmod, (e * e) • f = e • f := by
      intro f
      have h1 : π (π f) = π f := hidemπ f
      rw [key f] at h1
      rw [key (e • f)] at h1
      rw [smul_smul] at h1
      exact h1
    have hee : e * e = e := by
      apply Subtype.ext
      ext x
      have hcx := congrArg (fun z : antiperiodicSubmod => (z : C(ℝ, ℝ)) x) (hidem_smul cM)
      have hsx := congrArg (fun z : antiperiodicSubmod => (z : C(ℝ, ℝ)) x) (hidem_smul sM)
      simp only [smul_apply_coe, cM_coe, sM_coe] at hcx hsx
      have htrig := cosπ_sq_add_sinπ_sq x
      linear_combination cosπ x * hcx + sinπ x * hsx +
        ((e : C(ℝ, ℝ)) x - ((e * e : periodicSubalg) : C(ℝ, ℝ)) x) * htrig
    -- An idempotent in `A` is `0` or `1`, forcing one summand to vanish.
    rcases periodicSubalg_idempotent_eq_zero_or_one e hee with he0 | he1
    · left
      rw [Submodule.eq_bot_iff]
      intro w hw
      have h := hleft w hw
      rw [key w, he0, zero_smul] at h
      exact h.symm
    · right
      rw [Submodule.eq_bot_iff]
      intro w hw
      have h := hright w hw
      rw [key w, he1, one_smul] at h
      exact h

/-- **Problem 3.8.5(ii), first part.** `A` is not isomorphic to `M` as `A`-modules: `M` is a
nontrivial line bundle on the circle (the Möbius bundle), so it is not free of rank 1.

If `φ : A ≃ₗ M`, then `u := φ 1` generates `M`: every `m` is `(φ.symm m) • u`. But `u` is a
continuous antiperiodic function, so `u 0` and `u 1 = -u 0` have opposite signs and `u` vanishes
somewhere in `[0, 1]` by the intermediate value theorem. Then every element of `M` vanishes at
that point, contradicting the antiperiodic section `x ↦ cos(π (x - x₀))`, which is nonzero there. -/
theorem periodic_not_linearEquiv_antiperiodic :
    IsEmpty (periodicSubalg ≃ₗ[periodicSubalg] antiperiodicSubmod) := by
  refine ⟨fun φ => ?_⟩
  -- `u := φ 1`, a global section that generates `M`.
  set u : antiperiodicSubmod := φ 1 with hu
  set U : C(ℝ, ℝ) := (u : C(ℝ, ℝ)) with hU_def
  have hUanti : ∀ x, U (x + 1) = - U x := u.2
  -- Every element of `M` is a periodic multiple of `u`.
  have hgen : ∀ m : antiperiodicSubmod,
      (m : C(ℝ, ℝ)) = ((φ.symm m • u : antiperiodicSubmod) : C(ℝ, ℝ)) := by
    intro m
    have : (φ.symm m • u : antiperiodicSubmod) = m := by
      rw [hu, ← φ.map_smul, smul_eq_mul, mul_one, φ.apply_symm_apply]
    rw [this]
  -- `U` vanishes somewhere in `[0, 1]` by the intermediate value theorem.
  have hroot : ∃ x₀ ∈ Set.Icc (0 : ℝ) 1, U x₀ = 0 := by
    have hcont : ContinuousOn U (Set.Icc 0 1) := U.continuous.continuousOn
    have hU1 : U 1 = - U 0 := by have := hUanti 0; simpa using this
    rcases le_or_gt 0 (U 0) with h0 | h0
    · have hmem : (0 : ℝ) ∈ Set.Icc (U 1) (U 0) := ⟨by rw [hU1]; linarith, h0⟩
      obtain ⟨x₀, hx₀, hval⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
      exact ⟨x₀, hx₀, hval⟩
    · have hmem : (0 : ℝ) ∈ Set.Icc (U 0) (U 1) := ⟨by linarith, by rw [hU1]; linarith⟩
      obtain ⟨x₀, hx₀, hval⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
      exact ⟨x₀, hx₀, hval⟩
  obtain ⟨x₀, _, hx₀0⟩ := hroot
  -- The antiperiodic section `w x = cos(π (x - x₀))` is nonzero at `x₀`.
  set w : C(ℝ, ℝ) := ⟨fun x => Real.cos (Real.pi * (x - x₀)), by fun_prop⟩ with hw_def
  have hw_mem : w ∈ antiperiodicSubmod := by
    intro x
    change Real.cos (Real.pi * (x + 1 - x₀)) = - Real.cos (Real.pi * (x - x₀))
    rw [show Real.pi * (x + 1 - x₀) = Real.pi * (x - x₀) + Real.pi by ring, Real.cos_add_pi]
  set wM : antiperiodicSubmod := ⟨w, hw_mem⟩ with hwM
  have hwval : (wM : C(ℝ, ℝ)) x₀ = 1 := by
    change Real.cos (Real.pi * (x₀ - x₀)) = 1
    simp
  have hzero : (wM : C(ℝ, ℝ)) x₀ = 0 := by
    rw [hgen wM, smul_apply_coe, ← hU_def, hx₀0, mul_zero]
  rw [hwval] at hzero
  exact one_ne_zero hzero

/-- Multiplication by a fixed antiperiodic function `h`, as an `A`-linear map `M →ₗ[A] A`
(the product of two antiperiodics is periodic). -/
noncomputable def antiMulL (h : antiperiodicSubmod) :
    antiperiodicSubmod →ₗ[periodicSubalg] periodicSubalg where
  toFun f := antiMul h f
  map_add' f g := by
    apply Subtype.ext; ext t
    simp only [Subalgebra.coe_add, ContinuousMap.add_apply, antiMul_coe_apply, Submodule.coe_add]
    ring
  map_smul' a f := by
    apply Subtype.ext; ext t
    simp only [RingHom.id_apply, antiMul_coe_apply, smul_apply_coe, smul_eq_mul,
      Subalgebra.coe_mul, ContinuousMap.mul_apply]
    ring

/-- The rotation map `M × M →ₗ[A] A × A`, `(f, g) ↦ (cos·f − sin·g, sin·f + cos·g)`. Each output
component is a sum of products of antiperiodic functions, hence periodic. -/
noncomputable def rotInv :
    (antiperiodicSubmod × antiperiodicSubmod) →ₗ[periodicSubalg]
      (periodicSubalg × periodicSubalg) where
  toFun fg := (antiMul cM fg.1 - antiMul sM fg.2, antiMul sM fg.1 + antiMul cM fg.2)
  map_add' x y := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · apply Subtype.ext; ext t
      simp only [Prod.fst_add, Prod.snd_add, Subalgebra.coe_add, Subalgebra.coe_sub,
        ContinuousMap.add_apply, ContinuousMap.sub_apply, antiMul_coe_apply, Submodule.coe_add]
      ring
    · apply Subtype.ext; ext t
      simp only [Prod.fst_add, Prod.snd_add, Subalgebra.coe_add, ContinuousMap.add_apply,
        antiMul_coe_apply, Submodule.coe_add]
      ring
  map_smul' a x := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · apply Subtype.ext; ext t
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Subalgebra.coe_sub,
        ContinuousMap.sub_apply, antiMul_coe_apply, smul_apply_coe, smul_eq_mul,
        Subalgebra.coe_mul, ContinuousMap.mul_apply]
      ring
    · apply Subtype.ext; ext t
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Subalgebra.coe_add,
        ContinuousMap.add_apply, antiMul_coe_apply, smul_apply_coe, smul_eq_mul,
        Subalgebra.coe_mul, ContinuousMap.mul_apply]
      ring

/-- The inverse rotation `A × A →ₗ[A] M × M`, `(p, q) ↦ (cos·p + sin·q, −sin·p + cos·q)`. Each
output component is periodic times antiperiodic, hence antiperiodic. -/
noncomputable def rotFwd :
    (periodicSubalg × periodicSubalg) →ₗ[periodicSubalg]
      (antiperiodicSubmod × antiperiodicSubmod) where
  toFun pq := (pq.1 • cM + pq.2 • sM, -(pq.1 • sM) + pq.2 • cM)
  map_add' x y := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · apply Subtype.ext; ext t
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, ContinuousMap.add_apply,
        smul_apply_coe, Subalgebra.coe_add, cM_coe, sM_coe]
      ring
    · apply Subtype.ext; ext t
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Submodule.coe_neg,
        ContinuousMap.add_apply, ContinuousMap.neg_apply, smul_apply_coe, Subalgebra.coe_add,
        cM_coe, sM_coe]
      ring
  map_smul' a x := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · apply Subtype.ext; ext t
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Submodule.coe_add,
        ContinuousMap.add_apply, smul_apply_coe, smul_eq_mul, Subalgebra.coe_mul,
        ContinuousMap.mul_apply, cM_coe, sM_coe]
      ring
    · apply Subtype.ext; ext t
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Submodule.coe_add,
        Submodule.coe_neg, ContinuousMap.add_apply, ContinuousMap.neg_apply, smul_apply_coe,
        smul_eq_mul, Subalgebra.coe_mul, ContinuousMap.mul_apply, cM_coe, sM_coe]
      ring

@[simp] lemma rotInv_apply (fg : antiperiodicSubmod × antiperiodicSubmod) :
    rotInv fg = (antiMul cM fg.1 - antiMul sM fg.2, antiMul sM fg.1 + antiMul cM fg.2) := rfl

@[simp] lemma rotFwd_apply (pq : periodicSubalg × periodicSubalg) :
    rotFwd pq = (pq.1 • cM + pq.2 • sM, -(pq.1 • sM) + pq.2 • cM) := rfl

/-- `rotInv ∘ rotFwd = id` on `A × A`: `cos² + sin² = 1`. -/
lemma rotInv_rotFwd (pq : periodicSubalg × periodicSubalg) : rotInv (rotFwd pq) = pq := by
  obtain ⟨p, q⟩ := pq
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · apply Subtype.ext; ext t
    simp only [rotFwd_apply, rotInv_apply, Subalgebra.coe_sub, ContinuousMap.sub_apply,
      antiMul_coe_apply, Submodule.coe_add, Submodule.coe_neg, ContinuousMap.add_apply,
      ContinuousMap.neg_apply, smul_apply_coe, cM_coe, sM_coe, cosπ_apply, sinπ_apply]
    linear_combination ((p : C(ℝ, ℝ)) t) * Real.sin_sq_add_cos_sq (Real.pi * t)
  · apply Subtype.ext; ext t
    simp only [rotFwd_apply, rotInv_apply, Subalgebra.coe_add, ContinuousMap.add_apply,
      antiMul_coe_apply, Submodule.coe_add, Submodule.coe_neg, ContinuousMap.add_apply,
      ContinuousMap.neg_apply, smul_apply_coe, cM_coe, sM_coe, cosπ_apply, sinπ_apply]
    linear_combination ((q : C(ℝ, ℝ)) t) * Real.sin_sq_add_cos_sq (Real.pi * t)

/-- `rotFwd ∘ rotInv = id` on `M × M`: `cos² + sin² = 1`. -/
lemma rotFwd_rotInv (fg : antiperiodicSubmod × antiperiodicSubmod) : rotFwd (rotInv fg) = fg := by
  obtain ⟨f, g⟩ := fg
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · apply Subtype.ext; ext t
    simp only [rotFwd_apply, rotInv_apply, Subalgebra.coe_sub, Subalgebra.coe_add,
      ContinuousMap.sub_apply, ContinuousMap.add_apply, antiMul_coe_apply, Submodule.coe_add,
      ContinuousMap.add_apply, smul_apply_coe, cM_coe, sM_coe, cosπ_apply, sinπ_apply]
    linear_combination ((f : C(ℝ, ℝ)) t) * Real.sin_sq_add_cos_sq (Real.pi * t)
  · apply Subtype.ext; ext t
    simp only [rotFwd_apply, rotInv_apply, Subalgebra.coe_sub, Subalgebra.coe_add,
      ContinuousMap.sub_apply, ContinuousMap.add_apply, antiMul_coe_apply, Submodule.coe_add,
      Submodule.coe_neg, ContinuousMap.neg_apply, smul_apply_coe, cM_coe, sM_coe,
      cosπ_apply, sinπ_apply]
    linear_combination ((g : C(ℝ, ℝ)) t) * Real.sin_sq_add_cos_sq (Real.pi * t)

/-- **Problem 3.8.5(ii), second part.** `A ⊕ A ≅ M ⊕ M` as `A`-modules, via the rotation
`(f, g) ↦ (cos·f − sin·g, sin·f + cos·g)` and its transpose inverse. -/
theorem periodic_sq_linearEquiv_antiperiodic_sq :
    Nonempty ((periodicSubalg × periodicSubalg) ≃ₗ[periodicSubalg]
      (antiperiodicSubmod × antiperiodicSubmod)) :=
  ⟨(LinearEquiv.ofLinear rotInv rotFwd
      (by apply LinearMap.ext; intro pq
          simp only [LinearMap.comp_apply, LinearMap.id_apply]; exact rotInv_rotFwd pq)
      (by apply LinearMap.ext; intro fg
          simp only [LinearMap.comp_apply, LinearMap.id_apply]; exact rotFwd_rotInv fg)).symm⟩

end Etingof.Problem3_8_5

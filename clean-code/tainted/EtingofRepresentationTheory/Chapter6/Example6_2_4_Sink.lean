import Mathlib
import EtingofRepresentationTheory.Chapter6.Example6_2_2
import EtingofRepresentationTheory.Chapter6.Example6_2_4

/-!
# Example 6.2.4, second orientation: the pair of subspaces problem

The quiver A₃ admits two orientations. The first, `• → • → •`, is treated in
`Example6_2_4.lean`. This file treats the second,

  `• → • ← •`,

whose representations consist of three vector spaces `V₁, V₂, V₃` together with linear
maps `f : V₁ → V₂` and `g : V₃ → V₂`. After splitting off the kernels of `f` and `g` one
may regard `V₁` and `V₃` as subspaces of `V₂`, so classifying these representations is the
pair of subspaces problem.

The six indecomposable representations, written as dimension vectors `(dim V₁, dim V₂, dim V₃)`,
are

  `(1,0,0)`, `(0,0,1)`, `(0,1,0)`, `(1,1,0)`, `(0,1,1)`, `(1,1,1)`,

with `f` an isomorphism whenever `dim V₁ = dim V₂ = 1` and `g` an isomorphism whenever
`dim V₃ = dim V₂ = 1`.

The dimension vectors are pairwise distinct, so they already separate the six classes. The
file proves the necessary condition on dimension vectors, constructs the six representatives,
proves each is indecomposable, and proves that every indecomposable representation is
isomorphic to exactly one of them.
-/

/-- A representation of the A₃ quiver in the orientation `• → • ← •` over a field `k`. -/
structure A₃SinkRep (k : Type*) [Field k] where
  V₁ : Type*
  V₂ : Type*
  V₃ : Type*
  [addCommGroup₁ : AddCommGroup V₁]
  [module₁ : Module k V₁]
  [finiteDimensional₁ : FiniteDimensional k V₁]
  [addCommGroup₂ : AddCommGroup V₂]
  [module₂ : Module k V₂]
  [finiteDimensional₂ : FiniteDimensional k V₂]
  [addCommGroup₃ : AddCommGroup V₃]
  [module₃ : Module k V₃]
  [finiteDimensional₃ : FiniteDimensional k V₃]
  f : V₁ →ₗ[k] V₂
  g : V₃ →ₗ[k] V₂

attribute [instance] A₃SinkRep.addCommGroup₁ A₃SinkRep.module₁ A₃SinkRep.finiteDimensional₁
  A₃SinkRep.addCommGroup₂ A₃SinkRep.module₂ A₃SinkRep.finiteDimensional₂
  A₃SinkRep.addCommGroup₃ A₃SinkRep.module₃ A₃SinkRep.finiteDimensional₃

/-- A representation of `• → • ← •` is indecomposable if it is nontrivial and every
decomposition of the three vertex spaces compatible with `f` and `g` has a zero summand. -/
def A₃SinkRep.Indecomposable {k : Type*} [Field k] (ρ : A₃SinkRep k) : Prop :=
  (0 < Module.finrank k ρ.V₁ ∨ 0 < Module.finrank k ρ.V₂ ∨
   0 < Module.finrank k ρ.V₃) ∧
  ∀ (p₁ q₁ : Submodule k ρ.V₁) (p₂ q₂ : Submodule k ρ.V₂)
    (p₃ q₃ : Submodule k ρ.V₃),
    IsCompl p₁ q₁ → IsCompl p₂ q₂ → IsCompl p₃ q₃ →
    (∀ x ∈ p₁, ρ.f x ∈ p₂) → (∀ x ∈ q₁, ρ.f x ∈ q₂) →
    (∀ z ∈ p₃, ρ.g z ∈ p₂) → (∀ z ∈ q₃, ρ.g z ∈ q₂) →
    (p₁ = ⊥ ∧ p₂ = ⊥ ∧ p₃ = ⊥) ∨ (q₁ = ⊥ ∧ q₂ = ⊥ ∧ q₃ = ⊥)

/-- A bijective linear map preserves `IsCompl` under `comap`. -/
lemma isCompl_comap_of_bijective {k : Type*} [Field k]
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (h : V →ₗ[k] W) (hh : Function.Bijective h)
    (p q : Submodule k W) (hpq : IsCompl p q) :
    IsCompl (Submodule.comap h p) (Submodule.comap h q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxp hxq
    have hmem : h x ∈ p ⊓ q := ⟨hxp, hxq⟩
    rw [hpq.1.eq_bot, Submodule.mem_bot] at hmem
    exact hh.1 (by rw [hmem, map_zero])
  · rw [codisjoint_iff]
    ext x
    simp only [Submodule.mem_sup, Submodule.mem_top, iff_true]
    have hx : h x ∈ (⊤ : Submodule k W) := Submodule.mem_top
    rw [← hpq.2.eq_top] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a', rfl⟩ := hh.2 a
    obtain ⟨b', rfl⟩ := hh.2 b
    refine ⟨a', ha, b', hb, hh.1 ?_⟩
    rw [map_add, hab]

namespace A₃SinkRep

variable {k : Type*} [Field k]

private lemma top_eq_bot_of_finrank_zero {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (h : Module.finrank k V = 0) : (⊤ : Submodule k V) = ⊥ :=
  Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h)

private lemma finrank_zero_of_top_eq_bot {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (h : (⊤ : Submodule k V) = ⊥) : Module.finrank k V = 0 := by
  rw [← finrank_top (R := k) (M := V), h, finrank_bot]

/-- Either `f` is injective, or the representation is concentrated at the first vertex. -/
private lemma ker_f_or (ρ : A₃SinkRep k) (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.f = ⊥ ∨
      (Module.finrank k ρ.V₂ = 0 ∧ Module.finrank k ρ.V₃ = 0) := by
  by_contra h
  push Not at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.f)
  have hres := hind.2 (LinearMap.ker ρ.f) q₁ ⊥ ⊤ ⊥ ⊤ hq₁ isCompl_bot_top isCompl_bot_top
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun z hz => by rw [(Submodule.mem_bot (R := k)).mp hz, map_zero]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
  rcases hres with ⟨hk, _, _⟩ | ⟨_, h2, h3⟩
  · exact hker hk
  · exact hrest (finrank_zero_of_top_eq_bot h2) (finrank_zero_of_top_eq_bot h3)

/-- Either `g` is injective, or the representation is concentrated at the third vertex. -/
private lemma ker_g_or (ρ : A₃SinkRep k) (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.g = ⊥ ∨
      (Module.finrank k ρ.V₂ = 0 ∧ Module.finrank k ρ.V₁ = 0) := by
  by_contra h
  push Not at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₃, hq₃⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.g)
  have hres := hind.2 ⊥ ⊤ ⊥ ⊤ (LinearMap.ker ρ.g) q₃ isCompl_bot_top isCompl_bot_top hq₃
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
    (fun _ _ => Submodule.mem_top)
    (fun z hz => by simp [LinearMap.mem_ker.mp hz])
    (fun _ _ => Submodule.mem_top)
  rcases hres with ⟨_, _, hk⟩ | ⟨h1, h2, _⟩
  · exact hker hk
  · exact hrest (finrank_zero_of_top_eq_bot h2) (finrank_zero_of_top_eq_bot h1)

/-- Either the images of `f` and `g` span the middle space, or the representation is
concentrated at the middle vertex. -/
private lemma range_sup_or (ρ : A₃SinkRep k) (hind : ρ.Indecomposable) :
    LinearMap.range ρ.f ⊔ LinearMap.range ρ.g = ⊤ ∨
      (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₃ = 0) := by
  by_contra h
  push Not at h
  obtain ⟨hsup, hrest⟩ := h
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl (LinearMap.range ρ.f ⊔ LinearMap.range ρ.g)
  have hres := hind.2 ⊤ ⊥ (LinearMap.range ρ.f ⊔ LinearMap.range ρ.g) T ⊤ ⊥
    isCompl_top_bot hT isCompl_top_bot
    (fun x _ => Submodule.mem_sup_left (LinearMap.mem_range_self ρ.f x))
    (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
    (fun z _ => Submodule.mem_sup_right (LinearMap.mem_range_self ρ.g z))
    (fun z hz => by rw [(Submodule.mem_bot (R := k)).mp hz, map_zero]; exact Submodule.zero_mem _)
  rcases hres with ⟨h1, _, h3⟩ | ⟨_, hTbot, _⟩
  · exact hrest (finrank_zero_of_top_eq_bot h1) (finrank_zero_of_top_eq_bot h3)
  · exact hsup (eq_top_of_isCompl_bot (hTbot ▸ hT))

/-- If the middle space is zero the representation is a single one-dimensional space at an
outer vertex. -/
private lemma V₂_zero_cases (ρ : A₃SinkRep k) (hind : ρ.Indecomposable)
    (h₂ : Module.finrank k ρ.V₂ = 0) :
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₃ = 0) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₃ = 1) := by
  obtain ⟨hnt, hind_cond⟩ := hind
  have hV₂zero : ∀ y : ρ.V₂, y = 0 := a3_zero_of_finrank_zero ρ.V₂ h₂
  -- One of the outer vertices is zero.
  have houter : Module.finrank k ρ.V₁ = 0 ∨ Module.finrank k ρ.V₃ = 0 := by
    have hres := hind_cond ⊤ ⊥ ⊥ ⊤ ⊥ ⊤ isCompl_top_bot isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV₂zero (ρ.f x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun z _ => by rw [hV₂zero (ρ.g z)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hres with ⟨h1, _, _⟩ | ⟨_, _, h3⟩
    · exact Or.inl (finrank_zero_of_top_eq_bot h1)
    · exact Or.inr (finrank_zero_of_top_eq_bot h3)
  rcases houter with h₁ | h₃
  · -- `V₁ = 0`, so `V₃` carries the whole representation.
    have hV₁zero : ∀ x : ρ.V₁, x = 0 := a3_zero_of_finrank_zero ρ.V₁ h₁
    have h₃pos : 0 < Module.finrank k ρ.V₃ := by omega
    refine Or.inr ⟨h₁, ?_⟩
    rw [← Etingof.Example_6_2_2]
    refine ⟨Module.nontrivial_of_finrank_pos h₃pos, fun p₃ q₃ hpq₃ => ?_⟩
    have hres := hind_cond ⊥ ⊤ ⊥ ⊤ p₃ q₃ isCompl_bot_top isCompl_bot_top hpq₃
      (fun x _ => by rw [hV₂zero (ρ.f x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun z _ => by rw [hV₂zero (ρ.g z)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hres with ⟨_, _, hp⟩ | ⟨_, _, hq⟩
    · exact Or.inl hp
    · exact Or.inr hq
  · -- `V₃ = 0`, so `V₁` carries the whole representation.
    have hV₃zero : ∀ z : ρ.V₃, z = 0 := a3_zero_of_finrank_zero ρ.V₃ h₃
    have h₁pos : 0 < Module.finrank k ρ.V₁ := by omega
    refine Or.inl ⟨?_, h₃⟩
    rw [← Etingof.Example_6_2_2]
    refine ⟨Module.nontrivial_of_finrank_pos h₁pos, fun p₁ q₁ hpq₁ => ?_⟩
    have hres := hind_cond p₁ q₁ ⊥ ⊤ ⊥ ⊤ hpq₁ isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV₂zero (ρ.f x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun z _ => by rw [hV₂zero (ρ.g z)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hres with ⟨hp, _, _⟩ | ⟨hq, _, _⟩
    · exact Or.inl hp
    · exact Or.inr hq

/-- The middle space is one-dimensional when both outer spaces vanish. -/
private lemma V₂_dim_one_of_outer_zero (ρ : A₃SinkRep k) (hind : ρ.Indecomposable)
    (h₁ : Module.finrank k ρ.V₁ = 0) (h₃ : Module.finrank k ρ.V₃ = 0)
    (h₂ : 0 < Module.finrank k ρ.V₂) : Module.finrank k ρ.V₂ = 1 := by
  obtain ⟨_, hind_cond⟩ := hind
  have hV₁zero : ∀ x : ρ.V₁, x = 0 := a3_zero_of_finrank_zero ρ.V₁ h₁
  have hV₃zero : ∀ z : ρ.V₃, z = 0 := a3_zero_of_finrank_zero ρ.V₃ h₃
  rw [← Etingof.Example_6_2_2]
  refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
  have hres := hind_cond ⊥ ⊤ p₂ q₂ ⊥ ⊤ isCompl_bot_top hpq₂ isCompl_bot_top
    (fun x _ => by rw [hV₁zero x, map_zero]; exact Submodule.zero_mem _)
    (fun x _ => by rw [hV₁zero x, map_zero]; exact Submodule.zero_mem _)
    (fun z _ => by rw [hV₃zero z, map_zero]; exact Submodule.zero_mem _)
    (fun z _ => by rw [hV₃zero z, map_zero]; exact Submodule.zero_mem _)
  rcases hres with ⟨_, hp, _⟩ | ⟨_, hq, _⟩
  · exact Or.inl hp
  · exact Or.inr hq

/-- **Example 6.2.4(2) (Etingof), dimension vectors.** Every indecomposable representation of
the quiver `• → • ← •` has dimension vector one of
`(1,0,0)`, `(0,1,0)`, `(0,0,1)`, `(1,1,0)`, `(0,1,1)`, `(1,1,1)`,
with the indicated maps isomorphisms. -/
theorem _root_.Etingof.Example_6_2_4_sink (k : Type*) [Field k] (ρ : A₃SinkRep k)
    (hind : ρ.Indecomposable) :
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 0 ∧
      Module.finrank k ρ.V₃ = 0) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Module.finrank k ρ.V₃ = 0) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 0 ∧
      Module.finrank k ρ.V₃ = 1) ∨
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Module.finrank k ρ.V₃ = 0 ∧ Function.Bijective ρ.f) ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Module.finrank k ρ.V₃ = 1 ∧ Function.Bijective ρ.g) ∨
    (Module.finrank k ρ.V₁ = 1 ∧ Module.finrank k ρ.V₂ = 1 ∧
      Module.finrank k ρ.V₃ = 1 ∧ Function.Bijective ρ.f ∧
      Function.Bijective ρ.g) := by
  have hkerf := ker_f_or ρ hind
  have hkerg := ker_g_or ρ hind
  have hsup := range_sup_or ρ hind
  obtain ⟨hnt, hind_cond⟩ := hind
  have hind' : ρ.Indecomposable := ⟨hnt, hind_cond⟩
  rcases Nat.eq_zero_or_pos (Module.finrank k ρ.V₂) with h₂ | h₂
  · -- The middle space vanishes.
    rcases V₂_zero_cases ρ hind' h₂ with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · exact Or.inl ⟨h1, h₂, h3⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h₂, h3⟩))
  · -- The middle space is nonzero, so both maps are injective.
    have hf_inj : Function.Injective ρ.f :=
      LinearMap.ker_eq_bot.mp (hkerf.resolve_right (fun h => absurd h.1 h₂.ne'))
    have hg_inj : Function.Injective ρ.g :=
      LinearMap.ker_eq_bot.mp (hkerg.resolve_right (fun h => absurd h.1 h₂.ne'))
    rcases hsup with hsup | ⟨h₁, h₃⟩
    swap
    · -- Both outer spaces vanish: the middle vertex simple.
      exact Or.inr (Or.inl ⟨h₁, V₂_dim_one_of_outer_zero ρ hind' h₁ h₃ h₂, h₃⟩)
    -- The images of `f` and `g` span `V₂`.
    by_cases hD : LinearMap.range ρ.f ⊓ LinearMap.range ρ.g = ⊥
    · -- The two subspaces are complementary: the representation splits off one outer vertex.
      have hUW : IsCompl (LinearMap.range ρ.f) (LinearMap.range ρ.g) :=
        ⟨disjoint_iff.mpr hD, codisjoint_iff.mpr hsup⟩
      have hres := hind_cond ⊤ ⊥ (LinearMap.range ρ.f) (LinearMap.range ρ.g) ⊥ ⊤
        isCompl_top_bot hUW isCompl_bot_top
        (fun x _ => LinearMap.mem_range_self ρ.f x)
        (fun x hx => by
          rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
        (fun z hz => by
          rw [(Submodule.mem_bot (R := k)).mp hz, map_zero]; exact Submodule.zero_mem _)
        (fun z _ => LinearMap.mem_range_self ρ.g z)
      rcases hres with ⟨h1, hU, _⟩ | ⟨_, hW, h3⟩
      · -- `V₁ = 0` and `range f = ⊥`, so `g` is bijective.
        have h₁ : Module.finrank k ρ.V₁ = 0 := finrank_zero_of_top_eq_bot h1
        have hgtop : LinearMap.range ρ.g = ⊤ := by
          rw [← hsup, hU, bot_sup_eq]
        have hg_bij : Function.Bijective ρ.g := ⟨hg_inj, LinearMap.range_eq_top.mp hgtop⟩
        have hdim : Module.finrank k ρ.V₃ = Module.finrank k ρ.V₂ :=
          (LinearEquiv.ofBijective ρ.g hg_bij).finrank_eq
        -- `V₂` is one-dimensional, transporting decompositions along `g`.
        have hV₂dim1 : Module.finrank k ρ.V₂ = 1 := by
          rw [← Etingof.Example_6_2_2]
          refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
          have hV₁zero : ∀ x : ρ.V₁, x = 0 := a3_zero_of_finrank_zero ρ.V₁ h₁
          have hpq₃ := isCompl_comap_of_bijective ρ.g hg_bij p₂ q₂ hpq₂
          have h := hind_cond ⊥ ⊤ p₂ q₂ (Submodule.comap ρ.g p₂) (Submodule.comap ρ.g q₂)
            isCompl_bot_top hpq₂ hpq₃
            (fun x _ => by rw [hV₁zero x, map_zero]; exact Submodule.zero_mem _)
            (fun x _ => by rw [hV₁zero x, map_zero]; exact Submodule.zero_mem _)
            (fun z hz => hz) (fun z hz => hz)
          rcases h with ⟨_, hp, _⟩ | ⟨_, hq, _⟩
          · exact Or.inl hp
          · exact Or.inr hq
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, hV₂dim1, by omega, hg_bij⟩))))
      · -- `V₃ = 0` and `range g = ⊥`, so `f` is bijective.
        have h₃ : Module.finrank k ρ.V₃ = 0 := finrank_zero_of_top_eq_bot h3
        have hftop : LinearMap.range ρ.f = ⊤ := by
          rw [← hsup, hW, sup_bot_eq]
        have hf_bij : Function.Bijective ρ.f := ⟨hf_inj, LinearMap.range_eq_top.mp hftop⟩
        have hdim : Module.finrank k ρ.V₁ = Module.finrank k ρ.V₂ :=
          (LinearEquiv.ofBijective ρ.f hf_bij).finrank_eq
        have hV₂dim1 : Module.finrank k ρ.V₂ = 1 := by
          rw [← Etingof.Example_6_2_2]
          refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
          have hV₃zero : ∀ z : ρ.V₃, z = 0 := a3_zero_of_finrank_zero ρ.V₃ h₃
          have hpq₁ := isCompl_comap_of_bijective ρ.f hf_bij p₂ q₂ hpq₂
          have h := hind_cond (Submodule.comap ρ.f p₂) (Submodule.comap ρ.f q₂) p₂ q₂ ⊥ ⊤
            hpq₁ hpq₂ isCompl_bot_top
            (fun x hx => hx) (fun x hx => hx)
            (fun z _ => by rw [hV₃zero z, map_zero]; exact Submodule.zero_mem _)
            (fun z _ => by rw [hV₃zero z, map_zero]; exact Submodule.zero_mem _)
          rcases h with ⟨_, hp, _⟩ | ⟨_, hq, _⟩
          · exact Or.inl hp
          · exact Or.inr hq
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hV₂dim1, h₃, hf_bij⟩)))
    · -- The two subspaces meet: the representation is the `(1,1,1)` one.
      -- Split `V₂` as `(range f ⊓ range g) ⊕ (f Q₁ ⊔ g Q₃)`.
      obtain ⟨Q₁, hQ₁⟩ :=
        Submodule.exists_isCompl (Submodule.comap ρ.f (LinearMap.range ρ.f ⊓ LinearMap.range ρ.g))
      obtain ⟨Q₃, hQ₃⟩ :=
        Submodule.exists_isCompl (Submodule.comap ρ.g (LinearMap.range ρ.f ⊓ LinearMap.range ρ.g))
      set D := LinearMap.range ρ.f ⊓ LinearMap.range ρ.g with hDdef
      set Q₂ := Submodule.map ρ.f Q₁ ⊔ Submodule.map ρ.g Q₃ with hQ₂def
      have hDQ₂ : IsCompl D Q₂ := by
        constructor
        · rw [Submodule.disjoint_def]
          intro z hzD hzQ₂
          obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hzQ₂
          obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
          -- `f x` lies in both images, hence in `D`, forcing `x = 0`.
          have hfxW : ρ.f x ∈ LinearMap.range ρ.g := by
            have hsubs : ρ.f x = z - ρ.g y := eq_sub_of_add_eq hab
            rw [hsubs]
            exact Submodule.sub_mem _ hzD.2 (LinearMap.mem_range_self ρ.g y)
          have hxmem : x ∈ Submodule.comap ρ.f D ⊓ Q₁ :=
            ⟨⟨LinearMap.mem_range_self ρ.f x, hfxW⟩, hx⟩
          rw [hQ₁.1.eq_bot, Submodule.mem_bot] at hxmem
          rw [hxmem, map_zero, zero_add] at hab
          -- Now `z = g y` lies in `D`, forcing `y = 0`.
          have hyD : ρ.g y ∈ D := by rw [hab]; exact hzD
          have hymem : y ∈ Submodule.comap ρ.g D ⊓ Q₃ := ⟨hyD, hy⟩
          rw [hQ₃.1.eq_bot, Submodule.mem_bot] at hymem
          rw [hymem, map_zero] at hab
          exact hab.symm
        · rw [codisjoint_iff]
          have hUle : LinearMap.range ρ.f ≤ D ⊔ Q₂ := by
            rintro _ ⟨x, rfl⟩
            have hx : x ∈ (⊤ : Submodule k ρ.V₁) := Submodule.mem_top
            rw [← hQ₁.2.eq_top] at hx
            obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
            rw [← huv, map_add]
            exact Submodule.add_mem _ (Submodule.mem_sup_left hu)
              (Submodule.mem_sup_right (Submodule.mem_sup_left (Submodule.mem_map_of_mem hv)))
          have hWle : LinearMap.range ρ.g ≤ D ⊔ Q₂ := by
            rintro _ ⟨z, rfl⟩
            have hz : z ∈ (⊤ : Submodule k ρ.V₃) := Submodule.mem_top
            rw [← hQ₃.2.eq_top] at hz
            obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hz
            rw [← huv, map_add]
            exact Submodule.add_mem _ (Submodule.mem_sup_left hu)
              (Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_map_of_mem hv)))
          exact top_le_iff.mp (hsup ▸ sup_le hUle hWle)
      have hres := hind_cond (Submodule.comap ρ.f D) Q₁ D Q₂ (Submodule.comap ρ.g D) Q₃
        hQ₁ hDQ₂ hQ₃
        (fun x hx => hx) (fun x hx => Submodule.mem_sup_left (Submodule.mem_map_of_mem hx))
        (fun z hz => hz) (fun z hz => Submodule.mem_sup_right (Submodule.mem_map_of_mem hz))
      rcases hres with ⟨_, hDbot, _⟩ | ⟨_, hQ₂bot, _⟩
      · exact absurd hDbot hD
      · -- `D = ⊤`, so both maps are surjective.
        have hDtop : D = ⊤ := eq_top_of_isCompl_bot (hQ₂bot ▸ hDQ₂)
        have hftop : LinearMap.range ρ.f = ⊤ :=
          top_le_iff.mp (hDtop ▸ (inf_le_left : D ≤ LinearMap.range ρ.f))
        have hgtop : LinearMap.range ρ.g = ⊤ :=
          top_le_iff.mp (hDtop ▸ (inf_le_right : D ≤ LinearMap.range ρ.g))
        have hf_bij : Function.Bijective ρ.f := ⟨hf_inj, LinearMap.range_eq_top.mp hftop⟩
        have hg_bij : Function.Bijective ρ.g := ⟨hg_inj, LinearMap.range_eq_top.mp hgtop⟩
        have hdim₁ : Module.finrank k ρ.V₁ = Module.finrank k ρ.V₂ :=
          (LinearEquiv.ofBijective ρ.f hf_bij).finrank_eq
        have hdim₃ : Module.finrank k ρ.V₃ = Module.finrank k ρ.V₂ :=
          (LinearEquiv.ofBijective ρ.g hg_bij).finrank_eq
        have hV₂ : Module.finrank k ρ.V₂ = 1 := by
          rw [← Etingof.Example_6_2_2]
          refine ⟨Module.nontrivial_of_finrank_pos h₂, fun p₂ q₂ hpq₂ => ?_⟩
          have hpq₁ := isCompl_comap_of_bijective ρ.f hf_bij p₂ q₂ hpq₂
          have hpq₃ := isCompl_comap_of_bijective ρ.g hg_bij p₂ q₂ hpq₂
          have h := hind_cond (Submodule.comap ρ.f p₂) (Submodule.comap ρ.f q₂) p₂ q₂
            (Submodule.comap ρ.g p₂) (Submodule.comap ρ.g q₂) hpq₁ hpq₂ hpq₃
            (fun x hx => hx) (fun x hx => hx) (fun z hz => hz) (fun z hz => hz)
          rcases h with ⟨_, hp, _⟩ | ⟨_, hq, _⟩
          · exact Or.inl hp
          · exact Or.inr hq
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨by omega, hV₂, by omega, hf_bij, hg_bij⟩))))

end A₃SinkRep

/-!
## Classification: the six indecomposable representatives

We construct the six canonical indecomposable representations of `• → • ← •`, prove each is
indecomposable, and prove every indecomposable representation is isomorphic to exactly one of
them. This upgrades the dimension-vector necessary condition above to a classification of
isomorphism classes.
-/

open Module

/-- Isomorphism of representations of `• → • ← •`. -/
structure A₃SinkRep.Iso {k : Type*} [Field k] (ρ σ : A₃SinkRep k) where
  e₁ : ρ.V₁ ≃ₗ[k] σ.V₁
  e₂ : ρ.V₂ ≃ₗ[k] σ.V₂
  e₃ : ρ.V₃ ≃ₗ[k] σ.V₃
  comm_f : ∀ x, e₂ (ρ.f x) = σ.f (e₁ x)
  comm_g : ∀ z, e₂ (ρ.g z) = σ.g (e₃ z)

namespace A₃SinkRep.Iso

/-- The identity isomorphism. -/
def refl {k : Type*} [Field k] (ρ : A₃SinkRep k) : ρ.Iso ρ where
  e₁ := LinearEquiv.refl k ρ.V₁
  e₂ := LinearEquiv.refl k ρ.V₂
  e₃ := LinearEquiv.refl k ρ.V₃
  comm_f := fun _ => rfl
  comm_g := fun _ => rfl

/-- The inverse of an isomorphism. -/
def symm {k : Type*} [Field k] {ρ σ : A₃SinkRep k} (e : ρ.Iso σ) : σ.Iso ρ where
  e₁ := e.e₁.symm
  e₂ := e.e₂.symm
  e₃ := e.e₃.symm
  comm_f := fun y => by
    apply e.e₂.injective
    rw [e.e₂.apply_symm_apply, e.comm_f, e.e₁.apply_symm_apply]
  comm_g := fun y => by
    apply e.e₂.injective
    rw [e.e₂.apply_symm_apply, e.comm_g, e.e₃.apply_symm_apply]

/-- Composition of isomorphisms. -/
def trans {k : Type*} [Field k] {ρ σ τ : A₃SinkRep k} (e : ρ.Iso σ) (e' : σ.Iso τ) :
    ρ.Iso τ where
  e₁ := e.e₁.trans e'.e₁
  e₂ := e.e₂.trans e'.e₂
  e₃ := e.e₃.trans e'.e₃
  comm_f := fun x => by
    simp only [LinearEquiv.trans_apply]
    rw [e.comm_f, e'.comm_f]
  comm_g := fun z => by
    simp only [LinearEquiv.trans_apply]
    rw [e.comm_g, e'.comm_g]

/-- Isomorphic representations have equal dimensions at all three vertices. -/
lemma finrank_eq {k : Type*} [Field k] {ρ σ : A₃SinkRep k} (e : ρ.Iso σ) :
    Module.finrank k ρ.V₁ = Module.finrank k σ.V₁ ∧
    Module.finrank k ρ.V₂ = Module.finrank k σ.V₂ ∧
    Module.finrank k ρ.V₃ = Module.finrank k σ.V₃ :=
  ⟨e.e₁.finrank_eq, e.e₂.finrank_eq, e.e₃.finrank_eq⟩

end A₃SinkRep.Iso

/-- The representative `k → 0 ← 0`. -/
abbrev A₃SinkRep.rep_100 (k : Type*) [Field k] : A₃SinkRep k where
  V₁ := k
  V₂ := PUnit
  V₃ := PUnit
  f := 0
  g := 0

/-- The representative `0 → k ← 0`. -/
abbrev A₃SinkRep.rep_010 (k : Type*) [Field k] : A₃SinkRep k where
  V₁ := PUnit
  V₂ := k
  V₃ := PUnit
  f := 0
  g := 0

/-- The representative `0 → 0 ← k`. -/
abbrev A₃SinkRep.rep_001 (k : Type*) [Field k] : A₃SinkRep k where
  V₁ := PUnit
  V₂ := PUnit
  V₃ := k
  f := 0
  g := 0

/-- The representative `k ≃ k ← 0`. -/
abbrev A₃SinkRep.rep_110 (k : Type*) [Field k] : A₃SinkRep k where
  V₁ := k
  V₂ := k
  V₃ := PUnit
  f := LinearMap.id
  g := 0

/-- The representative `0 → k ≃ k`. -/
abbrev A₃SinkRep.rep_011 (k : Type*) [Field k] : A₃SinkRep k where
  V₁ := PUnit
  V₂ := k
  V₃ := k
  f := 0
  g := LinearMap.id

/-- The representative `k ≃ k ≃ k`. -/
abbrev A₃SinkRep.rep_111 (k : Type*) [Field k] : A₃SinkRep k where
  V₁ := k
  V₂ := k
  V₃ := k
  f := LinearMap.id
  g := LinearMap.id

namespace A₃SinkRep

/-- Every submodule of a subsingleton module is trivial. -/
theorem submodule_eq_bot_of_subsingleton {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    [Subsingleton M] (p : Submodule k M) : p = ⊥ := by
  rw [eq_bot_iff]; intro x _; rw [Submodule.mem_bot]; exact Subsingleton.elim _ _

theorem rep_100_indecomposable (k : Type*) [Field k] : (rep_100 k).Indecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ hpq₁ _ _ _ _ _ _
  have hsum : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]; exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, submodule_eq_bot_of_subsingleton p₂,
      submodule_eq_bot_of_subsingleton p₃⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega), submodule_eq_bot_of_subsingleton q₂,
      submodule_eq_bot_of_subsingleton q₃⟩

theorem rep_010_indecomposable (k : Type*) [Field k] : (rep_010 k).Indecomposable := by
  refine ⟨Or.inr (Or.inl Module.finrank_pos), ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ _ hpq₂ _ _ _ _ _
  have hsum : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₂) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁, Submodule.finrank_eq_zero.mp h0,
      submodule_eq_bot_of_subsingleton p₃⟩
  · exact Or.inr ⟨submodule_eq_bot_of_subsingleton q₁, Submodule.finrank_eq_zero.mp (by omega),
      submodule_eq_bot_of_subsingleton q₃⟩

theorem rep_001_indecomposable (k : Type*) [Field k] : (rep_001 k).Indecomposable := by
  refine ⟨Or.inr (Or.inr Module.finrank_pos), ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ _ _ hpq₃ _ _ _ _
  have hsum : Module.finrank k p₃ + Module.finrank k q₃ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₃]; exact finrank_self k
  rcases Nat.eq_zero_or_pos (Module.finrank k p₃) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁, submodule_eq_bot_of_subsingleton p₂,
      Submodule.finrank_eq_zero.mp h0⟩
  · exact Or.inr ⟨submodule_eq_bot_of_subsingleton q₁, submodule_eq_bot_of_subsingleton q₂,
      Submodule.finrank_eq_zero.mp (by omega)⟩

theorem rep_110_indecomposable (k : Type*) [Field k] : (rep_110 k).Indecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ hpq₁ hpq₂ _ hfp hfq _ _
  have hsum₁ : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]; exact finrank_self k
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  have hfp' : Module.finrank k p₁ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfp x hx)
  have hfq' : Module.finrank k q₁ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfq x hx)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, Submodule.finrank_eq_zero.mp (by omega),
      submodule_eq_bot_of_subsingleton p₃⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega), submodule_eq_bot_of_subsingleton q₃⟩

theorem rep_011_indecomposable (k : Type*) [Field k] : (rep_011 k).Indecomposable := by
  refine ⟨Or.inr (Or.inl Module.finrank_pos), ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ _ hpq₂ hpq₃ _ _ hgp hgq
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  have hsum₃ : Module.finrank k p₃ + Module.finrank k q₃ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₃]; exact finrank_self k
  have hgp' : Module.finrank k p₃ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun z hz => by simpa using hgp z hz)
  have hgq' : Module.finrank k q₃ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun z hz => by simpa using hgq z hz)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₃) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁,
      Submodule.finrank_eq_zero.mp (by omega), Submodule.finrank_eq_zero.mp h0⟩
  · exact Or.inr ⟨submodule_eq_bot_of_subsingleton q₁,
      Submodule.finrank_eq_zero.mp (by omega), Submodule.finrank_eq_zero.mp (by omega)⟩

theorem rep_111_indecomposable (k : Type*) [Field k] : (rep_111 k).Indecomposable := by
  refine ⟨Or.inl Module.finrank_pos, ?_⟩
  intro p₁ q₁ p₂ q₂ p₃ q₃ hpq₁ hpq₂ hpq₃ hfp hfq hgp hgq
  have hsum₁ : Module.finrank k p₁ + Module.finrank k q₁ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₁]; exact finrank_self k
  have hsum₂ : Module.finrank k p₂ + Module.finrank k q₂ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₂]; exact finrank_self k
  have hsum₃ : Module.finrank k p₃ + Module.finrank k q₃ = 1 := by
    rw [Submodule.finrank_add_eq_of_isCompl hpq₃]; exact finrank_self k
  have hfp' : Module.finrank k p₁ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfp x hx)
  have hfq' : Module.finrank k q₁ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun x hx => by simpa using hfq x hx)
  have hgp' : Module.finrank k p₃ ≤ Module.finrank k p₂ :=
    Submodule.finrank_mono (fun z hz => by simpa using hgp z hz)
  have hgq' : Module.finrank k q₃ ≤ Module.finrank k q₂ :=
    Submodule.finrank_mono (fun z hz => by simpa using hgq z hz)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega)⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega), Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The six representatives, indexed by `Fin 6`. -/
def rep (k : Type*) [Field k] : Fin 6 → A₃SinkRep k
  | 0 => rep_100 k
  | 1 => rep_010 k
  | 2 => rep_001 k
  | 3 => rep_110 k
  | 4 => rep_011 k
  | 5 => rep_111 k

/-- The six representatives are indecomposable. -/
theorem rep_indecomposable (k : Type*) [Field k] (i : Fin 6) : (rep k i).Indecomposable := by
  fin_cases i
  · exact rep_100_indecomposable k
  · exact rep_010_indecomposable k
  · exact rep_001_indecomposable k
  · exact rep_110_indecomposable k
  · exact rep_011_indecomposable k
  · exact rep_111_indecomposable k

/-- Dimension vector of a representation of `• → • ← •`. -/
noncomputable def dimvec (k : Type*) [Field k] (σ : A₃SinkRep k) : ℕ × ℕ × ℕ :=
  (Module.finrank k σ.V₁, Module.finrank k σ.V₂, Module.finrank k σ.V₃)

theorem Iso.dimvec_eq {k : Type*} [Field k] {ρ σ : A₃SinkRep k} (e : ρ.Iso σ) :
    dimvec k ρ = dimvec k σ := by
  obtain ⟨h₁, h₂, h₃⟩ := e.finrank_eq
  simp [dimvec, h₁, h₂, h₃]

theorem dimvec_rep_100 (k : Type*) [Field k] : dimvec k (rep_100 k) = (1, 0, 0) := by
  simp [dimvec, finrank_self, finrank_zero_of_subsingleton]

theorem dimvec_rep_010 (k : Type*) [Field k] : dimvec k (rep_010 k) = (0, 1, 0) := by
  simp [dimvec, finrank_self, finrank_zero_of_subsingleton]

theorem dimvec_rep_001 (k : Type*) [Field k] : dimvec k (rep_001 k) = (0, 0, 1) := by
  simp [dimvec, finrank_self, finrank_zero_of_subsingleton]

theorem dimvec_rep_110 (k : Type*) [Field k] : dimvec k (rep_110 k) = (1, 1, 0) := by
  simp [dimvec, finrank_self, finrank_zero_of_subsingleton]

theorem dimvec_rep_011 (k : Type*) [Field k] : dimvec k (rep_011 k) = (0, 1, 1) := by
  simp [dimvec, finrank_self, finrank_zero_of_subsingleton]

theorem dimvec_rep_111 (k : Type*) [Field k] : dimvec k (rep_111 k) = (1, 1, 1) := by
  simp [dimvec, finrank_self]

/-- **Example 6.2.4(2) (Etingof), classification.** Every indecomposable representation of the
quiver `• → • ← •` is isomorphic to exactly one of the six representatives. This is the
solution of the pair of subspaces problem. -/
theorem exists_unique_iso_rep (k : Type*) [Field k] (ρ : A₃SinkRep k)
    (hind : ρ.Indecomposable) : ∃! i : Fin 6, Nonempty (ρ.Iso (rep k i)) := by
  have hexists : ∃ i : Fin 6, Nonempty (ρ.Iso (rep k i)) := by
    rcases _root_.Etingof.Example_6_2_4_sink k ρ hind with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, hf⟩ | ⟨h1, h2, h3, hg⟩ |
        ⟨h1, h2, h3, hf, hg⟩
    · refine ⟨0, ?_⟩
      change Nonempty (ρ.Iso (rep_100 k))
      exact ⟨{ e₁ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact (finrank_self k).symm)).some
               e₂ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact finrank_zero_of_subsingleton.symm)).some
               e₃ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
               comm_f := fun _ => Subsingleton.elim _ _
               comm_g := fun _ => Subsingleton.elim _ _ }⟩
    · refine ⟨1, ?_⟩
      change Nonempty (ρ.Iso (rep_010 k))
      haveI hs₁ : Subsingleton ρ.V₁ := Module.finrank_zero_iff.mp h1
      haveI hs₃ : Subsingleton ρ.V₃ := Module.finrank_zero_iff.mp h3
      exact ⟨{ e₁ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
               e₂ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact (finrank_self k).symm)).some
               e₃ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
               comm_f := fun x => by rw [Subsingleton.elim x 0]; simp
               comm_g := fun z => by rw [Subsingleton.elim z 0]; simp }⟩
    · refine ⟨2, ?_⟩
      change Nonempty (ρ.Iso (rep_001 k))
      exact ⟨{ e₁ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
               e₂ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact finrank_zero_of_subsingleton.symm)).some
               e₃ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact (finrank_self k).symm)).some
               comm_f := fun _ => Subsingleton.elim _ _
               comm_g := fun _ => Subsingleton.elim _ _ }⟩
    · refine ⟨3, ?_⟩
      change Nonempty (ρ.Iso (rep_110 k))
      haveI hs₃ : Subsingleton ρ.V₃ := Module.finrank_zero_iff.mp h3
      obtain ⟨e₁⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.V₁) (M' := k) (by rw [h1]; exact (finrank_self k).symm)
      let fEq : ρ.V₁ ≃ₗ[k] ρ.V₂ := LinearEquiv.ofBijective ρ.f hf
      refine ⟨{ e₁ := e₁, e₂ := fEq.symm.trans e₁, e₃ := ?_
                comm_f := fun x => ?_
                comm_g := fun z => by rw [Subsingleton.elim z 0]; simp }⟩
      · exact (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
          (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
      · have hfx : fEq.symm (ρ.f x) = x := fEq.symm_apply_apply x
        simp only [LinearEquiv.trans_apply, hfx]
        rfl
    · refine ⟨4, ?_⟩
      change Nonempty (ρ.Iso (rep_011 k))
      haveI hs₁ : Subsingleton ρ.V₁ := Module.finrank_zero_iff.mp h1
      obtain ⟨e₃⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.V₃) (M' := k) (by rw [h3]; exact (finrank_self k).symm)
      let gEq : ρ.V₃ ≃ₗ[k] ρ.V₂ := LinearEquiv.ofBijective ρ.g hg
      refine ⟨{ e₁ := ?_, e₂ := gEq.symm.trans e₃, e₃ := e₃
                comm_f := fun x => by rw [Subsingleton.elim x 0]; simp
                comm_g := fun z => ?_ }⟩
      · exact (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
          (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
      · have hgz : gEq.symm (ρ.g z) = z := gEq.symm_apply_apply z
        simp only [LinearEquiv.trans_apply, hgz]
        rfl
    · refine ⟨5, ?_⟩
      change Nonempty (ρ.Iso (rep_111 k))
      obtain ⟨e₂⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.V₂) (M' := (rep_111 k).V₂) (by rw [h2]; exact (finrank_self k).symm)
      let fEq : ρ.V₁ ≃ₗ[k] ρ.V₂ := LinearEquiv.ofBijective ρ.f hf
      let gEq : ρ.V₃ ≃ₗ[k] ρ.V₂ := LinearEquiv.ofBijective ρ.g hg
      exact ⟨{ e₁ := fEq.trans e₂, e₂ := e₂, e₃ := gEq.trans e₂
               comm_f := fun x => by simp only [LinearEquiv.trans_apply]; rfl
               comm_g := fun z => by simp only [LinearEquiv.trans_apply]; rfl }⟩
  obtain ⟨i, hi⟩ := hexists
  refine ⟨i, hi, fun j hj => ?_⟩
  obtain ⟨ei⟩ := hi
  obtain ⟨ej⟩ := hj
  have hdv : dimvec k (rep k j) = dimvec k (rep k i) := (ej.symm.trans ei).dimvec_eq
  fin_cases i <;> fin_cases j <;>
    simp_all [rep, dimvec_rep_100, dimvec_rep_010, dimvec_rep_001, dimvec_rep_110,
      dimvec_rep_011, dimvec_rep_111]

end A₃SinkRep

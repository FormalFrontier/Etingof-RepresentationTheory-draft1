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
  push_neg at h
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
  push_neg at h
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
  push_neg at h
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
theorem Etingof.Example_6_2_4_sink (k : Type*) [Field k] (ρ : A₃SinkRep k)
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

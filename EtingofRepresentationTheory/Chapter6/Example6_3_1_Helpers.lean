import Mathlib
import EtingofRepresentationTheory.Chapter6.Example6_2_2

/-!
# Example 6.3.1 Helpers: D₄ Representation Infrastructure

Helper definitions and lemmas for the classification of indecomposable
representations of the D₄ quiver.

See `Example6_3_1.lean` for the main classification theorem.
-/

/-- A representation of the D₄ quiver with orientation V₁ → V, V₂ → V, V₃ → V
(three arms mapping into a central vertex). -/
structure D₄Rep (k : Type*) [Field k] where
  /-- The central vector space -/
  V : Type*
  /-- The first arm -/
  V₁ : Type*
  /-- The second arm -/
  V₂ : Type*
  /-- The third arm -/
  V₃ : Type*
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module k V]
  [finiteDimensionalV : FiniteDimensional k V]
  [addCommGroup₁ : AddCommGroup V₁]
  [module₁ : Module k V₁]
  [finiteDimensional₁ : FiniteDimensional k V₁]
  [addCommGroup₂ : AddCommGroup V₂]
  [module₂ : Module k V₂]
  [finiteDimensional₂ : FiniteDimensional k V₂]
  [addCommGroup₃ : AddCommGroup V₃]
  [module₃ : Module k V₃]
  [finiteDimensional₃ : FiniteDimensional k V₃]
  /-- Linear map from arm 1 to center -/
  A₁ : V₁ →ₗ[k] V
  /-- Linear map from arm 2 to center -/
  A₂ : V₂ →ₗ[k] V
  /-- Linear map from arm 3 to center -/
  A₃ : V₃ →ₗ[k] V

attribute [instance] D₄Rep.addCommGroupV D₄Rep.moduleV D₄Rep.finiteDimensionalV
  D₄Rep.addCommGroup₁ D₄Rep.module₁ D₄Rep.finiteDimensional₁
  D₄Rep.addCommGroup₂ D₄Rep.module₂ D₄Rep.finiteDimensional₂
  D₄Rep.addCommGroup₃ D₄Rep.module₃ D₄Rep.finiteDimensional₃

/-- A D₄-representation is indecomposable if it is nontrivial and for any
decomposition V = p ⊕ q, V₁ = p₁ ⊕ q₁, V₂ = p₂ ⊕ q₂, V₃ = p₃ ⊕ q₃
compatible with the maps (Aᵢ maps pᵢ into p and qᵢ into q), one of the
summands is zero. -/
def D₄Rep.Indecomposable {k : Type*} [Field k] (ρ : D₄Rep k) : Prop :=
  (0 < Module.finrank k ρ.V ∨ 0 < Module.finrank k ρ.V₁ ∨
   0 < Module.finrank k ρ.V₂ ∨ 0 < Module.finrank k ρ.V₃) ∧
  ∀ (p q : Submodule k ρ.V)
    (p₁ q₁ : Submodule k ρ.V₁)
    (p₂ q₂ : Submodule k ρ.V₂)
    (p₃ q₃ : Submodule k ρ.V₃),
    IsCompl p q → IsCompl p₁ q₁ → IsCompl p₂ q₂ → IsCompl p₃ q₃ →
    (∀ x ∈ p₁, ρ.A₁ x ∈ p) → (∀ x ∈ q₁, ρ.A₁ x ∈ q) →
    (∀ x ∈ p₂, ρ.A₂ x ∈ p) → (∀ x ∈ q₂, ρ.A₂ x ∈ q) →
    (∀ x ∈ p₃, ρ.A₃ x ∈ p) → (∀ x ∈ q₃, ρ.A₃ x ∈ q) →
    (p = ⊥ ∧ p₁ = ⊥ ∧ p₂ = ⊥ ∧ p₃ = ⊥) ∨
    (q = ⊥ ∧ q₁ = ⊥ ∧ q₂ = ⊥ ∧ q₃ = ⊥)

/-- The dimension vector of a D₄ representation: (dim V, dim V₁, dim V₂, dim V₃). -/
noncomputable def D₄Rep.dimVector {k : Type*} [Field k] (ρ : D₄Rep k) : ℕ × ℕ × ℕ × ℕ :=
  (Module.finrank k ρ.V, Module.finrank k ρ.V₁,
   Module.finrank k ρ.V₂, Module.finrank k ρ.V₃)

/-- The set of dimension vectors of the 12 indecomposable representations of D₄.
These correspond to the 12 positive roots of the D₄ root system.

Organized as (dim V, dim V₁, dim V₂, dim V₃):
- 3 kernel representations: (0,1,0,0), (0,0,1,0), (0,0,0,1)
- 1 simple at center: (1,0,0,0)
- 3 center + one arm: (1,1,0,0), (1,0,1,0), (1,0,0,1)
- 3 center + two arms: (1,1,1,0), (1,1,0,1), (1,0,1,1)
- 1 all arms: (1,1,1,1)
- 1 generic: (2,1,1,1) -/
def D₄_indecomposable_dimVectors : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {(0,1,0,0), (0,0,1,0), (0,0,0,1),  -- kernel reps
   (1,0,0,0),                          -- simple at center
   (1,1,0,0), (1,0,1,0), (1,0,0,1),  -- center + one arm
   (1,1,1,0), (1,1,0,1), (1,0,1,1),  -- center + two arms
   (1,1,1,1),                          -- all arms equal
   (2,1,1,1)}                          -- generic

/-- **Example 6.3.1 (Etingof)**: Every indecomposable representation of the D₄ quiver
(with orientation V₁ → V ← V₃, V₂ → V) has dimension vector in the set of
12 positive roots of D₄. These are all the dimension vectors (dim V, dim V₁, dim V₂, dim V₃)
of indecomposable representations.

The proof proceeds by iteratively splitting off direct summands:
1. Split off kernels of A₁, A₂, A₃ to make all maps injective
2. Split off complement of V₁+V₂+V₃ (simple at center) to make sum = V
3. Split off V₁∩V₂∩V₃ to make triple intersection = 0
4. Split off pairwise intersections to make all pairwise intersections = 0
5. Split off Vᵢ ∩ (Vⱼ⊕Vₖ) complements to get Vᵢ ⊆ Vⱼ⊕Vₖ
6. The remaining representation decomposes into copies of (2,1,1,1) -/
-- Step 1: Splitting off kernels. For each map Aᵢ, either ker Aᵢ = ⊥
-- or all other components have dimension 0.
lemma ker_A₁_or_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.A₁ = ⊥ ∨
    (Module.finrank k ρ.V = 0 ∧ Module.finrank k ρ.V₂ = 0 ∧
     Module.finrank k ρ.V₃ = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.A₁)
  -- Decompose: (⊥, ker A₁, ⊥, ⊥) ⊕ (⊤, q₁, ⊤, ⊤)
  have := hind.2 ⊥ ⊤ (LinearMap.ker ρ.A₁) q₁ ⊥ ⊤ ⊥ ⊤
    isCompl_bot_top hq₁ isCompl_bot_top isCompl_bot_top
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨_, hk, _, _⟩ | ⟨htop, _, htop₂, htop₃⟩
  · exact hker hk
  · apply hrest
    exact ⟨by rw [← finrank_top (R := k) (M := ρ.V), htop, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₂), htop₂, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₃), htop₃, finrank_bot]⟩

lemma ker_A₂_or_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.A₂ = ⊥ ∨
    (Module.finrank k ρ.V = 0 ∧ Module.finrank k ρ.V₁ = 0 ∧
     Module.finrank k ρ.V₃ = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₂, hq₂⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.A₂)
  have := hind.2 ⊥ ⊤ ⊥ ⊤ (LinearMap.ker ρ.A₂) q₂ ⊥ ⊤
    isCompl_bot_top isCompl_bot_top hq₂ isCompl_bot_top
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨_, _, hk, _⟩ | ⟨htop, htop₁, _, htop₃⟩
  · exact hker hk
  · apply hrest
    exact ⟨by rw [← finrank_top (R := k) (M := ρ.V), htop, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₁), htop₁, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₃), htop₃, finrank_bot]⟩

lemma ker_A₃_or_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable) :
    LinearMap.ker ρ.A₃ = ⊥ ∨
    (Module.finrank k ρ.V = 0 ∧ Module.finrank k ρ.V₁ = 0 ∧
     Module.finrank k ρ.V₂ = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₃, hq₃⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.A₃)
  have := hind.2 ⊥ ⊤ ⊥ ⊤ ⊥ ⊤ (LinearMap.ker ρ.A₃) q₃
    isCompl_bot_top isCompl_bot_top isCompl_bot_top hq₃
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨_, _, _, hk⟩ | ⟨htop, htop₁, htop₂, _⟩
  · exact hker hk
  · apply hrest
    exact ⟨by rw [← finrank_top (R := k) (M := ρ.V), htop, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₁), htop₁, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.V₂), htop₂, finrank_bot]⟩

-- Helper: if ρ is indecomposable and V = V₂ = V₃ = 0, then V₁ is indecomposable
-- as a vector space, hence dim V₁ = 1.
lemma dim_V₁_eq_one_of_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hV : Module.finrank k ρ.V = 0) (hV₂ : Module.finrank k ρ.V₂ = 0)
    (hV₃ : Module.finrank k ρ.V₃ = 0) :
    Module.finrank k ρ.V₁ = 1 := by
  rw [← Etingof.Example_6_2_2]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p₁ q₁ hpq₁ => ?_⟩
  · have : 0 < Module.finrank k ρ.V₁ := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htopV : (⊤ : Submodule k ρ.V) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV)
    have htopV₂ : (⊤ : Submodule k ρ.V₂) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV₂)
    have htopV₃ : (⊤ : Submodule k ρ.V₃) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV₃)
    have hV_zero : ∀ (x : ρ.V), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V) := Submodule.mem_top
      rwa [htopV, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ p₁ q₁ ⊥ ⊤ ⊥ ⊤
      isCompl_bot_top hpq₁ isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV_zero (ρ.A₁ x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨_, hp₁, _, _⟩ | ⟨_, hq₁, _, _⟩
    · left; exact hp₁
    · right; exact hq₁

lemma dim_V₂_eq_one_of_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hV : Module.finrank k ρ.V = 0) (hV₁ : Module.finrank k ρ.V₁ = 0)
    (hV₃ : Module.finrank k ρ.V₃ = 0) :
    Module.finrank k ρ.V₂ = 1 := by
  rw [← Etingof.Example_6_2_2]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p₂ q₂ hpq₂ => ?_⟩
  · have : 0 < Module.finrank k ρ.V₂ := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htopV : (⊤ : Submodule k ρ.V) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV)
    have hV_zero : ∀ (x : ρ.V), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V) := Submodule.mem_top
      rwa [htopV, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ ⊥ ⊤ p₂ q₂ ⊥ ⊤
      isCompl_bot_top isCompl_bot_top hpq₂ isCompl_bot_top
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x _ => by rw [hV_zero (ρ.A₂ x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨_, _, hp₂, _⟩ | ⟨_, _, hq₂, _⟩
    · left; exact hp₂
    · right; exact hq₂

lemma dim_V₃_eq_one_of_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hV : Module.finrank k ρ.V = 0) (hV₁ : Module.finrank k ρ.V₁ = 0)
    (hV₂ : Module.finrank k ρ.V₂ = 0) :
    Module.finrank k ρ.V₃ = 1 := by
  rw [← Etingof.Example_6_2_2]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p₃ q₃ hpq₃ => ?_⟩
  · have : 0 < Module.finrank k ρ.V₃ := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htopV : (⊤ : Submodule k ρ.V) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV)
    have hV_zero : ∀ (x : ρ.V), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V) := Submodule.mem_top
      rwa [htopV, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ ⊥ ⊤ ⊥ ⊤ p₃ q₃
      isCompl_bot_top isCompl_bot_top isCompl_bot_top hpq₃
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x _ => by rw [hV_zero (ρ.A₃ x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨_, _, _, hp₃⟩ | ⟨_, _, _, hq₃⟩
    · left; exact hp₃
    · right; exact hq₃

-- Helper: injective linear map into a zero-dimensional space means the source is zero-dimensional
lemma finrank_eq_zero_of_injective_into_zero {k : Type*} [Field k]
    {V₁ V : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V₁ →ₗ[k] V) (hf : LinearMap.ker f = ⊥) (hV : Module.finrank k V = 0) :
    Module.finrank k V₁ = 0 := by
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hf
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

-- Helper: if all arms are zero-dimensional and ρ is indecomposable, then dim V = 1
lemma dim_V_eq_one_of_arms_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (h₁ : Module.finrank k ρ.V₁ = 0) (h₂ : Module.finrank k ρ.V₂ = 0)
    (h₃ : Module.finrank k ρ.V₃ = 0) :
    Module.finrank k ρ.V = 1 := by
  rw [← Etingof.Example_6_2_2]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p q hpq => ?_⟩
  · have : 0 < Module.finrank k ρ.V := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htop₁ : (⊤ : Submodule k ρ.V₁) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₁)
    have htop₂ : (⊤ : Submodule k ρ.V₂) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₂)
    have htop₃ : (⊤ : Submodule k ρ.V₃) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₃)
    have hV₁_zero : ∀ (x : ρ.V₁), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V₁) := Submodule.mem_top
      rwa [htop₁, Submodule.mem_bot] at this
    have hV₂_zero : ∀ (x : ρ.V₂), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V₂) := Submodule.mem_top
      rwa [htop₂, Submodule.mem_bot] at this
    have hV₃_zero : ∀ (x : ρ.V₃), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.V₃) := Submodule.mem_top
      rwa [htop₃, Submodule.mem_bot] at this
    specialize hind_cond p q ⊥ ⊤ ⊥ ⊤ ⊥ ⊤
      hpq isCompl_bot_top isCompl_bot_top isCompl_bot_top
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun x _ => by rw [hV₁_zero x, map_zero]; exact Submodule.zero_mem _)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun x _ => by rw [hV₂_zero x, map_zero]; exact Submodule.zero_mem _)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun x _ => by rw [hV₃_zero x, map_zero]; exact Submodule.zero_mem _)
    rcases hind_cond with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
    · left; exact hp
    · right; exact hq

-- Step 2: range sum = ⊤ or all arms are zero
lemma range_sum_eq_top_or_arms_zero {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥) :
    LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃ = ⊤ ∨
    (Module.finrank k ρ.V₁ = 0 ∧ Module.finrank k ρ.V₂ = 0 ∧
     Module.finrank k ρ.V₃ = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hR, harms⟩ := h
  set R := LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃ with hR_def
  obtain ⟨S, hRS⟩ := Submodule.exists_isCompl R
  -- Decompose: (R, V₁, V₂, V₃) ⊕ (S, 0, 0, 0)
  have := hind.2 R S ⊤ ⊥ ⊤ ⊥ ⊤ ⊥
    hRS isCompl_top_bot isCompl_top_bot isCompl_top_bot
    (fun x _ => by
      have h : ρ.A₁ x ∈ LinearMap.range ρ.A₁ := LinearMap.mem_range.mpr ⟨x, rfl⟩
      exact Submodule.mem_sup_left (Submodule.mem_sup_left h))
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun x _ => by
      have h : ρ.A₂ x ∈ LinearMap.range ρ.A₂ := LinearMap.mem_range.mpr ⟨x, rfl⟩
      exact Submodule.mem_sup_left (Submodule.mem_sup_right h))
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun x _ => by
      have h : ρ.A₃ x ∈ LinearMap.range ρ.A₃ := LinearMap.mem_range.mpr ⟨x, rfl⟩
      exact Submodule.mem_sup_right h)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
  rcases this with ⟨hRbot, htop₁, htop₂, htop₃⟩ | ⟨hSbot, _, _, _⟩
  · -- R = ⊥ means all ranges are zero, so all arms are zero
    apply harms
    have hR₁ : LinearMap.range ρ.A₁ = ⊥ := by
      have h : LinearMap.range ρ.A₁ ≤ R :=
        le_sup_left.trans (le_sup_left (a := LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂))
      rw [hRbot] at h; exact bot_unique h
    have hR₂ : LinearMap.range ρ.A₂ = ⊥ := by
      have h : LinearMap.range ρ.A₂ ≤ R :=
        le_sup_right.trans (le_sup_left (a := LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂))
      rw [hRbot] at h; exact bot_unique h
    have hR₃ : LinearMap.range ρ.A₃ = ⊥ := by
      have h : LinearMap.range ρ.A₃ ≤ R := le_sup_right
      rw [hRbot] at h; exact bot_unique h
    exact ⟨by rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hA₁)]; simp [hR₁],
           by rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hA₂)]; simp [hR₂],
           by rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hA₃)]; simp [hR₃]⟩
  · have : R = ⊤ := by
      have := hRS.sup_eq_top
      rw [hSbot, sup_bot_eq] at this
      exact this
    exact hR this

-- Helper: a "clean" decomposition where each range lies in one summand.
-- If V = p ⊕ q and each range(Aᵢ) ≤ p or ≤ q, then p = ⊥ or q = ⊥.
lemma decomp_of_ranges_split {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (p q : Submodule k ρ.V) (hpq : IsCompl p q)
    (h₁ : LinearMap.range ρ.A₁ ≤ p ∨ LinearMap.range ρ.A₁ ≤ q)
    (h₂ : LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q)
    (h₃ : LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) :
    p = ⊥ ∨ q = ⊥ := by
  -- For each arm: if range ≤ p, use (⊤, ⊥); if range ≤ q, use (⊥, ⊤)
  -- Construct compatible decomposition per arm
  have arm₁ : ∃ (p₁ q₁ : Submodule k ρ.V₁), IsCompl p₁ q₁ ∧
      (∀ x ∈ p₁, ρ.A₁ x ∈ p) ∧ (∀ x ∈ q₁, ρ.A₁ x ∈ q) := by
    rcases h₁ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  have arm₂ : ∃ (p₂ q₂ : Submodule k ρ.V₂), IsCompl p₂ q₂ ∧
      (∀ x ∈ p₂, ρ.A₂ x ∈ p) ∧ (∀ x ∈ q₂, ρ.A₂ x ∈ q) := by
    rcases h₂ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  have arm₃ : ∃ (p₃ q₃ : Submodule k ρ.V₃), IsCompl p₃ q₃ ∧
      (∀ x ∈ p₃, ρ.A₃ x ∈ p) ∧ (∀ x ∈ q₃, ρ.A₃ x ∈ q) := by
    rcases h₃ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  obtain ⟨p₁, q₁, hc₁, hp₁, hq₁⟩ := arm₁
  obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := arm₂
  obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := arm₃
  have := hind.2 p q p₁ q₁ p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃ hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
  rcases this with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
  · left; exact hp
  · right; exact hq

-- When A₁ is surjective (range = ⊤) and A₁ is injective, the comap of a
-- complement p ⊕ q = V gives a valid IsCompl decomposition of V₁.
lemma comap_isCompl_of_surj_inj {k : Type*} [Field k]
    {V₁ V : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V] [Module k V]
    (A : V₁ →ₗ[k] V) (hA_inj : Function.Injective A) (hA_surj : LinearMap.range A = ⊤)
    (p q : Submodule k V) (hpq : IsCompl p q) :
    IsCompl (Submodule.comap A p) (Submodule.comap A q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxp hxq
    have : A x ∈ p ⊓ q := ⟨hxp, hxq⟩
    rw [hpq.inf_eq_bot, Submodule.mem_bot] at this
    exact hA_inj (this.trans (map_zero _).symm)
  · rw [codisjoint_iff]; ext x
    simp only [Submodule.mem_sup, Submodule.mem_comap, Submodule.mem_top, iff_true]
    have hA_surj' : Function.Surjective A := LinearMap.range_eq_top.mp hA_surj
    have hx_top : A x ∈ (⊤ : Submodule k V) := Submodule.mem_top
    rw [← hpq.sup_eq_top] at hx_top
    obtain ⟨yp, hyp, yq, hyq, heq⟩ := Submodule.mem_sup.mp hx_top
    obtain ⟨x₁, hx₁⟩ := hA_surj' yp
    obtain ⟨x₂, hx₂⟩ := hA_surj' yq
    have : x = x₁ + x₂ := hA_inj (by rw [map_add, hx₁, hx₂, heq])
    exact ⟨x₁, by rw [show A x₁ = yp from hx₁]; exact hyp,
           x₂, by rw [show A x₂ = yq from hx₂]; exact hyq, this.symm⟩

-- Two distinct 1-dim submodules in a 2-dim space are complementary.
lemma isCompl_of_finrank_one_ne {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2)
    (p q : Submodule k V) (hp : Module.finrank k p = 1) (hq : Module.finrank k q = 1)
    (hne : p ≠ q) : IsCompl p q := by
  -- Key fact: finrank(p ⊓ q) ≤ 1 (since p ⊓ q ≤ p)
  have hpq_le : Module.finrank k (p ⊓ q : Submodule k V) ≤ 1 :=
    (Submodule.finrank_mono (inf_le_left (a := p) (b := q))).trans hp.le
  -- If finrank(p ⊓ q) = 1, then p ⊓ q = p = q, contradiction
  have hpq_zero : Module.finrank k (p ⊓ q : Submodule k V) = 0 := by
    by_contra h; push_neg at h
    have hpq_eq : Module.finrank k (p ⊓ q : Submodule k V) = 1 := by omega
    have h1 : (p ⊓ q : Submodule k V) = p :=
      Submodule.eq_of_le_of_finrank_le (inf_le_left (a := p) (b := q)) (by omega)
    have h2 : (p ⊓ q : Submodule k V) = q :=
      Submodule.eq_of_le_of_finrank_le (inf_le_right (a := p) (b := q)) (by omega)
    exact hne (h1.symm.trans h2)
  -- finrank(p ⊔ q) = 1 + 1 - 0 = 2
  have hpq_sup : Module.finrank k (p ⊔ q : Submodule k V) = 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq p q; omega
  constructor
  · -- Disjoint: finrank(p ⊓ q) = 0 → p ⊓ q = ⊥
    rw [disjoint_iff]
    exact Submodule.finrank_eq_zero.mp hpq_zero
  · -- Codisjoint: finrank(p ⊔ q) = finrank V → p ⊔ q = ⊤
    rw [codisjoint_iff]
    exact Submodule.eq_top_of_finrank_eq (by omega)

-- General decomposition: for each arm, either its range fits in a summand (use ⊤/⊥),
-- or it is bijective (use comap). In either case, indecomposability forces p = ⊥ or q = ⊥.
lemma decomp_general {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (p q : Submodule k ρ.V) (hpq : IsCompl p q)
    (h₁ : (LinearMap.range ρ.A₁ ≤ p ∨ LinearMap.range ρ.A₁ ≤ q) ∨
           (Function.Injective ρ.A₁ ∧ LinearMap.range ρ.A₁ = ⊤))
    (h₂ : (LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q) ∨
           (Function.Injective ρ.A₂ ∧ LinearMap.range ρ.A₂ = ⊤))
    (h₃ : (LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) ∨
           (Function.Injective ρ.A₃ ∧ LinearMap.range ρ.A₃ = ⊤)) :
    p = ⊥ ∨ q = ⊥ := by
  -- Construct compatible arm decomposition for each arm
  have arm₁ : ∃ (p₁ q₁ : Submodule k ρ.V₁), IsCompl p₁ q₁ ∧
      (∀ x ∈ p₁, ρ.A₁ x ∈ p) ∧ (∀ x ∈ q₁, ρ.A₁ x ∈ q) := by
    rcases h₁ with (h | h) | ⟨hinj, hsurj⟩
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
    · exact ⟨Submodule.comap ρ.A₁ p, Submodule.comap ρ.A₁ q,
        comap_isCompl_of_surj_inj ρ.A₁ hinj hsurj p q hpq,
        fun x hx => hx, fun x hx => hx⟩
  have arm₂ : ∃ (p₂ q₂ : Submodule k ρ.V₂), IsCompl p₂ q₂ ∧
      (∀ x ∈ p₂, ρ.A₂ x ∈ p) ∧ (∀ x ∈ q₂, ρ.A₂ x ∈ q) := by
    rcases h₂ with (h | h) | ⟨hinj, hsurj⟩
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
    · exact ⟨Submodule.comap ρ.A₂ p, Submodule.comap ρ.A₂ q,
        comap_isCompl_of_surj_inj ρ.A₂ hinj hsurj p q hpq,
        fun x hx => hx, fun x hx => hx⟩
  have arm₃ : ∃ (p₃ q₃ : Submodule k ρ.V₃), IsCompl p₃ q₃ ∧
      (∀ x ∈ p₃, ρ.A₃ x ∈ p) ∧ (∀ x ∈ q₃, ρ.A₃ x ∈ q) := by
    rcases h₃ with (h | h) | ⟨hinj, hsurj⟩
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
    · exact ⟨Submodule.comap ρ.A₃ p, Submodule.comap ρ.A₃ q,
        comap_isCompl_of_surj_inj ρ.A₃ hinj hsurj p q hpq,
        fun x hx => hx, fun x hx => hx⟩
  obtain ⟨p₁, q₁, hc₁, hp₁, hq₁⟩ := arm₁
  obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := arm₂
  obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := arm₃
  have := hind.2 p q p₁ q₁ p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃ hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
  rcases this with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
  · left; exact hp
  · right; exact hq

-- When p ≤ range A and A is injective, comap A p and comap A q are complementary.
lemma comap_isCompl_of_inj_le {k : Type*} [Field k]
    {V₁ V : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V₁] [FiniteDimensional k V]
    (A : V₁ →ₗ[k] V) (hA_inj : Function.Injective A)
    (p q : Submodule k V) (hpq : IsCompl p q) (hle : p ≤ LinearMap.range A) :
    IsCompl (Submodule.comap A p) (Submodule.comap A q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxp hxq
    have : A x ∈ p ⊓ q := ⟨hxp, hxq⟩
    rw [hpq.inf_eq_bot, Submodule.mem_bot] at this
    exact hA_inj (this.trans (map_zero _).symm)
  · rw [codisjoint_iff]; ext x
    simp only [Submodule.mem_sup, Submodule.mem_comap, Submodule.mem_top, iff_true]
    obtain ⟨yp, hyp, yq, hyq, heq⟩ := Submodule.mem_sup.mp
      (show A x ∈ p ⊔ q from hpq.sup_eq_top ▸ Submodule.mem_top)
    have hAx : A x ∈ LinearMap.range A := LinearMap.mem_range.mpr ⟨x, rfl⟩
    have hyp_range : yp ∈ LinearMap.range A := hle hyp
    have hyq_range : yq ∈ LinearMap.range A := by
      have hsub : A x - yp ∈ LinearMap.range A := (LinearMap.range A).sub_mem hAx hyp_range
      rwa [show A x - yp = yq from by rw [← heq]; abel] at hsub
    obtain ⟨x₁, hx₁⟩ := LinearMap.mem_range.mp hyp_range
    obtain ⟨x₂, hx₂⟩ := LinearMap.mem_range.mp hyq_range
    have : x = x₁ + x₂ := hA_inj (by rw [map_add, hx₁, hx₂, heq])
    exact ⟨x₁, show A x₁ ∈ p from hx₁ ▸ hyp,
           x₂, show A x₂ ∈ q from hx₂ ▸ hyq, this.symm⟩

-- Find a complement of p containing S, given Disjoint S p.
-- This is a wrapper around Disjoint.exists_isCompl from Mathlib.
lemma exists_isCompl_containing {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (p S : Submodule k V) (hdisj : Disjoint S p) :
    ∃ q : Submodule k V, IsCompl p q ∧ S ≤ q := by
  obtain ⟨q, hSq, hqp⟩ := hdisj.exists_isCompl
  exact ⟨q, hqp.symm, hSq⟩

lemma build_arm_decomp {k : Type*} [Field k]
    {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (A : W →ₗ[k] V) (hA_inj : Function.Injective A)
    (p q : Submodule k V) (hpq : IsCompl p q)
    (hcond : p ≤ LinearMap.range A ∨ LinearMap.range A ≤ q) :
    ∃ (pW qW : Submodule k W), IsCompl pW qW ∧
      (∀ x ∈ pW, A x ∈ p) ∧ (∀ x ∈ qW, A x ∈ q) := by
  rcases hcond with hle | hle
  · exact ⟨Submodule.comap A p, Submodule.comap A q,
      comap_isCompl_of_inj_le A hA_inj p q hpq hle,
      fun x hx => hx, fun x hx => hx⟩
  · exact ⟨⊥, ⊤, isCompl_bot_top,
      fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
      fun x _ => hle (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩

lemma arm_isCompl_aux {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
    {V' : Type*} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (p q : Submodule k W) (hpq : IsCompl p q)
    (A : V' →ₗ[k] W) (hA_inj : Function.Injective A)
    (R : Submodule k W) (hR_eq : LinearMap.range A = R)
    (hR_split : ∀ x ∈ R, ∃ a ∈ R, ∃ b ∈ R, a ∈ p ∧ b ∈ q ∧ a + b = x) :
    IsCompl (Submodule.comap A p) (Submodule.comap A q) ∧
      (∀ x ∈ Submodule.comap A p, A x ∈ p) ∧
      (∀ x ∈ Submodule.comap A q, A x ∈ q) := by
  refine ⟨⟨?_, ?_⟩, fun x hx => hx, fun x hx => hx⟩
  · rw [Submodule.disjoint_def]
    intro x hxp hxq
    have : A x ∈ p ⊓ q := ⟨hxp, hxq⟩
    rw [hpq.inf_eq_bot, Submodule.mem_bot] at this
    exact hA_inj (this.trans (map_zero _).symm)
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hAx_mem : A x ∈ R := hR_eq ▸ LinearMap.mem_range.mpr ⟨x, rfl⟩
    obtain ⟨a, ha_R, b, hb_R, ha_p, hb_q, hab⟩ := hR_split (A x) hAx_mem
    obtain ⟨a', rfl⟩ := LinearMap.mem_range.mp (hR_eq ▸ ha_R)
    obtain ⟨b', rfl⟩ := LinearMap.mem_range.mp (hR_eq ▸ hb_R)
    have : x = a' + b' := hA_inj (by rw [map_add, hab])
    rw [this]
    exact Submodule.add_mem_sup (Submodule.mem_comap.mpr ha_p) (Submodule.mem_comap.mpr hb_q)

import Mathlib
import EtingofRepresentationTheory.Chapter6.Example6_2_2

/-!
# Example 6.3.1: Indecomposable Representations of D₄

The quiver D₄ (with one central vertex and three arms) has 12 indecomposable
representations for the orientation where three arrows point into the central vertex.

The classification reduces to the **triple of subspaces problem**: classifying
triples of subspaces V₁, V₂, V₃ of a vector space V up to isomorphism.

The 12 indecomposable representations have dimension vectors (center, arm₁, arm₂, arm₃):
- (0,1,0,0), (0,0,1,0), (0,0,0,1): kernel representations at each arm
- (1,0,0,0): simple representation at center
- (1,1,0,0), (1,0,1,0), (1,0,0,1): one arm maps isomorphically to center
- (1,1,1,0), (1,1,0,1), (1,0,1,1): two arms map isomorphically, V₁∩V₂ = 0 type
- (1,1,1,1): all three arms map isomorphically, V₁∩V₂∩V₃ = 0 type
- (2,1,1,1): the "generic" indecomposable (graph of isomorphism)

## Mathlib correspondence

Not in Mathlib. The classification of D₄ representations requires solving the
triple of subspaces problem, which is a classical result in linear algebra.

## Formalization note

We follow Etingof's proof, which proceeds by iteratively splitting off
representations: first kernels of the maps, then the complement of the sum,
then pairwise intersections, then the triple intersection, and finally reducing
to the triple of subspaces problem with conditions (1) V₁+V₂+V₃=V,
(2) pairwise disjoint, (3) each Vᵢ ⊆ sum of other two, which forces dim V = 2n
and produces n copies of the (2,1,1,1) indecomposable.
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
private lemma ker_A₁_or_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
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

private lemma ker_A₂_or_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
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

private lemma ker_A₃_or_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
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
private lemma dim_V₁_eq_one_of_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
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

private lemma dim_V₂_eq_one_of_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
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

private lemma dim_V₃_eq_one_of_rest_zero {k : Type*} [Field k] (ρ : D₄Rep k)
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
private lemma finrank_eq_zero_of_injective_into_zero {k : Type*} [Field k]
    {V₁ V : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V₁ →ₗ[k] V) (hf : LinearMap.ker f = ⊥) (hV : Module.finrank k V = 0) :
    Module.finrank k V₁ = 0 := by
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hf
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

-- Helper: if all arms are zero-dimensional and ρ is indecomposable, then dim V = 1
private lemma dim_V_eq_one_of_arms_zero {k : Type*} [Field k] (ρ : D₄Rep k)
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
private lemma range_sum_eq_top_or_arms_zero {k : Type*} [Field k] (ρ : D₄Rep k)
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
private lemma decomp_of_ranges_split {k : Type*} [Field k] (ρ : D₄Rep k)
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
private lemma comap_isCompl_of_surj_inj {k : Type*} [Field k]
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
private lemma isCompl_of_finrank_one_ne {k : Type*} [Field k]
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
private lemma decomp_general {k : Type*} [Field k] (ρ : D₄Rep k)
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
private lemma comap_isCompl_of_inj_le {k : Type*} [Field k]
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
private lemma exists_isCompl_containing {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (p S : Submodule k V) (hdisj : Disjoint S p) :
    ∃ q : Submodule k V, IsCompl p q ∧ S ≤ q := by
  obtain ⟨q, hSq, hqp⟩ := hdisj.exists_isCompl
  exact ⟨q, hqp.symm, hSq⟩

private lemma build_arm_decomp {k : Type*} [Field k]
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

private lemma arm_isCompl_aux {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
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

-- When all pairwise intersections are trivial and each Rᵢ ≤ Rⱼ ⊔ Rₖ,
-- dim V = 2n with n ≥ 2 and the rep decomposes (graph of isomorphism argument).
private lemma decomp_all_pairwise_compl {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥)
    (hR : LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃ = ⊤)
    (hV : Module.finrank k ρ.V ≥ 3)
    (h₁₂ : LinearMap.range ρ.A₁ ⊓ LinearMap.range ρ.A₂ = ⊥)
    (h₁₃ : LinearMap.range ρ.A₁ ⊓ LinearMap.range ρ.A₃ = ⊥)
    (h₂₃ : LinearMap.range ρ.A₂ ⊓ LinearMap.range ρ.A₃ = ⊥)
    (hR1_le : LinearMap.range ρ.A₁ ≤ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃)
    (hR2_le : LinearMap.range ρ.A₂ ≤ LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₃)
    (hR3_le : LinearMap.range ρ.A₃ ≤ LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂) :
    False := by
  set R₁ := LinearMap.range ρ.A₁
  set R₂ := LinearMap.range ρ.A₂
  set R₃ := LinearMap.range ρ.A₃
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  -- All pairwise IsCompl
  have h12_top : R₁ ⊔ R₂ = ⊤ :=
    eq_top_iff.mpr (hR ▸ sup_le le_rfl (hR3_le.trans le_rfl))
  have hc12 : IsCompl R₁ R₂ := IsCompl.of_eq (disjoint_iff.mp (disjoint_iff.mpr h₁₂)) h12_top
  have h13_top : R₁ ⊔ R₃ = ⊤ := by
    have h1 : R₁ ⊔ R₂ ≤ R₁ ⊔ R₃ := sup_le le_sup_left hR2_le
    exact eq_top_iff.mpr (hR ▸ (sup_le_sup_right h1 _).trans
      (by rw [sup_assoc, sup_idem] : (R₁ ⊔ R₃) ⊔ R₃ ≤ R₁ ⊔ R₃))
  have hc13 : IsCompl R₁ R₃ :=
    IsCompl.of_eq (disjoint_iff.mp (disjoint_iff.mpr h₁₃)) h13_top
  have h23_top : R₂ ⊔ R₃ = ⊤ := by
    have h1 : R₁ ⊔ R₂ ≤ R₂ ⊔ R₃ := sup_le hR1_le le_sup_left
    exact eq_top_iff.mpr (hR ▸ (sup_le_sup_right h1 _).trans
      (by rw [sup_assoc, sup_idem] : (R₂ ⊔ R₃) ⊔ R₃ ≤ R₂ ⊔ R₃))
  have hc23 : IsCompl R₂ R₃ :=
    IsCompl.of_eq (disjoint_iff.mp (disjoint_iff.mpr h₂₃)) h23_top
  -- dim V = 2n, n = dim R₁ = dim R₂ = dim R₃ ≥ 2
  have hdim12 := Submodule.finrank_add_eq_of_isCompl hc12
  have hdim13 := Submodule.finrank_add_eq_of_isCompl hc13
  have hdim23 := Submodule.finrank_add_eq_of_isCompl hc23
  have hfr₁ := LinearMap.finrank_range_of_inj hinj₁
  have hfr₂ := LinearMap.finrank_range_of_inj hinj₂
  have hfr₃ := LinearMap.finrank_range_of_inj hinj₃
  have hn_ge : Module.finrank k ↥R₁ ≥ 2 := by omega
  -- Projections from V = R₁ ⊕ R₂
  let π₁ := Submodule.linearProjOfIsCompl R₁ R₂ hc12
  let π₂ := Submodule.linearProjOfIsCompl R₂ R₁ hc12.symm
  -- Key property: v = R₁.subtype(π₁ v) + R₂.subtype(π₂ v)
  have decomp_v : ∀ v : ρ.V,
      v = R₁.subtype (π₁ v) + R₂.subtype (π₂ v) :=
    fun v => (Submodule.IsCompl.projection_add_projection_eq_self hc12 v).symm
  -- Helper: for v ∈ R₁, π₁(v) = ⟨v, _⟩ and π₂(v) = 0
  have π₁_on_R₁ : ∀ (v : ↥R₁), π₁ (R₁.subtype v) = v :=
    Submodule.linearProjOfIsCompl_apply_left hc12
  have π₂_on_R₁ : ∀ (v : ↥R₁), π₂ (R₁.subtype v) = 0 := fun v => by
    have : R₁.subtype v ∈ LinearMap.ker π₂ := by
      rw [Submodule.linearProjOfIsCompl_ker hc12.symm]; exact v.2
    exact LinearMap.mem_ker.mp this
  -- Helper: for v ∈ R₂, π₁(v) = 0 and π₂(v) = ⟨v, _⟩
  have π₁_on_R₂ : ∀ (v : ↥R₂), π₁ (R₂.subtype v) = 0 := fun v => by
    have : R₂.subtype v ∈ LinearMap.ker π₁ := by
      rw [Submodule.linearProjOfIsCompl_ker hc12]; exact v.2
    exact LinearMap.mem_ker.mp this
  have π₂_on_R₂ : ∀ (v : ↥R₂), π₂ (R₂.subtype v) = v :=
    Submodule.linearProjOfIsCompl_apply_left hc12.symm
  -- π₁ ∘ ι₃ : R₃ → R₁ is injective
  have hπ₁ι₃_inj : Function.Injective (π₁.comp R₃.subtype) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    ext
    have h_diff_R3 : a - b ∈ R₃ := R₃.sub_mem ha hb
    have h_ker : a - b ∈ LinearMap.ker π₁ := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact heq
    rw [Submodule.linearProjOfIsCompl_ker hc12] at h_ker
    have : a - b ∈ R₂ ⊓ R₃ := ⟨h_ker, h_diff_R3⟩
    rw [h₂₃] at this; exact sub_eq_zero.mp ((Submodule.mem_bot k).mp this)
  have hdim_eq3_1 : Module.finrank k ↥R₃ = Module.finrank k ↥R₁ := by omega
  let e₁ : ↥R₃ ≃ₗ[k] ↥R₁ := LinearEquiv.ofInjectiveOfFinrankEq
    (π₁.comp R₃.subtype) hπ₁ι₃_inj hdim_eq3_1
  -- π₂ ∘ ι₃ : R₃ → R₂ is injective
  have hπ₂ι₃_inj : Function.Injective (π₂.comp R₃.subtype) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    ext
    have h_diff_R3 : a - b ∈ R₃ := R₃.sub_mem ha hb
    have h_ker : a - b ∈ LinearMap.ker π₂ := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact heq
    rw [Submodule.linearProjOfIsCompl_ker hc12.symm] at h_ker
    have : a - b ∈ R₁ ⊓ R₃ := ⟨h_ker, h_diff_R3⟩
    rw [h₁₃] at this; exact sub_eq_zero.mp ((Submodule.mem_bot k).mp this)
  have hdim_eq3_2 : Module.finrank k ↥R₃ = Module.finrank k ↥R₂ := by omega
  let e₂ : ↥R₃ ≃ₗ[k] ↥R₂ := LinearEquiv.ofInjectiveOfFinrankEq
    (π₂.comp R₃.subtype) hπ₂ι₃_inj hdim_eq3_2
  -- Graph iso A : R₁ ≃ R₂
  let A_iso : ↥R₁ ≃ₗ[k] ↥R₂ := e₁.symm.trans e₂
  -- Choose proper nonzero W ≤ R₁ (dim R₁ ≥ 2)
  have hR₁_ne : R₁ ≠ ⊥ := by intro h; rw [h, finrank_bot] at hn_ge; omega
  have hR₁_nt : Nontrivial ↥R₁ := by
    obtain ⟨v, hvm, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR₁_ne
    exact ⟨⟨⟨v, hvm⟩, 0, fun h => hv (congr_arg Subtype.val h)⟩⟩
  obtain ⟨w, hw_ne⟩ := exists_ne (0 : ↥R₁)
  let W : Submodule k ↥R₁ := Submodule.span k {w}
  have hW_ne : W ≠ ⊥ := by
    intro h; exact hw_ne (Submodule.span_singleton_eq_bot.mp h)
  obtain ⟨W', hWc⟩ := Submodule.exists_isCompl W
  have hW'_ne : W' ≠ ⊥ := by
    intro h; have := Submodule.finrank_add_eq_of_isCompl hWc
    rw [h, finrank_bot, add_zero, finrank_span_singleton hw_ne] at this; omega
  -- AW = A(W), AW' = A(W')
  let AW : Submodule k ↥R₂ := Submodule.map A_iso.toLinearMap W
  let AW' : Submodule k ↥R₂ := Submodule.map A_iso.toLinearMap W'
  have hAW_isCompl : IsCompl AW AW' := by
    constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro x ⟨hx1, hx2⟩
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx1
      obtain ⟨b, hb, heq⟩ := Submodule.mem_map.mp hx2
      have hab : a = b := A_iso.injective (by exact_mod_cast heq.symm)
      subst hab
      have : a ∈ W ⊓ W' := ⟨ha, hb⟩
      rw [hWc.inf_eq_bot, Submodule.mem_bot] at this
      simp [this]
    · rw [codisjoint_iff, ← Submodule.map_sup, hWc.sup_eq_top,
        Submodule.map_top, LinearMap.range_eq_top.mpr A_iso.surjective]
  -- Membership helpers for p and q
  have mem_p_of : ∀ v : ρ.V, π₁ v ∈ W → π₂ v ∈ AW → v ∈
      (Submodule.comap π₁ W ⊓ Submodule.comap π₂ AW : Submodule k ρ.V) :=
    fun v h1 h2 => ⟨Submodule.mem_comap.mpr h1, Submodule.mem_comap.mpr h2⟩
  have mem_q_of : ∀ v : ρ.V, π₁ v ∈ W' → π₂ v ∈ AW' → v ∈
      (Submodule.comap π₁ W' ⊓ Submodule.comap π₂ AW' : Submodule k ρ.V) :=
    fun v h1 h2 => ⟨Submodule.mem_comap.mpr h1, Submodule.mem_comap.mpr h2⟩
  -- Central decomposition: p, q defined by projections
  let p := Submodule.comap π₁ W ⊓ Submodule.comap π₂ AW
  let q := Submodule.comap π₁ W' ⊓ Submodule.comap π₂ AW'
  -- p ≠ ⊥: R₁.subtype w ∈ p
  have hp_ne : p ≠ ⊥ := by
    intro h
    have : R₁.subtype w ∈ p :=
      mem_p_of _ (by rw [π₁_on_R₁]; exact Submodule.mem_span_singleton_self w)
        (by rw [π₂_on_R₁]; exact AW.zero_mem)
    rw [h] at this
    exact hw_ne (by ext; exact (Submodule.mem_bot k).mp this)
  -- q ≠ ⊥
  have hq_ne : q ≠ ⊥ := by
    intro h
    obtain ⟨w', hw'_mem, hw'_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'_ne
    have : R₁.subtype w' ∈ q :=
      mem_q_of _ (by rw [π₁_on_R₁]; exact hw'_mem) (by rw [π₂_on_R₁]; exact AW'.zero_mem)
    rw [h] at this
    exact hw'_ne (by ext; exact (Submodule.mem_bot k).mp this)
  -- IsCompl p q
  have hpq : IsCompl p q := by
    constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro v hv
      -- v ∈ p ⊓ q means v ∈ p and v ∈ q
      -- p = comap π₁ W ⊓ comap π₂ AW, q = comap π₁ W' ⊓ comap π₂ AW'
      have hvp := (Submodule.mem_inf.mp hv).1
      have hvq := (Submodule.mem_inf.mp hv).2
      have hv1 : π₁ v ∈ W := (Submodule.mem_inf.mp hvp).1
      have hv2 : π₂ v ∈ AW := (Submodule.mem_inf.mp hvp).2
      have hv3 : π₁ v ∈ W' := (Submodule.mem_inf.mp hvq).1
      have hv4 : π₂ v ∈ AW' := (Submodule.mem_inf.mp hvq).2
      have h1 : π₁ v ∈ W ⊓ W' := ⟨hv1, hv3⟩
      rw [hWc.inf_eq_bot, Submodule.mem_bot] at h1
      have h2 : π₂ v ∈ AW ⊓ AW' := ⟨hv2, hv4⟩
      rw [hAW_isCompl.inf_eq_bot, Submodule.mem_bot] at h2
      have := decomp_v v
      rw [h1, h2, map_zero, map_zero, add_zero] at this
      exact this
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro v
      obtain ⟨w₁, hw₁, w₁', hw₁', hww⟩ := Submodule.mem_sup.mp
        (show π₁ v ∈ W ⊔ W' from hWc.sup_eq_top ▸ Submodule.mem_top)
      obtain ⟨a₁, ha₁, a₁', ha₁', haa⟩ := Submodule.mem_sup.mp
        (show π₂ v ∈ AW ⊔ AW' from hAW_isCompl.sup_eq_top ▸ Submodule.mem_top)
      have hvp : R₁.subtype w₁ + R₂.subtype a₁ ∈ p :=
        mem_p_of _ (by rw [map_add, π₁_on_R₁, π₁_on_R₂, add_zero]; exact hw₁)
          (by rw [map_add, π₂_on_R₁, π₂_on_R₂, zero_add]; exact ha₁)
      have hvq : R₁.subtype w₁' + R₂.subtype a₁' ∈ q :=
        mem_q_of _ (by rw [map_add, π₁_on_R₁, π₁_on_R₂, add_zero]; exact hw₁')
          (by rw [map_add, π₂_on_R₁, π₂_on_R₂, zero_add]; exact ha₁')
      have hsum : R₁.subtype w₁ + R₂.subtype a₁ +
          (R₁.subtype w₁' + R₂.subtype a₁') = v := by
        rw [decomp_v v, ← hww, ← haa, map_add, map_add]; abel
      exact Submodule.mem_sup.mpr ⟨_, hvp, _, hvq, hsum⟩
  -- Helper: construct arm decomposition via range splitting
  -- arm_isCompl is now a top-level lemma (arm_isCompl_aux) for universe polymorphism
  -- Range splitting helper for R₁/R₂ submodules
  have range_split_R₁ : ∀ x ∈ R₁, ∃ a ∈ R₁, ∃ b ∈ R₁,
      a ∈ p ∧ b ∈ q ∧ a + b = x := by
    intro x hx
    obtain ⟨w₁, hw₁, w₁', hw₁', hww⟩ := Submodule.mem_sup.mp
      (show (⟨x, hx⟩ : ↥R₁) ∈ W ⊔ W' from hWc.sup_eq_top ▸ Submodule.mem_top)
    refine ⟨R₁.subtype w₁, w₁.2, R₁.subtype w₁', w₁'.2,
      mem_p_of _ (by rw [π₁_on_R₁]; exact hw₁) (by rw [π₂_on_R₁]; exact AW.zero_mem),
      mem_q_of _ (by rw [π₁_on_R₁]; exact hw₁') (by rw [π₂_on_R₁]; exact AW'.zero_mem), ?_⟩
    have heq : (⟨x, hx⟩ : ↥R₁) = w₁ + w₁' := by
      ext; simpa using (congr_arg Subtype.val hww).symm
    calc R₁.subtype w₁ + R₁.subtype w₁' = R₁.subtype (w₁ + w₁') := (map_add _ _ _).symm
      _ = R₁.subtype ⟨x, hx⟩ := by rw [← heq]
      _ = x := rfl
  have range_split_R₂ : ∀ x ∈ R₂, ∃ a ∈ R₂, ∃ b ∈ R₂,
      a ∈ p ∧ b ∈ q ∧ a + b = x := by
    intro x hx
    obtain ⟨a₁, ha₁, a₁', ha₁', haa⟩ := Submodule.mem_sup.mp
      (show (⟨x, hx⟩ : ↥R₂) ∈ AW ⊔ AW' from hAW_isCompl.sup_eq_top ▸ Submodule.mem_top)
    refine ⟨R₂.subtype a₁, a₁.2, R₂.subtype a₁', a₁'.2,
      mem_p_of _ (by rw [π₁_on_R₂]; exact W.zero_mem) (by rw [π₂_on_R₂]; exact ha₁),
      mem_q_of _ (by rw [π₁_on_R₂]; exact W'.zero_mem) (by rw [π₂_on_R₂]; exact ha₁'), ?_⟩
    have heq : (⟨x, hx⟩ : ↥R₂) = a₁ + a₁' := by
      ext; simpa using (congr_arg Subtype.val haa).symm
    calc R₂.subtype a₁ + R₂.subtype a₁' = R₂.subtype (a₁ + a₁') := (map_add _ _ _).symm
      _ = R₂.subtype ⟨x, hx⟩ := by rw [← heq]
      _ = x := rfl
  -- Range splitting for R₃: v ∈ p iff π₁(v) ∈ W (since π₂ = A_iso ∘ π₁ on R₃)
  have range_split_R₃ : ∀ x ∈ R₃, ∃ a ∈ R₃, ∃ b ∈ R₃,
      a ∈ p ∧ b ∈ q ∧ a + b = x := by
    intro x hx
    obtain ⟨w₁, hw₁, w₁', hw₁', hww⟩ := Submodule.mem_sup.mp
      (show π₁ x ∈ W ⊔ W' from hWc.sup_eq_top ▸ Submodule.mem_top)
    let v₁ := e₁.symm w₁
    let v₁' := e₁.symm w₁'
    -- e₁ maps v₁ to w₁
    have he₁_v₁ : (π₁.comp R₃.subtype) v₁ = w₁ := by
      change (π₁.comp R₃.subtype) (e₁.symm w₁) = w₁
      simp [e₁, LinearEquiv.ofInjectiveOfFinrankEq]
    have he₁_v₁' : (π₁.comp R₃.subtype) v₁' = w₁' := by
      change (π₁.comp R₃.subtype) (e₁.symm w₁') = w₁'
      simp [e₁, LinearEquiv.ofInjectiveOfFinrankEq]
    -- π₂(ι₃(v₁)) = A_iso(w₁) (since A_iso = e₁⁻¹ ∘ e₂, e₂ = π₂ ∘ ι₃)
    have hπ₂_v₁ : π₂ (R₃.subtype v₁) = A_iso w₁ := by
      change (π₂.comp R₃.subtype) (e₁.symm w₁) =
        (e₁.symm.trans e₂) w₁
      simp [e₁, e₂, LinearEquiv.ofInjectiveOfFinrankEq, LinearEquiv.trans_apply]
    have hπ₂_v₁' : π₂ (R₃.subtype v₁') = A_iso w₁' := by
      change (π₂.comp R₃.subtype) (e₁.symm w₁') =
        (e₁.symm.trans e₂) w₁'
      simp [e₁, e₂, LinearEquiv.ofInjectiveOfFinrankEq, LinearEquiv.trans_apply]
    have hv₁_p : (v₁ : ρ.V) ∈ p :=
      mem_p_of _ (by change (π₁.comp R₃.subtype) v₁ ∈ W; rw [he₁_v₁]; exact hw₁)
        (by change π₂ (R₃.subtype v₁) ∈ AW; rw [hπ₂_v₁]; exact Submodule.mem_map_of_mem hw₁)
    have hv₁'_q : (v₁' : ρ.V) ∈ q :=
      mem_q_of _ (by change (π₁.comp R₃.subtype) v₁' ∈ W'; rw [he₁_v₁']; exact hw₁')
        (by change π₂ (R₃.subtype v₁') ∈ AW'; rw [hπ₂_v₁']; exact Submodule.mem_map_of_mem hw₁')
    have hsum : (v₁ : ρ.V) + (v₁' : ρ.V) = x := by
      have key : v₁ + v₁' = (⟨x, hx⟩ : ↥R₃) := by
        apply hπ₁ι₃_inj
        show (π₁.comp R₃.subtype) (v₁ + v₁') = (π₁.comp R₃.subtype) ⟨x, hx⟩
        rw [map_add, he₁_v₁, he₁_v₁']
        ext; simpa using congr_arg Subtype.val hww
      exact congr_arg Subtype.val key
    exact ⟨v₁, v₁.2, v₁', v₁'.2, hv₁_p, hv₁'_q, hsum⟩
  -- Build arm decompositions
  obtain ⟨hc₁, hp₁, hq₁⟩ := arm_isCompl_aux p q hpq ρ.A₁ hinj₁ R₁ rfl range_split_R₁
  obtain ⟨hc₂, hp₂, hq₂⟩ := arm_isCompl_aux p q hpq ρ.A₂ hinj₂ R₂ rfl range_split_R₂
  obtain ⟨hc₃, hp₃, hq₃⟩ := arm_isCompl_aux p q hpq ρ.A₃ hinj₃ R₃ rfl range_split_R₃
  -- Apply indecomposability to get contradiction
  rcases hind.2 p q _ _ _ _ _ _ hpq hc₁ hc₂ hc₃ hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
    with ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩
  · exact hp_ne h
  · exact hq_ne h

-- dim V ≥ 3, all injective, range sum = ⊤ → contradicts indecomposability
private lemma decomp_dim_ge_three {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥)
    (hR : LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃ = ⊤)
    (hV : Module.finrank k ρ.V ≥ 3) : False := by
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  haveI : Nontrivial ρ.V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  -- Helper: given nontrivial IsCompl p q with each arm either p ≤ Rᵢ or Rᵢ ≤ q,
  -- derive False from indecomposability.
  have mk_absurd : ∀ (p q : Submodule k ρ.V), IsCompl p q →
      p ≠ ⊥ → q ≠ ⊥ →
      (p ≤ LinearMap.range ρ.A₁ ∨ LinearMap.range ρ.A₁ ≤ q) →
      (p ≤ LinearMap.range ρ.A₂ ∨ LinearMap.range ρ.A₂ ≤ q) →
      (p ≤ LinearMap.range ρ.A₃ ∨ LinearMap.range ρ.A₃ ≤ q) →
      False := by
    intro p q hpq hp_ne hq_ne h1 h2 h3
    obtain ⟨p₁, q₁, hc₁, hp₁, hq₁⟩ := build_arm_decomp ρ.A₁ hinj₁ p q hpq h1
    obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := build_arm_decomp ρ.A₂ hinj₂ p q hpq h2
    obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := build_arm_decomp ρ.A₃ hinj₃ p q hpq h3
    rcases hind.2 p q p₁ q₁ p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃ hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
      with ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩
    · exact hp_ne h
    · exact hq_ne h
  -- Helper: use a 1-dim span to derive contradiction via mk_absurd.
  have span_absurd : ∀ (w : ρ.V) (_ : w ≠ 0) (q : Submodule k ρ.V)
      (hpq : IsCompl (Submodule.span k {w}) q),
      (Submodule.span k {w} ≤ LinearMap.range ρ.A₁ ∨ LinearMap.range ρ.A₁ ≤ q) →
      (Submodule.span k {w} ≤ LinearMap.range ρ.A₂ ∨ LinearMap.range ρ.A₂ ≤ q) →
      (Submodule.span k {w} ≤ LinearMap.range ρ.A₃ ∨ LinearMap.range ρ.A₃ ≤ q) →
      False := by
    intro w hw q hpq h1 h2 h3
    have hp_dim := finrank_span_singleton (K := k) hw
    have hp_ne : Submodule.span k {w} ≠ ⊥ := by
      intro h; exact hw (Submodule.span_singleton_eq_bot.mp h)
    have hq_ne : q ≠ ⊥ := by
      intro h; have := Submodule.finrank_add_eq_of_isCompl hpq
      rw [h, finrank_bot, add_zero, hp_dim] at this; omega
    exact mk_absurd _ q hpq hp_ne hq_ne h1 h2 h3
  -- Abbreviations for readability (used in comments only; proofs use full names)
  set R₁ := LinearMap.range ρ.A₁
  set R₂ := LinearMap.range ρ.A₂
  set R₃ := LinearMap.range ρ.A₃
  -- Case 1: R₁ ⊓ R₂ ⊓ R₃ ≠ ⊥
  by_cases h_triple : R₁ ⊓ R₂ ⊓ R₃ ≠ ⊥
  · obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_triple
    rw [Submodule.mem_inf, Submodule.mem_inf] at hw_mem
    obtain ⟨q, hpq⟩ := Submodule.exists_isCompl (Submodule.span k {w})
    exact span_absurd w hw_ne q hpq
      (Or.inl (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1.1)))
      (Or.inl (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1.2)))
      (Or.inl (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.2)))
  · push_neg at h_triple
    -- Case 2: Some Rᵢ ⊓ Rⱼ ≠ ⊥ (with triple intersection = ⊥)
    by_cases h₁₂ : R₁ ⊓ R₂ ≠ ⊥
    · obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁₂
      rw [Submodule.mem_inf] at hw_mem
      have hp1 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1)
      have hp2 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.2)
      have hdisj : Disjoint R₃ (Submodule.span k {w}) := by
        rw [disjoint_comm, disjoint_iff]
        exact le_bot_iff.mp (le_trans (inf_le_inf_right R₃ (le_inf hp1 hp2)) h_triple.le)
      obtain ⟨q, hpq, h3q⟩ := exists_isCompl_containing _ R₃ hdisj
      exact span_absurd w hw_ne q hpq (Or.inl hp1) (Or.inl hp2) (Or.inr h3q)
    · push_neg at h₁₂
      by_cases h₁₃ : R₁ ⊓ R₃ ≠ ⊥
      · obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁₃
        rw [Submodule.mem_inf] at hw_mem
        have hp1 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1)
        have hp3 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.2)
        have h132 : R₁ ⊓ R₃ ⊓ R₂ = ⊥ := by
          convert h_triple using 1; ac_rfl
        have hdisj : Disjoint R₂ (Submodule.span k {w}) := by
          rw [disjoint_comm, disjoint_iff]
          exact le_bot_iff.mp (le_trans (inf_le_inf_right R₂ (le_inf hp1 hp3)) h132.le)
        obtain ⟨q, hpq, h2q⟩ := exists_isCompl_containing _ R₂ hdisj
        exact span_absurd w hw_ne q hpq (Or.inl hp1) (Or.inr h2q) (Or.inl hp3)
      · push_neg at h₁₃
        by_cases h₂₃ : R₂ ⊓ R₃ ≠ ⊥
        · obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂₃
          rw [Submodule.mem_inf] at hw_mem
          have hp2 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1)
          have hp3 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.2)
          have h231 : R₂ ⊓ R₃ ⊓ R₁ = ⊥ := by
            convert h_triple using 1; ac_rfl
          have hdisj : Disjoint R₁ (Submodule.span k {w}) := by
            rw [disjoint_comm, disjoint_iff]
            exact le_bot_iff.mp (le_trans (inf_le_inf_right R₁ (le_inf hp2 hp3)) h231.le)
          obtain ⟨q, hpq, h1q⟩ := exists_isCompl_containing _ R₁ hdisj
          exact span_absurd w hw_ne q hpq (Or.inr h1q) (Or.inl hp2) (Or.inl hp3)
        · push_neg at h₂₃
          -- Case 3: All pairwise = ⊥. Try one-vs-two splits.
          -- Helper: given Disjoint Rᵢ (Rⱼ ⊔ Rₖ) with Rᵢ ⊔ Rⱼ ⊔ Rₖ = ⊤,
          -- derive False by finding nontrivial IsCompl.
          have case3 : ∀ {Ra Rb Rc : Submodule k ρ.V},
              Disjoint Ra (Rb ⊔ Rc) → Ra ⊔ (Rb ⊔ Rc) = ⊤ →
              Rb ⊓ Rc = ⊥ →
              (∀ p q : Submodule k ρ.V, IsCompl p q → p ≠ ⊥ → q ≠ ⊥ →
                (p ≤ Ra ∨ Ra ≤ q) → (p ≤ Rb ∨ Rb ≤ q) →
                (p ≤ Rc ∨ Rc ≤ q) → False) →
              False := by
            intro Ra Rb Rc hdisj hcod hjk absurd_fn
            have hpq : IsCompl Ra (Rb ⊔ Rc) := ⟨hdisj, codisjoint_iff.mpr hcod⟩
            by_cases haz : Ra = ⊥
            · -- Ra = ⊥, Rb ⊔ Rc = ⊤
              have htop : Rb ⊔ Rc = ⊤ := by rwa [haz, bot_sup_eq] at hcod
              by_cases hbz : Rb = ⊥
              · -- Rb = ⊥, Rc = ⊤
                have hctop : Rc = ⊤ := by rwa [hbz, bot_sup_eq] at htop
                obtain ⟨v, hv⟩ := exists_ne (0 : ρ.V)
                obtain ⟨q, hpq'⟩ := Submodule.exists_isCompl (Submodule.span k {v})
                have hp_ne : Submodule.span k {v} ≠ ⊥ := by
                  intro h; exact hv (Submodule.span_singleton_eq_bot.mp h)
                have hq_ne : q ≠ ⊥ := by
                  intro h; have := Submodule.finrank_add_eq_of_isCompl hpq'
                  rw [h, finrank_bot, add_zero, finrank_span_singleton hv] at this; omega
                exact absurd_fn _ q hpq' hp_ne hq_ne
                  (Or.inr (haz ▸ bot_le)) (Or.inr (hbz ▸ bot_le))
                  (Or.inl (hctop ▸ le_top))
              · by_cases hcz : Rc = ⊥
                · -- Rc = ⊥, Rb = ⊤
                  have hbtop : Rb = ⊤ := by rwa [hcz, sup_bot_eq] at htop
                  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.V)
                  obtain ⟨q, hpq'⟩ := Submodule.exists_isCompl (Submodule.span k {v})
                  have hp_ne : Submodule.span k {v} ≠ ⊥ := by
                    intro h; exact hv (Submodule.span_singleton_eq_bot.mp h)
                  have hq_ne : q ≠ ⊥ := by
                    intro h; have := Submodule.finrank_add_eq_of_isCompl hpq'
                    rw [h, finrank_bot, add_zero, finrank_span_singleton hv] at this; omega
                  exact absurd_fn _ q hpq' hp_ne hq_ne
                    (Or.inr (haz ▸ bot_le)) (Or.inl (hbtop ▸ le_top))
                    (Or.inr (hcz ▸ bot_le))
                · -- Both Rb, Rc nontrivial. IsCompl Rb Rc.
                  have hbc : IsCompl Rb Rc :=
                    ⟨disjoint_iff.mpr hjk, codisjoint_iff.mpr htop⟩
                  exact absurd_fn Rb Rc hbc hbz hcz
                    (Or.inr (haz ▸ bot_le)) (Or.inl le_rfl) (Or.inr le_rfl)
            · -- Ra ≠ ⊥
              by_cases hqz : Rb ⊔ Rc = ⊥
              · -- Rb = Rc = ⊥, Ra = ⊤
                have hbz : Rb = ⊥ := le_bot_iff.mp (by rw [← hqz]; exact le_sup_left)
                have hcz : Rc = ⊥ := le_bot_iff.mp (by rw [← hqz]; exact le_sup_right)
                have hatop : Ra = ⊤ := by rwa [hqz, sup_bot_eq] at hcod
                obtain ⟨v, hv⟩ := exists_ne (0 : ρ.V)
                obtain ⟨q, hpq'⟩ := Submodule.exists_isCompl (Submodule.span k {v})
                have hp_ne : Submodule.span k {v} ≠ ⊥ := by
                  intro h; exact hv (Submodule.span_singleton_eq_bot.mp h)
                have hq_ne : q ≠ ⊥ := by
                  intro h; have := Submodule.finrank_add_eq_of_isCompl hpq'
                  rw [h, finrank_bot, add_zero, finrank_span_singleton hv] at this; omega
                exact absurd_fn _ q hpq' hp_ne hq_ne
                  (Or.inl (hatop ▸ le_top)) (Or.inr (hbz ▸ bot_le))
                  (Or.inr (hcz ▸ bot_le))
              · exact absurd_fn Ra (Rb ⊔ Rc) hpq haz hqz
                  (Or.inl le_rfl) (Or.inr le_sup_left) (Or.inr le_sup_right)
          by_cases hR₁_23 : Disjoint R₁ (R₂ ⊔ R₃)
          · have : R₁ ⊔ (R₂ ⊔ R₃) = ⊤ := by rw [← sup_assoc]; exact hR
            exact case3 hR₁_23 this h₂₃ mk_absurd
          · by_cases hR₂_13 : Disjoint R₂ (R₁ ⊔ R₃)
            · have : R₂ ⊔ (R₁ ⊔ R₃) = ⊤ := by
                have := hR; rw [show R₁ ⊔ R₂ ⊔ R₃ = R₂ ⊔ (R₁ ⊔ R₃) from by
                  simp only [sup_comm, sup_left_comm]] at this; exact this
              exact case3 hR₂_13 this h₁₃
                (fun p q hpq hp hq ha hb hc => mk_absurd p q hpq hp hq hb ha hc)
            · by_cases hR₃_12 : Disjoint R₃ (R₁ ⊔ R₂)
              · have : R₃ ⊔ (R₁ ⊔ R₂) = ⊤ := by
                  have := hR; rw [show R₁ ⊔ R₂ ⊔ R₃ = R₃ ⊔ (R₁ ⊔ R₂) from by
                    simp only [sup_comm, sup_left_comm]] at this; exact this
                exact case3 hR₃_12 this h₁₂
                  (fun p q hpq hp hq ha hb hc => mk_absurd p q hpq hp hq hb hc ha)
              · -- All Rᵢ ⊓ (Rⱼ ⊔ Rₖ) ≠ ⊥, all pairwise = ⊥.
                -- Split: some Rᵢ ⊄ Rⱼ ⊔ Rₖ (use span_absurd) vs all contained.
                -- Helper: if Rᵢ ⊄ Rⱼ ⊔ Rₖ, find w ∈ Rᵢ \ (Rⱼ ⊔ Rₖ) and use span_absurd
                have not_le_absurd :
                    ∀ (Ra Rb Rc : Submodule k ρ.V),
                      ¬ Ra ≤ Rb ⊔ Rc →
                      (∀ (w : ρ.V), w ≠ 0 → ∀ (q : Submodule k ρ.V),
                        IsCompl (Submodule.span k {w}) q →
                        (Submodule.span k {w} ≤ Ra ∨ Ra ≤ q) →
                        (Submodule.span k {w} ≤ Rb ∨ Rb ≤ q) →
                        (Submodule.span k {w} ≤ Rc ∨ Rc ≤ q) →
                        False) →
                      False := by
                  intro Ra Rb Rc hle absurd_fn
                  have ⟨w, hw_in, hw_not⟩ : ∃ w, w ∈ Ra ∧ w ∉ (Rb ⊔ Rc : Submodule k ρ.V) := by
                    by_contra h; push_neg at h; exact hle h
                  have hw_ne : w ≠ 0 := fun h => hw_not (h ▸ (Rb ⊔ Rc).zero_mem)
                  have hdisj : Disjoint (Rb ⊔ Rc) (Submodule.span k {w}) :=
                    (Submodule.disjoint_span_singleton' hw_ne).mpr hw_not
                  obtain ⟨q, hpq, hle'⟩ := exists_isCompl_containing _ (Rb ⊔ Rc) hdisj
                  exact absurd_fn w hw_ne q hpq
                    (Or.inl (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_in)))
                    (Or.inr (le_sup_left.trans hle'))
                    (Or.inr (le_sup_right.trans hle'))
                by_cases hR1_le : R₁ ≤ R₂ ⊔ R₃
                · by_cases hR2_le : R₂ ≤ R₁ ⊔ R₃
                  · by_cases hR3_le : R₃ ≤ R₁ ⊔ R₂
                    · -- SUBCASE B: all Rᵢ ≤ Rⱼ ⊔ Rₖ
                      -- This gives IsCompl for all pairs, dim V = 2n, n ≥ 2.
                      -- The representation decomposes (graph of iso argument).
                      exact decomp_all_pairwise_compl ρ hind hA₁ hA₂ hA₃ hR hV
                        h₁₂ h₁₃ h₂₃ hR1_le hR2_le hR3_le
                    · exact not_le_absurd R₃ R₁ R₂ hR3_le
                        (fun w hw q hpq h3 h1 h2 => span_absurd w hw q hpq h1 h2 h3)
                  · exact not_le_absurd R₂ R₁ R₃ hR2_le
                      (fun w hw q hpq h2 h1 h3 => span_absurd w hw q hpq h1 h2 h3)
                · exact not_le_absurd R₁ R₂ R₃ hR1_le
                    (fun w hw q hpq h1 h2 h3 => span_absurd w hw q hpq h1 h2 h3)

-- Helper: if A₁ is bijective in a D₄ rep and p ⊕ q = V with other ranges split,
-- then p = ⊥ or q = ⊥.
private lemma decomp_bijective_and_split {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁_inj : Function.Injective ρ.A₁)
    (hA₁_surj : LinearMap.range ρ.A₁ = ⊤)
    (p q : Submodule k ρ.V) (hpq : IsCompl p q)
    (h₂ : LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q)
    (h₃ : LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) :
    p = ⊥ ∨ q = ⊥ := by
  have hc₁ := comap_isCompl_of_surj_inj ρ.A₁ hA₁_inj hA₁_surj p q hpq
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
  obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := arm₂
  obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := arm₃
  have := hind.2 p q (Submodule.comap ρ.A₁ p) (Submodule.comap ρ.A₁ q)
    p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃
    (fun x hx => hx) (fun x hx => hx)
    hp₂ hq₂ hp₃ hq₃
  rcases this with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
  · left; exact hp
  · right; exact hq

-- Helper: if dim V ≥ 2, all injective, range sum = ⊤, indecomposable,
-- then dim V = 2 and all dim Vᵢ = 1.
private lemma classification_injective_dim_bound {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥)
    (hR : LinearMap.range ρ.A₁ ⊔ LinearMap.range ρ.A₂ ⊔ LinearMap.range ρ.A₃ = ⊤)
    (hV : Module.finrank k ρ.V ≥ 2) :
    Module.finrank k ρ.V = 2 ∧ Module.finrank k ρ.V₁ = 1 ∧
    Module.finrank k ρ.V₂ = 1 ∧ Module.finrank k ρ.V₃ = 1 := by
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  have hle₁ := LinearMap.finrank_le_finrank_of_injective hinj₁
  have hle₂ := LinearMap.finrank_le_finrank_of_injective hinj₂
  have hle₃ := LinearMap.finrank_le_finrank_of_injective hinj₃
  -- dim V ≤ 2 (dim V ≥ 3 is impossible for indecomposable reps)
  have hV_le : Module.finrank k ρ.V ≤ 2 := by
    by_contra h; push_neg at h
    exact decomp_dim_ge_three ρ hind hA₁ hA₂ hA₃ hR (by omega)
  have hV_eq : Module.finrank k ρ.V = 2 := by omega
  -- Arm-specific range = ⊤ / range = ⊥ lemmas
  have rt₁ : Module.finrank k ρ.V₁ = 2 → LinearMap.range ρ.A₁ = ⊤ :=
    fun h => (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank (by omega)).mp hA₁
  have rt₂ : Module.finrank k ρ.V₂ = 2 → LinearMap.range ρ.A₂ = ⊤ :=
    fun h => (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank (by omega)).mp hA₂
  have rt₃ : Module.finrank k ρ.V₃ = 2 → LinearMap.range ρ.A₃ = ⊤ :=
    fun h => (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank (by omega)).mp hA₃
  -- Helper: finrank of range (by injectivity)
  have fr₁ := LinearMap.finrank_range_of_inj hinj₁
  have fr₂ := LinearMap.finrank_range_of_inj hinj₂
  have fr₃ := LinearMap.finrank_range_of_inj hinj₃
  have rb₁ : Module.finrank k ρ.V₁ = 0 → LinearMap.range ρ.A₁ = ⊥ :=
    fun h => Submodule.finrank_eq_zero.mp (by rw [fr₁]; exact h)
  have rb₂ : Module.finrank k ρ.V₂ = 0 → LinearMap.range ρ.A₂ = ⊥ :=
    fun h => Submodule.finrank_eq_zero.mp (by rw [fr₂]; exact h)
  have rb₃ : Module.finrank k ρ.V₃ = 0 → LinearMap.range ρ.A₃ = ⊥ :=
    fun h => Submodule.finrank_eq_zero.mp (by rw [fr₃]; exact h)
  haveI : Nontrivial ρ.V := Module.nontrivial_of_finrank_eq_succ (n := 1) (by omega)
  -- Contradiction helper: given 1-dim p, q, decomp_general gives False
  have absurd_pq : ∀ (p q : Submodule k ρ.V), IsCompl p q →
      Module.finrank k p = 1 → Module.finrank k q = 1 →
      (LinearMap.range ρ.A₁ ≤ p ∨ LinearMap.range ρ.A₁ ≤ q) ∨
        (Function.Injective ρ.A₁ ∧ LinearMap.range ρ.A₁ = ⊤) →
      (LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q) ∨
        (Function.Injective ρ.A₂ ∧ LinearMap.range ρ.A₂ = ⊤) →
      (LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) ∨
        (Function.Injective ρ.A₃ ∧ LinearMap.range ρ.A₃ = ⊤) →
      False := by
    intro p q hpq hp hq h₁ h₂ h₃
    rcases decomp_general ρ hind p q hpq h₁ h₂ h₃ with hp_bot | hq_bot
    · rw [hp_bot, finrank_bot] at hp; omega
    · rw [hq_bot, finrank_bot] at hq; omega
  -- Prove all dims = 1. Strategy: for each arm with dim ≠ 1, find nontrivial
  -- complement pair accommodating all arm ranges, get contradiction via absurd_pq.
  refine ⟨hV_eq, ?_, ?_, ?_⟩
  all_goals by_contra hdim
  -- For dim V₁ = 1:
  · have hd₁ : Module.finrank k ρ.V₁ = 0 ∨ Module.finrank k ρ.V₁ = 2 := by omega
    -- Arm 1 has range ⊥ (dim 0) or is bijective (dim 2).
    -- Collect "constraining" ranges from arms 2, 3 (those with dim = 1).
    -- At most 2 such ranges. We can accommodate them in a complement pair.
    -- First, get a 1-dim subspace p in V.
    -- Choose p to contain a constraining range if one exists.
    have get_line : ∃ (p : Submodule k ρ.V), Module.finrank k p = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : ρ.V)
      exact ⟨Submodule.span k {v}, finrank_span_singleton hv⟩
    -- Build arm conditions for decomp_general based on arm dimensions
    have h₁_cond : ∀ (p q : Submodule k ρ.V), IsCompl p q →
        (LinearMap.range ρ.A₁ ≤ p ∨ LinearMap.range ρ.A₁ ≤ q) ∨
        (Function.Injective ρ.A₁ ∧ LinearMap.range ρ.A₁ = ⊤) := by
      intro p q _
      rcases hd₁ with h | h
      · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
      · exact Or.inr ⟨hinj₁, rt₁ h⟩
    -- For arms 2 and 3: if dim = 0 or 2, easy. If dim = 1, need range ≤ p or ≤ q.
    -- The 1-dim ranges are the "constraints" on our choice of p.
    -- Strategy: if a 1-dim range exists, make it = p (or q).
    -- We pick p = the first 1-dim range we find among arms 2, 3.
    -- If both are 1-dim and different, use isCompl_of_finrank_one_ne to make them (p, q).
    -- dim_range_i = finrank of range Aᵢ (= dim Vᵢ by injectivity)
    by_cases hd₂ : Module.finrank k ρ.V₂ = 1
    · -- range A₂ is a 1-dim line. Use it as p.
      set p := LinearMap.range ρ.A₂
      have hp : Module.finrank k p = 1 := by rw [fr₂, hd₂]
      by_cases hd₃ : Module.finrank k ρ.V₃ = 1
      · -- range A₃ is also 1-dim.
        by_cases heq : p = LinearMap.range ρ.A₃
        · -- Same line. Both ≤ p. Pick any complement q.
          obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
          have hq : Module.finrank k q = 1 := by
            have := Submodule.finrank_add_eq_of_isCompl hpq; omega
          exact absurd_pq p q hpq hp hq (h₁_cond p q hpq)
            (Or.inl (Or.inl le_rfl))
            (Or.inl (Or.inl (heq ▸ le_rfl)))
        · -- Different lines. IsCompl. Use p = range A₂, q = range A₃.
          have hq : Module.finrank k (LinearMap.range ρ.A₃) = 1 := by rw [fr₃, hd₃]
          have hpq := isCompl_of_finrank_one_ne hV_eq p (LinearMap.range ρ.A₃) hp hq heq
          exact absurd_pq p (LinearMap.range ρ.A₃) hpq hp hq (h₁_cond p _ hpq)
            (Or.inl (Or.inl le_rfl))
            (Or.inl (Or.inr le_rfl))
      · -- dim V₃ ≠ 1, so dim V₃ = 0 or 2. range A₃ fits easily.
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₃_cond : (LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) ∨
            (Function.Injective ρ.A₃ ∧ LinearMap.range ρ.A₃ = ⊤) := by
          have : Module.finrank k ρ.V₃ = 0 ∨ Module.finrank k ρ.V₃ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₃, rt₃ h⟩
        exact absurd_pq p q hpq hp hq (h₁_cond p q hpq)
          (Or.inl (Or.inl le_rfl)) h₃_cond
    · -- dim V₂ ≠ 1. Check dim V₃.
      by_cases hd₃ : Module.finrank k ρ.V₃ = 1
      · -- range A₃ is 1-dim. Use it as p.
        set p := LinearMap.range ρ.A₃
        have hp : Module.finrank k p = 1 := by rw [fr₃, hd₃]
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₂_cond : (LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q) ∨
            (Function.Injective ρ.A₂ ∧ LinearMap.range ρ.A₂ = ⊤) := by
          have : Module.finrank k ρ.V₂ = 0 ∨ Module.finrank k ρ.V₂ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₂, rt₂ h⟩
        exact absurd_pq p q hpq hp hq (h₁_cond p q hpq) h₂_cond
          (Or.inl (Or.inl le_rfl))
      · -- Neither arm 2 nor arm 3 has dim 1. Both have dim 0 or 2.
        -- No constraining ranges. Pick any 1-dim p.
        obtain ⟨p, hp⟩ := get_line
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₂_cond : (LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q) ∨
            (Function.Injective ρ.A₂ ∧ LinearMap.range ρ.A₂ = ⊤) := by
          have : Module.finrank k ρ.V₂ = 0 ∨ Module.finrank k ρ.V₂ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₂, rt₂ h⟩
        have h₃_cond : (LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) ∨
            (Function.Injective ρ.A₃ ∧ LinearMap.range ρ.A₃ = ⊤) := by
          have : Module.finrank k ρ.V₃ = 0 ∨ Module.finrank k ρ.V₃ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₃, rt₃ h⟩
        exact absurd_pq p q hpq hp hq (h₁_cond p q hpq) h₂_cond h₃_cond
  -- For dim V₂ = 1: symmetric argument with arms relabeled
  · have hd₂ : Module.finrank k ρ.V₂ = 0 ∨ Module.finrank k ρ.V₂ = 2 := by omega
    have h₂_cond : ∀ (p q : Submodule k ρ.V), IsCompl p q →
        (LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q) ∨
        (Function.Injective ρ.A₂ ∧ LinearMap.range ρ.A₂ = ⊤) := by
      intro p q _
      rcases hd₂ with h | h
      · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
      · exact Or.inr ⟨hinj₂, rt₂ h⟩
    have get_line : ∃ (p : Submodule k ρ.V), Module.finrank k p = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : ρ.V)
      exact ⟨Submodule.span k {v}, finrank_span_singleton hv⟩
    by_cases hd₁ : Module.finrank k ρ.V₁ = 1
    · set p := LinearMap.range ρ.A₁
      have hp : Module.finrank k p = 1 := by rw [fr₁, hd₁]
      by_cases hd₃ : Module.finrank k ρ.V₃ = 1
      · by_cases heq : p = LinearMap.range ρ.A₃
        · obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
          have hq : Module.finrank k q = 1 := by
            have := Submodule.finrank_add_eq_of_isCompl hpq; omega
          exact absurd_pq p q hpq hp hq (Or.inl (Or.inl le_rfl)) (h₂_cond p q hpq)
            (Or.inl (Or.inl (heq ▸ le_rfl)))
        · have hq : Module.finrank k (LinearMap.range ρ.A₃) = 1 := by rw [fr₃, hd₃]
          have hpq := isCompl_of_finrank_one_ne hV_eq p (LinearMap.range ρ.A₃) hp hq heq
          exact absurd_pq p (LinearMap.range ρ.A₃) hpq hp hq
            (Or.inl (Or.inl le_rfl)) (h₂_cond p _ hpq) (Or.inl (Or.inr le_rfl))
      · obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₃_cond : (LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) ∨
            (Function.Injective ρ.A₃ ∧ LinearMap.range ρ.A₃ = ⊤) := by
          have : Module.finrank k ρ.V₃ = 0 ∨ Module.finrank k ρ.V₃ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₃, rt₃ h⟩
        exact absurd_pq p q hpq hp hq (Or.inl (Or.inl le_rfl)) (h₂_cond p q hpq) h₃_cond
    · by_cases hd₃ : Module.finrank k ρ.V₃ = 1
      · set p := LinearMap.range ρ.A₃
        have hp : Module.finrank k p = 1 := by rw [fr₃, hd₃]
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₁_cond : (LinearMap.range ρ.A₁ ≤ p ∨ LinearMap.range ρ.A₁ ≤ q) ∨
            (Function.Injective ρ.A₁ ∧ LinearMap.range ρ.A₁ = ⊤) := by
          have : Module.finrank k ρ.V₁ = 0 ∨ Module.finrank k ρ.V₁ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₁, rt₁ h⟩
        exact absurd_pq p q hpq hp hq h₁_cond (h₂_cond p q hpq) (Or.inl (Or.inl le_rfl))
      · obtain ⟨p, hp⟩ := get_line
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₁_cond : (LinearMap.range ρ.A₁ ≤ p ∨ LinearMap.range ρ.A₁ ≤ q) ∨
            (Function.Injective ρ.A₁ ∧ LinearMap.range ρ.A₁ = ⊤) := by
          have : Module.finrank k ρ.V₁ = 0 ∨ Module.finrank k ρ.V₁ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₁, rt₁ h⟩
        have h₃_cond : (LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) ∨
            (Function.Injective ρ.A₃ ∧ LinearMap.range ρ.A₃ = ⊤) := by
          have : Module.finrank k ρ.V₃ = 0 ∨ Module.finrank k ρ.V₃ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₃, rt₃ h⟩
        exact absurd_pq p q hpq hp hq h₁_cond (h₂_cond p q hpq) h₃_cond
  -- For dim V₃ = 1: symmetric argument
  · have hd₃ : Module.finrank k ρ.V₃ = 0 ∨ Module.finrank k ρ.V₃ = 2 := by omega
    have h₃_cond : ∀ (p q : Submodule k ρ.V), IsCompl p q →
        (LinearMap.range ρ.A₃ ≤ p ∨ LinearMap.range ρ.A₃ ≤ q) ∨
        (Function.Injective ρ.A₃ ∧ LinearMap.range ρ.A₃ = ⊤) := by
      intro p q _
      rcases hd₃ with h | h
      · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
      · exact Or.inr ⟨hinj₃, rt₃ h⟩
    have get_line : ∃ (p : Submodule k ρ.V), Module.finrank k p = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : ρ.V)
      exact ⟨Submodule.span k {v}, finrank_span_singleton hv⟩
    by_cases hd₁ : Module.finrank k ρ.V₁ = 1
    · set p := LinearMap.range ρ.A₁
      have hp : Module.finrank k p = 1 := by rw [fr₁, hd₁]
      by_cases hd₂ : Module.finrank k ρ.V₂ = 1
      · by_cases heq : p = LinearMap.range ρ.A₂
        · obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
          have hq : Module.finrank k q = 1 := by
            have := Submodule.finrank_add_eq_of_isCompl hpq; omega
          exact absurd_pq p q hpq hp hq (Or.inl (Or.inl le_rfl))
            (Or.inl (Or.inl (heq ▸ le_rfl))) (h₃_cond p q hpq)
        · have hq : Module.finrank k (LinearMap.range ρ.A₂) = 1 := by rw [fr₂, hd₂]
          have hpq := isCompl_of_finrank_one_ne hV_eq p (LinearMap.range ρ.A₂) hp hq heq
          exact absurd_pq p (LinearMap.range ρ.A₂) hpq hp hq
            (Or.inl (Or.inl le_rfl)) (Or.inl (Or.inr le_rfl)) (h₃_cond p _ hpq)
      · obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₂_cond : (LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q) ∨
            (Function.Injective ρ.A₂ ∧ LinearMap.range ρ.A₂ = ⊤) := by
          have : Module.finrank k ρ.V₂ = 0 ∨ Module.finrank k ρ.V₂ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₂, rt₂ h⟩
        exact absurd_pq p q hpq hp hq (Or.inl (Or.inl le_rfl)) h₂_cond (h₃_cond p q hpq)
    · by_cases hd₂ : Module.finrank k ρ.V₂ = 1
      · set p := LinearMap.range ρ.A₂
        have hp : Module.finrank k p = 1 := by rw [fr₂, hd₂]
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₁_cond : (LinearMap.range ρ.A₁ ≤ p ∨ LinearMap.range ρ.A₁ ≤ q) ∨
            (Function.Injective ρ.A₁ ∧ LinearMap.range ρ.A₁ = ⊤) := by
          have : Module.finrank k ρ.V₁ = 0 ∨ Module.finrank k ρ.V₁ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₁, rt₁ h⟩
        exact absurd_pq p q hpq hp hq h₁_cond (Or.inl (Or.inl le_rfl)) (h₃_cond p q hpq)
      · obtain ⟨p, hp⟩ := get_line
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₁_cond : (LinearMap.range ρ.A₁ ≤ p ∨ LinearMap.range ρ.A₁ ≤ q) ∨
            (Function.Injective ρ.A₁ ∧ LinearMap.range ρ.A₁ = ⊤) := by
          have : Module.finrank k ρ.V₁ = 0 ∨ Module.finrank k ρ.V₁ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₁, rt₁ h⟩
        have h₂_cond : (LinearMap.range ρ.A₂ ≤ p ∨ LinearMap.range ρ.A₂ ≤ q) ∨
            (Function.Injective ρ.A₂ ∧ LinearMap.range ρ.A₂ = ⊤) := by
          have : Module.finrank k ρ.V₂ = 0 ∨ Module.finrank k ρ.V₂ = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₂, rt₂ h⟩
        exact absurd_pq p q hpq hp hq h₁_cond h₂_cond (h₃_cond p q hpq)

-- The main classification for the all-injective case
private lemma classification_injective {k : Type*} [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable)
    (hA₁ : LinearMap.ker ρ.A₁ = ⊥) (hA₂ : LinearMap.ker ρ.A₂ = ⊥)
    (hA₃ : LinearMap.ker ρ.A₃ = ⊥) :
    ρ.dimVector ∈ D₄_indecomposable_dimVectors := by
  -- Get dimension bounds from injectivity
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  have hle₁ := LinearMap.finrank_le_finrank_of_injective hinj₁
  have hle₂ := LinearMap.finrank_le_finrank_of_injective hinj₂
  have hle₃ := LinearMap.finrank_le_finrank_of_injective hinj₃
  -- Step 2: Either range sum = ⊤ or all arms zero
  rcases range_sum_eq_top_or_arms_zero ρ hind hA₁ hA₂ hA₃ with hR | ⟨h₁, h₂, h₃⟩
  · -- Range sum = ⊤ case
    -- dim V ≥ 1 from nontriviality
    have hV_pos : 0 < Module.finrank k ρ.V := by
      rcases hind.1 with h | h | h | h
      · exact h
      · exact Nat.lt_of_lt_of_le h hle₁
      · exact Nat.lt_of_lt_of_le h hle₂
      · exact Nat.lt_of_lt_of_le h hle₃
    by_cases hV2 : Module.finrank k ρ.V ≥ 2
    · -- dim V ≥ 2: use the dimension bound lemma
      obtain ⟨hd, hd₁, hd₂, hd₃⟩ := classification_injective_dim_bound ρ hind hA₁ hA₂ hA₃ hR hV2
      unfold D₄Rep.dimVector D₄_indecomposable_dimVectors
      rw [hd, hd₁, hd₂, hd₃]
      simp [Finset.mem_insert]
    · -- dim V = 1: all dᵢ ∈ {0, 1}, membership is trivial
      push_neg at hV2
      have hV1 : Module.finrank k ρ.V = 1 := by omega
      have h₁ : Module.finrank k ρ.V₁ ≤ 1 := by omega
      have h₂ : Module.finrank k ρ.V₂ ≤ 1 := by omega
      have h₃ : Module.finrank k ρ.V₃ ≤ 1 := by omega
      simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert, Prod.mk.injEq]
      -- (1, d₁, d₂, d₃) with dᵢ ∈ {0, 1}: enumerate
      interval_cases (Module.finrank k ρ.V₁) <;>
        interval_cases (Module.finrank k ρ.V₂) <;>
          interval_cases (Module.finrank k ρ.V₃) <;> simp_all
  · -- All arms zero: dim V = 1, so dim vector is (1, 0, 0, 0)
    have hV := dim_V_eq_one_of_arms_zero ρ hind h₁ h₂ h₃
    simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert, Prod.mk.injEq]
    right; right; right; left
    exact ⟨hV, h₁, h₂, h₃⟩

theorem Etingof.Example_6_3_1 (k : Type*) [Field k] (ρ : D₄Rep k)
    (hind : ρ.Indecomposable) :
    ρ.dimVector ∈ D₄_indecomposable_dimVectors := by
  -- Case split on whether each kernel is trivial
  rcases ker_A₁_or_rest_zero ρ hind with hA₁ | ⟨hV, hV₂, hV₃⟩
  · rcases ker_A₂_or_rest_zero ρ hind with hA₂ | ⟨hV, hV₁, hV₃⟩
    · rcases ker_A₃_or_rest_zero ρ hind with hA₃ | ⟨hV, hV₁, hV₂⟩
      · -- All kernels trivial: triple of subspaces problem
        exact classification_injective ρ hind hA₁ hA₂ hA₃
      · -- ker A₃ ≠ ⊥, V = V₁ = V₂ = 0: dim V₃ = 1
        have hV₃ := dim_V₃_eq_one_of_rest_zero ρ hind hV hV₁ hV₂
        simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert,
          Prod.mk.injEq]
        right; right; left
        exact ⟨hV, hV₁, hV₂, hV₃⟩
    · -- ker A₂ ≠ ⊥, V = V₁ = V₃ = 0: dim V₂ = 1
      have hV₂ := dim_V₂_eq_one_of_rest_zero ρ hind hV hV₁ hV₃
      simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert,
        Prod.mk.injEq]
      right; left
      exact ⟨hV, hV₁, hV₂, hV₃⟩
  · -- ker A₁ ≠ ⊥, V = V₂ = V₃ = 0: dim V₁ = 1
    have hV₁ := dim_V₁_eq_one_of_rest_zero ρ hind hV hV₂ hV₃
    simp only [D₄Rep.dimVector, D₄_indecomposable_dimVectors, Finset.mem_insert,
      Prod.mk.injEq]
    left
    exact ⟨hV, hV₁, hV₂, hV₃⟩

/-- The set of indecomposable dimension vectors has exactly 12 elements,
corresponding to the 12 positive roots of D₄. -/
theorem D₄_indecomposable_dimVectors_card :
    D₄_indecomposable_dimVectors.card = 12 := by
  decide

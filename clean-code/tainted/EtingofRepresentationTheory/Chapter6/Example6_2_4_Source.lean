import Mathlib
import EtingofRepresentationTheory.Chapter6.Example6_2_4

/-!
# Example 6.2.4, first orientation: classification up to isomorphism

`Example6_2_4.lean` proves that an indecomposable representation of the quiver `• → • → •`
has dimension vector among

  `(1,0,0)`, `(0,1,0)`, `(0,0,1)`, `(1,1,0)`, `(0,1,1)`, `(1,1,1)`,

with the indicated maps injective. This file upgrades that necessary condition to a
classification of isomorphism classes: it constructs the six representatives, proves each is
indecomposable, and proves every indecomposable representation is isomorphic to exactly one of
them. The dimension vectors are pairwise distinct, so they already separate the six classes.

The companion file `Example6_2_4_Sink.lean` does the same for the second orientation.
-/

open Module

/-- Isomorphism of representations of `• → • → •`. -/
structure A₃Rep.Iso {k : Type*} [Field k] (ρ σ : A₃Rep k) where
  e₁ : ρ.V₁ ≃ₗ[k] σ.V₁
  e₂ : ρ.V₂ ≃ₗ[k] σ.V₂
  e₃ : ρ.V₃ ≃ₗ[k] σ.V₃
  comm_f : ∀ x, e₂ (ρ.f x) = σ.f (e₁ x)
  comm_g : ∀ y, e₃ (ρ.g y) = σ.g (e₂ y)

namespace A₃Rep.Iso

/-- The identity isomorphism. -/
def refl {k : Type*} [Field k] (ρ : A₃Rep k) : ρ.Iso ρ where
  e₁ := LinearEquiv.refl k ρ.V₁
  e₂ := LinearEquiv.refl k ρ.V₂
  e₃ := LinearEquiv.refl k ρ.V₃
  comm_f := fun _ => rfl
  comm_g := fun _ => rfl

/-- The inverse of an isomorphism. -/
def symm {k : Type*} [Field k] {ρ σ : A₃Rep k} (e : ρ.Iso σ) : σ.Iso ρ where
  e₁ := e.e₁.symm
  e₂ := e.e₂.symm
  e₃ := e.e₃.symm
  comm_f := fun y => by
    apply e.e₂.injective
    rw [e.e₂.apply_symm_apply, e.comm_f, e.e₁.apply_symm_apply]
  comm_g := fun y => by
    apply e.e₃.injective
    rw [e.e₃.apply_symm_apply, e.comm_g, e.e₂.apply_symm_apply]

/-- Composition of isomorphisms. -/
def trans {k : Type*} [Field k] {ρ σ τ : A₃Rep k} (e : ρ.Iso σ) (e' : σ.Iso τ) : ρ.Iso τ where
  e₁ := e.e₁.trans e'.e₁
  e₂ := e.e₂.trans e'.e₂
  e₃ := e.e₃.trans e'.e₃
  comm_f := fun x => by
    simp only [LinearEquiv.trans_apply]
    rw [e.comm_f, e'.comm_f]
  comm_g := fun y => by
    simp only [LinearEquiv.trans_apply]
    rw [e.comm_g, e'.comm_g]

/-- Isomorphic representations have equal dimensions at all three vertices. -/
lemma finrank_eq {k : Type*} [Field k] {ρ σ : A₃Rep k} (e : ρ.Iso σ) :
    Module.finrank k ρ.V₁ = Module.finrank k σ.V₁ ∧
    Module.finrank k ρ.V₂ = Module.finrank k σ.V₂ ∧
    Module.finrank k ρ.V₃ = Module.finrank k σ.V₃ :=
  ⟨e.e₁.finrank_eq, e.e₂.finrank_eq, e.e₃.finrank_eq⟩

end A₃Rep.Iso

/-- The representative `k → 0 → 0`. -/
abbrev A₃Rep.rep_100 (k : Type*) [Field k] : A₃Rep k where
  V₁ := k
  V₂ := PUnit
  V₃ := PUnit
  f := 0
  g := 0

/-- The representative `0 → k → 0`. -/
abbrev A₃Rep.rep_010 (k : Type*) [Field k] : A₃Rep k where
  V₁ := PUnit
  V₂ := k
  V₃ := PUnit
  f := 0
  g := 0

/-- The representative `0 → 0 → k`. -/
abbrev A₃Rep.rep_001 (k : Type*) [Field k] : A₃Rep k where
  V₁ := PUnit
  V₂ := PUnit
  V₃ := k
  f := 0
  g := 0

/-- The representative `k ≃ k → 0`. -/
abbrev A₃Rep.rep_110 (k : Type*) [Field k] : A₃Rep k where
  V₁ := k
  V₂ := k
  V₃ := PUnit
  f := LinearMap.id
  g := 0

/-- The representative `0 → k ≃ k`. -/
abbrev A₃Rep.rep_011 (k : Type*) [Field k] : A₃Rep k where
  V₁ := PUnit
  V₂ := k
  V₃ := k
  f := 0
  g := LinearMap.id

/-- The representative `k ≃ k ≃ k`. -/
abbrev A₃Rep.rep_111 (k : Type*) [Field k] : A₃Rep k where
  V₁ := k
  V₂ := k
  V₃ := k
  f := LinearMap.id
  g := LinearMap.id

namespace A₃Rep

/-- Every submodule of a subsingleton module is trivial. -/
private theorem submodule_eq_bot_of_subsingleton {k M : Type*} [Field k] [AddCommGroup M]
    [Module k M] [Subsingleton M] (p : Submodule k M) : p = ⊥ := by
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
  have hgp' : Module.finrank k p₂ ≤ Module.finrank k p₃ :=
    Submodule.finrank_mono (fun y hy => by simpa using hgp y hy)
  have hgq' : Module.finrank k q₂ ≤ Module.finrank k q₃ :=
    Submodule.finrank_mono (fun y hy => by simpa using hgq y hy)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₂) with h0 | hpos
  · exact Or.inl ⟨submodule_eq_bot_of_subsingleton p₁, Submodule.finrank_eq_zero.mp h0,
      Submodule.finrank_eq_zero.mp (by omega)⟩
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
  have hgp' : Module.finrank k p₂ ≤ Module.finrank k p₃ :=
    Submodule.finrank_mono (fun y hy => by simpa using hgp y hy)
  have hgq' : Module.finrank k q₂ ≤ Module.finrank k q₃ :=
    Submodule.finrank_mono (fun y hy => by simpa using hgq y hy)
  rcases Nat.eq_zero_or_pos (Module.finrank k p₁) with h0 | hpos
  · exact Or.inl ⟨Submodule.finrank_eq_zero.mp h0, Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega)⟩
  · exact Or.inr ⟨Submodule.finrank_eq_zero.mp (by omega),
      Submodule.finrank_eq_zero.mp (by omega), Submodule.finrank_eq_zero.mp (by omega)⟩

/-- The six representatives, indexed by `Fin 6`. -/
def rep (k : Type*) [Field k] : Fin 6 → A₃Rep k
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

/-- Dimension vector of a representation of `• → • → •`. -/
noncomputable def dimvec (k : Type*) [Field k] (σ : A₃Rep k) : ℕ × ℕ × ℕ :=
  (Module.finrank k σ.V₁, Module.finrank k σ.V₂, Module.finrank k σ.V₃)

theorem Iso.dimvec_eq {k : Type*} [Field k] {ρ σ : A₃Rep k} (e : ρ.Iso σ) :
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

/-- **Example 6.2.4(1) (Etingof), classification.** Every indecomposable representation of the
quiver `• → • → •` is isomorphic to exactly one of the six representatives. -/
theorem exists_unique_iso_rep (k : Type*) [Field k] (ρ : A₃Rep k) (hind : ρ.Indecomposable) :
    ∃! i : Fin 6, Nonempty (ρ.Iso (rep k i)) := by
  have hexists : ∃ i : Fin 6, Nonempty (ρ.Iso (rep k i)) := by
    rcases Etingof.Example_6_2_4 k ρ hind with
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
      exact ⟨{ e₁ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
               e₂ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact (finrank_self k).symm)).some
               e₃ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
               comm_f := fun x => by rw [Subsingleton.elim x 0]; simp
               comm_g := fun _ => Subsingleton.elim _ _ }⟩
    · refine ⟨2, ?_⟩
      change Nonempty (ρ.Iso (rep_001 k))
      haveI hs₂ : Subsingleton ρ.V₂ := Module.finrank_zero_iff.mp h2
      exact ⟨{ e₁ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
               e₂ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h2]; exact finrank_zero_of_subsingleton.symm)).some
               e₃ := (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
                  (by rw [h3]; exact (finrank_self k).symm)).some
               comm_f := fun _ => Subsingleton.elim _ _
               comm_g := fun y => by rw [Subsingleton.elim y 0]; simp }⟩
    · refine ⟨3, ?_⟩
      change Nonempty (ρ.Iso (rep_110 k))
      haveI hs₃ : Subsingleton ρ.V₃ := Module.finrank_zero_iff.mp h3
      have hf_bij : Function.Bijective ρ.f :=
        ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h1, h2])).mp hf⟩
      obtain ⟨e₁⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.V₁) (M' := k) (by rw [h1]; exact (finrank_self k).symm)
      let fEq : ρ.V₁ ≃ₗ[k] ρ.V₂ := LinearEquiv.ofBijective ρ.f hf_bij
      refine ⟨{ e₁ := e₁, e₂ := fEq.symm.trans e₁, e₃ := ?_
                comm_f := fun x => ?_
                comm_g := fun _ => Subsingleton.elim _ _ }⟩
      · exact (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
          (by rw [h3]; exact finrank_zero_of_subsingleton.symm)).some
      · have hfx : fEq.symm (ρ.f x) = x := fEq.symm_apply_apply x
        simp only [LinearEquiv.trans_apply, hfx]
        rfl
    · refine ⟨4, ?_⟩
      change Nonempty (ρ.Iso (rep_011 k))
      haveI hs₁ : Subsingleton ρ.V₁ := Module.finrank_zero_iff.mp h1
      have hg_bij : Function.Bijective ρ.g :=
        ⟨hg, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h2, h3])).mp hg⟩
      obtain ⟨e₂⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.V₂) (M' := k) (by rw [h2]; exact (finrank_self k).symm)
      let gEq : ρ.V₂ ≃ₗ[k] ρ.V₃ := LinearEquiv.ofBijective ρ.g hg_bij
      refine ⟨{ e₁ := ?_, e₂ := e₂, e₃ := gEq.symm.trans e₂
                comm_f := fun x => by rw [Subsingleton.elim x 0]; simp
                comm_g := fun y => ?_ }⟩
      · exact (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
          (by rw [h1]; exact finrank_zero_of_subsingleton.symm)).some
      · have hgy : gEq.symm (ρ.g y) = y := gEq.symm_apply_apply y
        simp only [LinearEquiv.trans_apply, hgy]
        rfl
    · refine ⟨5, ?_⟩
      change Nonempty (ρ.Iso (rep_111 k))
      have hf_bij : Function.Bijective ρ.f :=
        ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h1, h2])).mp hf⟩
      have hg_bij : Function.Bijective ρ.g :=
        ⟨hg, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h2, h3])).mp hg⟩
      obtain ⟨e₁⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
        (R := k) (M := ρ.V₁) (M' := k) (by rw [h1]; exact (finrank_self k).symm)
      let fEq : ρ.V₁ ≃ₗ[k] ρ.V₂ := LinearEquiv.ofBijective ρ.f hf_bij
      let gEq : ρ.V₂ ≃ₗ[k] ρ.V₃ := LinearEquiv.ofBijective ρ.g hg_bij
      refine ⟨{ e₁ := e₁, e₂ := fEq.symm.trans e₁, e₃ := gEq.symm.trans (fEq.symm.trans e₁)
                comm_f := fun x => ?_
                comm_g := fun y => ?_ }⟩
      · have hfx : fEq.symm (ρ.f x) = x := fEq.symm_apply_apply x
        simp only [LinearEquiv.trans_apply, hfx]
        rfl
      · have hgy : gEq.symm (ρ.g y) = y := gEq.symm_apply_apply y
        simp only [LinearEquiv.trans_apply, hgy]
        rfl
  obtain ⟨i, hi⟩ := hexists
  refine ⟨i, hi, fun j hj => ?_⟩
  obtain ⟨ei⟩ := hi
  obtain ⟨ej⟩ := hj
  have hdv : dimvec k (rep k j) = dimvec k (rep k i) := (ej.symm.trans ei).dimvec_eq
  fin_cases i <;> fin_cases j <;>
    simp_all [rep, dimvec_rep_100, dimvec_rep_010, dimvec_rep_001, dimvec_rep_110,
      dimvec_rep_011, dimvec_rep_111]

end A₃Rep

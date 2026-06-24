import Mathlib
import EtingofRepresentationTheory.Chapter3.Theorem3_10_2

/-!
# Theorem 5.6.1: Irreducible Representations of Product Groups

Let `G`, `H` be finite groups, let `{Vᵢ}` be the irreducible representations of `G`
over an algebraically closed field `k`, and let `{Wⱼ}` be the irreducible representations
of `H`. Then the irreducible representations of `G × H` over `k` are exactly the external
tensor products `{Vᵢ ⊗ Wⱼ}`.

Following Etingof, this is a direct consequence of Theorem 3.10.2 (the classification of
simple modules over a tensor product of finite-dimensional algebras), applied with
`A = k[G]` and `B = k[H]`. A representation of `G` is a module over the group algebra
`k[G]`, an irreducible representation is a simple module, and a representation of `G × H`
restricts to commuting actions of `G` and `H` (because `(g, h) = (g, 1) · (1, h)`), i.e.
a module over `k[G] ⊗ k[H]`.

## Main results

* `Etingof.IsIrreducibleRep` — irreducibility of a representation (nonzero, with no proper
  nonzero subrepresentations).
* `Etingof.extTprod` — the external tensor product `V ⊗ W` of a representation of `G` and a
  representation of `H`, as a representation of `G × H`.
* `Etingof.extTprod_isIrreducibleRep` — Theorem 5.6.1(i): the external tensor product of two
  irreducible representations is irreducible.
* `Etingof.exists_extTprod_of_isIrreducibleRep` — Theorem 5.6.1(ii): every irreducible
  representation of `G × H` is isomorphic to an external tensor product of an irreducible
  representation of `G` and one of `H`.
-/

open scoped TensorProduct
open MonoidAlgebra

namespace Etingof

variable {k : Type*} [CommSemiring k]

/-- A representation is *irreducible* if its underlying module is nonzero and its only
sub-`k`-modules stable under the group action are `⊥` and `⊤`. -/
def IsIrreducibleRep {Γ M : Type*} [Monoid Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) : Prop :=
  Nontrivial M ∧ ∀ N : Submodule k M, (∀ γ : Γ, ∀ x ∈ N, ρ γ x ∈ N) → N = ⊥ ∨ N = ⊤

/-! ### The external tensor product representation -/

section ExtTprod

variable {G H V W : Type*} [Monoid G] [Monoid H]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

/-- The external tensor product of a representation `ρ` of `G` on `V` and a representation `σ`
of `H` on `W`: the representation of `G × H` on `V ⊗[k] W` where `(g, h)` acts by
`ρ g ⊗ σ h`. -/
noncomputable def extTprod (ρ : Representation k G V) (σ : Representation k H W) :
    Representation k (G × H) (V ⊗[k] W) where
  toFun gh := TensorProduct.map (ρ gh.1) (σ gh.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one, TensorProduct.map_one]
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, TensorProduct.map_mul]

@[simp]
theorem extTprod_apply (ρ : Representation k G V) (σ : Representation k H W) (gh : G × H) :
    extTprod ρ σ gh = TensorProduct.map (ρ gh.1) (σ gh.2) :=
  rfl

end ExtTprod

/-! ### Bridge to simple modules over the group algebra -/

/-- An irreducible representation of `G` is a simple module over the group algebra `k[G]`. -/
theorem isSimpleModule_asModule_of_isIrreducibleRep
    {k Γ M : Type*} [Field k] [Monoid Γ] [AddCommGroup M] [Module k M]
    {ρ : Representation k Γ M} (h : IsIrreducibleRep ρ) :
    IsSimpleModule (MonoidAlgebra k Γ) ρ.asModule := by
  obtain ⟨hnt, hsub⟩ := h
  haveI : Nontrivial M := hnt
  haveI : Nontrivial ρ.asModule := hnt
  refine { toIsSimpleOrder := { eq_bot_or_eq_top := fun N => ?_ } }
  -- View the `k[Γ]`-submodule `N` as a subrepresentation (a `ρ`-stable `k`-submodule).
  set τ := Subrepresentation.ofSubmodule' N with hτ
  rcases hsub τ.toSubmodule (fun γ x hx => τ.apply_mem_toSubmodule γ hx) with hbot | htop
  · left
    refine eq_bot_iff.mpr fun w hw => ?_
    have hmem : w ∈ τ.toSubmodule := (Subrepresentation.mem_ofSubmodule'_iff).mpr hw
    rw [hbot, Submodule.mem_bot] at hmem
    simpa [hmem] using N.zero_mem
  · right
    refine eq_top_iff.mpr fun w _ => ?_
    have hmem : w ∈ τ.toSubmodule := by rw [htop]; trivial
    exact (Subrepresentation.mem_ofSubmodule'_iff).mp hmem

/-! ### Theorem 5.6.1(i): the external tensor product of irreducibles is irreducible -/

section PartI

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
variable {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Helper: a `k`-submodule of `V ⊗ W` stable under all of the `G × H`-actions
`ρ g ⊗ σ h` is also stable under `Algebra.lsmul a ⊗ Algebra.lsmul b` for arbitrary
`a ∈ k[G]`, `b ∈ k[H]` (the hypothesis required by `Etingof.tensor_product_irreducible`). -/
private theorem map_lsmul_mem_of_extTprod_stable
    (ρ : Representation k G V) (σ : Representation k H W)
    (N : Submodule k (V ⊗[k] W))
    (hN : ∀ gh : G × H, ∀ x ∈ N, extTprod ρ σ gh x ∈ N)
    (a : MonoidAlgebra k G) (b : MonoidAlgebra k H) (x : V ⊗[k] W) (hx : x ∈ N) :
    TensorProduct.map
      ((Algebra.lsmul k k ρ.asModule : MonoidAlgebra k G →ₐ[k] Module.End k ρ.asModule) a)
      ((Algebra.lsmul k k σ.asModule : MonoidAlgebra k H →ₐ[k] Module.End k σ.asModule) b)
      x ∈ N := by
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
    simp only [map_zero, TensorProduct.map_zero_left, LinearMap.zero_apply]
    exact N.zero_mem
  | add a₁ a₂ h₁ h₂ =>
    rw [map_add, TensorProduct.map_add_left]
    exact N.add_mem h₁ h₂
  | single g c =>
    -- Reduce the left factor: `lsmul (single g c) = c • ρ g`.
    have hL : (Algebra.lsmul k k ρ.asModule (MonoidAlgebra.single g c)) = c • ρ g := by
      ext v
      show (MonoidAlgebra.single g c) • v = (c • ρ g) v
      rw [Representation.single_smul]
      rfl
    induction b using MonoidAlgebra.induction_linear with
    | zero =>
      simp only [map_zero, TensorProduct.map_zero_right, LinearMap.zero_apply]
      exact N.zero_mem
    | add b₁ b₂ hb₁ hb₂ =>
      rw [map_add, TensorProduct.map_add_right]
      exact N.add_mem hb₁ hb₂
    | single h d =>
      have hR : (Algebra.lsmul k k σ.asModule (MonoidAlgebra.single h d)) = d • σ h := by
        ext w
        show (MonoidAlgebra.single h d) • w = (d • σ h) w
        rw [Representation.single_smul]
        rfl
      rw [hL, hR, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
        LinearMap.smul_apply, LinearMap.smul_apply]
      refine N.smul_mem c (N.smul_mem d ?_)
      exact hN (g, h) x hx

/-- **Theorem 5.6.1(i).** The external tensor product of an irreducible representation of `G`
and an irreducible representation of `H` is an irreducible representation of `G × H`. -/
theorem extTprod_isIrreducibleRep
    {ρ : Representation k G V} {σ : Representation k H W}
    (hρ : IsIrreducibleRep ρ) (hσ : IsIrreducibleRep σ) :
    IsIrreducibleRep (extTprod ρ σ) := by
  haveI hsG : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    isSimpleModule_asModule_of_isIrreducibleRep hρ
  haveI hsH : IsSimpleModule (MonoidAlgebra k H) σ.asModule :=
    isSimpleModule_asModule_of_isIrreducibleRep hσ
  haveI : Nontrivial V := hρ.1
  haveI : Nontrivial W := hσ.1
  refine ⟨?_, ?_⟩
  · have hpos : 0 < Module.finrank k (V ⊗[k] W) := by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
    exact Module.nontrivial_of_finrank_pos hpos
  · intro N hN
    exact tensor_product_irreducible k (MonoidAlgebra k G) (MonoidAlgebra k H)
      ρ.asModule σ.asModule N (map_lsmul_mem_of_extTprod_stable ρ σ N hN)

end PartI

end Etingof

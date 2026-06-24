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

/-! ### From a group-algebra module to a representation -/

section OfModule

variable {k G V : Type*} [CommSemiring k] [Monoid G]
  [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
  [IsScalarTower k (MonoidAlgebra k G) V]

/-- A module over the group algebra `k[G]` is a representation of `G`, with `g` acting by
`single g 1 • ·`. -/
noncomputable def ofGroupAlgebraModule : Representation k G V where
  toFun g :=
    { toFun := fun v => (MonoidAlgebra.single g (1 : k)) • v
      map_add' := fun x y => smul_add _ _ _
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [smul_comm] }
  map_one' := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
    rw [show (MonoidAlgebra.single (1 : G) (1 : k)) = 1 from (MonoidAlgebra.one_def).symm, one_smul]
  map_mul' g h := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    rw [show (MonoidAlgebra.single (g * h) (1 : k))
          = MonoidAlgebra.single g 1 * MonoidAlgebra.single h 1 from by
        rw [MonoidAlgebra.single_mul_single, one_mul], mul_smul]

@[simp]
theorem ofGroupAlgebraModule_apply (g : G) (v : V) :
    ofGroupAlgebraModule (k := k) (G := G) (V := V) g v = (MonoidAlgebra.single g (1 : k)) • v :=
  rfl

/-- `single g 1 • v` is exactly the `k[G]`-action coming from `ofGroupAlgebraModule`, i.e. it
equals `Algebra.lsmul k k V (single g 1)`. -/
theorem lsmul_single_eq (g : G) :
    (Algebra.lsmul k k V (MonoidAlgebra.single g (1 : k)) : Module.End k V)
      = ofGroupAlgebraModule (k := k) (G := G) (V := V) g := by
  ext v
  simp only [Algebra.lsmul_coe, ofGroupAlgebraModule_apply]

end OfModule

/-- An irreducible (= simple) module over `k[G]` gives an irreducible representation of `G`. -/
theorem isIrreducibleRep_ofGroupAlgebraModule
    {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [Module (MonoidAlgebra k G) V]
    [IsScalarTower k (MonoidAlgebra k G) V] [IsSimpleModule (MonoidAlgebra k G) V] :
    IsIrreducibleRep (ofGroupAlgebraModule (k := k) (G := G) (V := V)) := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra k G) V
  refine ⟨inferInstance, fun N hN => ?_⟩
  -- The `k`-submodule `N` is in fact a `k[G]`-submodule, by linearity of the action.
  let N' : Submodule (MonoidAlgebra k G) V :=
    { carrier := N
      add_mem' := fun hx hy => N.add_mem hx hy
      zero_mem' := N.zero_mem
      smul_mem' := fun a v hv => by
        induction a using MonoidAlgebra.induction_linear with
        | zero => simpa using N.zero_mem
        | add a₁ a₂ h₁ h₂ => rw [add_smul]; exact N.add_mem h₁ h₂
        | single g c =>
          have hsm : (MonoidAlgebra.single g c) • v = c • ((MonoidAlgebra.single g (1 : k)) • v) := by
            rw [← smul_assoc]
            congr 1
            rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
          rw [hsm]
          exact N.smul_mem c (hN g v hv) }
  have hNN' : ∀ x, x ∈ N' ↔ x ∈ N := fun _ => Iff.rfl
  rcases eq_bot_or_eq_top N' with h | h
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ N' := (hNN' x).mpr hx
    rw [h, Submodule.mem_bot] at this
    simp [this]
  · right
    refine eq_top_iff.mpr fun x _ => ?_
    have : x ∈ N' := by rw [h]; trivial
    exact (hNN' x).mp this

/-! ### Theorem 5.6.1(ii): every irreducible representation of `G × H` is an external
tensor product -/

section PartII

universe u

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
variable {M : Type u} [AddCommGroup M] [Module k M] [FiniteDimensional k M]

/-- **Theorem 5.6.1(ii).** Every irreducible representation `τ` of `G × H` over an
algebraically closed field is isomorphic, as a representation, to an external tensor product
`V ⊗ W` of an irreducible representation `V` of `G` and an irreducible representation `W` of
`H`. -/
theorem exists_extTprod_of_isIrreducibleRep
    (τ : Representation k (G × H) M) (hτ : IsIrreducibleRep τ) :
    ∃ (V W : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
      (ρ : Representation k G V) (σ : Representation k H W),
      IsIrreducibleRep ρ ∧ IsIrreducibleRep σ ∧
      ∃ e : M ≃ₗ[k] V ⊗[k] W, ∀ gh : G × H, ∀ m : M, e (τ gh m) = extTprod ρ σ gh (e m) := by
  obtain ⟨hM_nt, hM_irr⟩ := hτ
  haveI : Nontrivial M := hM_nt
  -- Restrict `τ` to the two factors, giving commuting `k[G]`- and `k[H]`-actions on `M`.
  set ρM : Representation k G M := τ.comp (MonoidHom.inl G H) with hρM
  set σM : Representation k H M := τ.comp (MonoidHom.inr G H) with hσM
  letI iAG : Module (MonoidAlgebra k G) M :=
    inferInstanceAs (Module (MonoidAlgebra k G) ρM.asModule)
  letI iAH : Module (MonoidAlgebra k H) M :=
    inferInstanceAs (Module (MonoidAlgebra k H) σM.asModule)
  letI iTG : IsScalarTower k (MonoidAlgebra k G) M :=
    inferInstanceAs (IsScalarTower k (MonoidAlgebra k G) ρM.asModule)
  letI iTH : IsScalarTower k (MonoidAlgebra k H) M :=
    inferInstanceAs (IsScalarTower k (MonoidAlgebra k H) σM.asModule)
  -- The generators act through `τ`: `single g c` acts as `c • τ (g, 1)`, etc.
  have hGsmul : ∀ (c : k) (g : G) (x : M), (MonoidAlgebra.single g c) • x = c • τ (g, 1) x := by
    intro c g x
    rw [Representation.single_smul]
    rfl
  have hHsmul : ∀ (d : k) (h : H) (x : M), (MonoidAlgebra.single h d) • x = d • τ (1, h) x := by
    intro d h x
    rw [Representation.single_smul]
    rfl
  -- `single g 1 • (single h 1 • x) = τ (g, h) x`, since `(g, 1) * (1, h) = (g, h)`.
  have hcompute : ∀ (g : G) (h : H) (x : M),
      (MonoidAlgebra.single g (1 : k)) • ((MonoidAlgebra.single h (1 : k)) • x) = τ (g, h) x := by
    intro g h x
    rw [hHsmul, one_smul, hGsmul, one_smul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp [Prod.ext_iff]
  -- The two actions commute.
  haveI iComm : SMulCommClass (MonoidAlgebra k G) (MonoidAlgebra k H) M := by
    refine ⟨fun a b m => ?_⟩
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a₁ a₂ h₁ h₂ => rw [add_smul, add_smul, smul_add, h₁, h₂]
    | single g c =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp
      | add b₁ b₂ hb₁ hb₂ => rw [add_smul, smul_add, add_smul, hb₁, hb₂]
      | single h d =>
        have hcomm : τ (g, 1) (τ (1, h) m) = τ (1, h) (τ (g, 1) m) := by
          have hprod : ((g, 1) : G × H) * (1, h) = (1, h) * (g, 1) := by simp [Prod.ext_iff]
          rw [← Module.End.mul_apply, ← map_mul, hprod, map_mul, Module.End.mul_apply]
        simp only [hGsmul, hHsmul, map_smul]
        rw [hcomm, smul_comm (c : k) (d : k)]
  -- Irreducibility of `M` as a module with commuting actions.
  have hMirr' : ∀ (U : Submodule k M),
      (∀ (a : MonoidAlgebra k G) (x : M), x ∈ U → a • x ∈ U) →
      (∀ (b : MonoidAlgebra k H) (x : M), x ∈ U → b • x ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hUA hUB
    refine hM_irr U fun gh x hx => ?_
    obtain ⟨g, h⟩ := gh
    have hx1 : (MonoidAlgebra.single h (1 : k)) • x ∈ U := hUB _ x hx
    have hx2 : (MonoidAlgebra.single g (1 : k)) • ((MonoidAlgebra.single h (1 : k)) • x) ∈ U :=
      hUA _ _ hx1
    rw [← hcompute]; exact hx2
  -- Apply Theorem 3.10.2(ii).
  obtain ⟨V, W, instV, instkV, instAV, instTV, instFV, hVsimple,
      instW, instkW, instBW, instTW, instFW, hWsimple, e, hAe, hBe⟩ :=
    Etingof.tensor_product_irreducible_classification k (MonoidAlgebra k G) (MonoidAlgebra k H)
      M hMirr'
  -- Build the representations and their irreducibility.
  refine ⟨V, W, instV, instkV, instFV, instW, instkW, instFW,
    ofGroupAlgebraModule (k := k) (G := G) (V := V),
    ofGroupAlgebraModule (k := k) (G := H) (V := W),
    isIrreducibleRep_ofGroupAlgebraModule, isIrreducibleRep_ofGroupAlgebraModule, e, ?_⟩
  intro gh m
  obtain ⟨g, h⟩ := gh
  -- Use `τ (g, h) m = single g 1 • (single h 1 • m)` and the equivariance of `e`.
  rw [← hcompute, hAe, hBe]
  -- `map (lsmul (single g 1)) id (map id (lsmul (single h 1)) (e m)) = map (ρ g) (σ h) (e m)`.
  rw [lsmul_single_eq, lsmul_single_eq, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    LinearMap.comp_id, LinearMap.id_comp]
  rfl

end PartII

end Etingof

import Mathlib

/-!
# A monomial basis of the symmetric power `SⁿV`

Mathlib defines the symmetric tensor power `Sym[k] (Fin n) V` as a quotient of the tensor power
`⨂ⁿV` by the permutation relation, but provides **no basis** for it (the universal property and the
relation to homogeneous polynomials are listed as TODOs in
`Mathlib.LinearAlgebra.TensorPower.Symmetric`). This file supplies that missing piece: given a basis
`b : Basis κ k V` of `V`, it constructs a genuine `Module.Basis` of `SⁿV` indexed by **degree-`n`
monomials** in `b` — that is, by `κ`-valued index tuples `Fin n → κ` taken up to permutation.

## Construction

The heart of the argument is the *symmetrized-orbit* picture of `SⁿV`:

* The tensor power `⨂ⁿV` has the basis `tensorBasis b` indexed by `p : Fin n → κ`, with
  `tensorBasis b p = ⨂ₜ i, b (p i)` (`Basis.piTensorProduct`).
* The quotient map `mk : ⨂ⁿV → SⁿV` identifies two basis tensors exactly when their indices are
  permutations of one another, so the images `mk (tensorBasis b p)` depend only on the monomial
  class `⟦p⟧` and span `SⁿV`.
* There are no further relations: we build an explicit linear isomorphism
  `SⁿV ≃ₗ[k] (Monomial n κ →₀ k)` whose forward map reads off the tensor coordinates and pushes them
  along the quotient of index tuples, and whose inverse sends `⟦p⟧ ↦ mk (tensorBasis b p)`. The two
  composites are checked on the tensor basis and on the standard basis of the finsupp, respectively.

Transporting the standard basis of `Monomial n κ →₀ k` through this isomorphism
(`Basis.ofRepr`) yields `symmetricPowerMonomialBasis b`, with
`symmetricPowerMonomialBasis b ⟦p⟧ = mk (⨂ₜ i, b (p i))` (`symmetricPowerMonomialBasis_toMonomial`).

This is the input required by `Etingof.DiagonalCoordinate.eq_bot_or_eq_top_of_connected` for the
symmetric half of Problem 4.12.3 (irreducibility of `SⁿV`, cited in Example 5.19.3): the diagonal
element of `GL(V)` acts on this basis with a monomial eigenvalue, and the transvections supply the
connectivity. Those steps are downstream; this file only builds the basis.
-/

open scoped TensorProduct BigOperators
open Module

namespace Etingof.SymmetricPowerBasis

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
  {κ : Type*} {n : ℕ}

/-- Two length-`n` index tuples describe the *same monomial* when one is a permutation of the other:
`p ≈ q` iff `q = p ∘ σ` for some `σ ∈ Sₙ`. -/
def monomialSetoid (n : ℕ) (κ : Type*) : Setoid (Fin n → κ) where
  r p q := ∃ σ : Equiv.Perm (Fin n), q = p ∘ σ
  iseqv :=
    { refl := fun p => ⟨1, by funext i; simp⟩
      symm := fun {p q} ⟨σ, h⟩ => ⟨σ⁻¹, by subst h; funext i; simp⟩
      trans := fun {p q r} ⟨σ, h⟩ ⟨τ, h'⟩ =>
        ⟨σ * τ, by subst h; subst h'; funext i; simp⟩ }

/-- Degree-`n` monomials in a `κ`-indexed basis: index tuples `Fin n → κ` up to permutation. -/
def Monomial (n : ℕ) (κ : Type*) : Type _ := Quotient (monomialSetoid n κ)

/-- The monomial class of an index tuple. -/
def toMonomial : (Fin n → κ) → Monomial n κ := Quotient.mk (monomialSetoid n κ)

/-- The basis of the tensor power `⨂ⁿV` induced by a basis `b` of `V`; the basis vector at
`p : Fin n → κ` is `⨂ₜ i, b (p i)`. -/
noncomputable def tensorBasis (b : Basis κ k V) :
    Basis (Fin n → κ) k (⨂[k] (_ : Fin n), V) :=
  Basis.piTensorProduct (fun _ : Fin n => b)

/-- The symmetric-power element attached to a monomial: `⟦p⟧ ↦ mk (⨂ₜ i, b (p i))`. Well-defined
because permuting the index tuple leaves the class in `SⁿV` unchanged. -/
noncomputable def monomialTensor (b : Basis κ k V) :
    Monomial n κ → SymmetricPower k (Fin n) V :=
  Quotient.lift (fun p => SymmetricPower.mk k (Fin n) V (tensorBasis b p))
    (by
      rintro p q ⟨σ, rfl⟩
      simp only [tensorBasis, Basis.piTensorProduct_apply]
      exact (SymmetricPower.tprod_equiv σ (fun i => b (p i))).symm)

@[simp] lemma monomialTensor_toMonomial (b : Basis κ k V) (p : Fin n → κ) :
    monomialTensor b (toMonomial p) = SymmetricPower.mk k (Fin n) V (tensorBasis b p) :=
  rfl

/-- The coordinate map on the tensor power: read the `tensorBasis` coordinates of a tensor and push
them forward along the quotient `Fin n → κ ↠ Monomial n κ`. This descends through `mk` to `SⁿV`
(see `toFinsupp`). -/
noncomputable def toFinsuppAux (b : Basis κ k V) :
    (⨂[k] (_ : Fin n), V) →ₗ[k] (Monomial n κ →₀ k) :=
  (Finsupp.lmapDomain k k (toMonomial (n := n) (κ := κ))).comp (tensorBasis b).repr.toLinearMap

@[simp] lemma toFinsuppAux_basis (b : Basis κ k V) (p : Fin n → κ) :
    toFinsuppAux b (tensorBasis b p) = Finsupp.single (toMonomial p) 1 := by
  simp only [toFinsuppAux, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The coordinate map is invariant under permuting the tensor factors: this is the reason it
descends to the symmetric power. Checked on the tensor basis, where a permutation just relabels the
monomial class. -/
lemma toFinsuppAux_reindex (b : Basis κ k V) (σ : Equiv.Perm (Fin n))
    (x : ⨂[k] (_ : Fin n), V) :
    toFinsuppAux b (PiTensorProduct.reindex k (fun _ : Fin n => V) σ x) = toFinsuppAux b x := by
  have h : (toFinsuppAux b).comp
      (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap = toFinsuppAux b := by
    apply Basis.ext (tensorBasis b)
    intro p
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hre : PiTensorProduct.reindex k (fun _ : Fin n => V) σ (tensorBasis b p)
        = tensorBasis b (fun i => p (σ.symm i)) := by
      simp only [tensorBasis, Basis.piTensorProduct_apply, PiTensorProduct.reindex_tprod]
    rw [hre, toFinsuppAux_basis, toFinsuppAux_basis]
    congr 1
    exact Quotient.sound ⟨σ, by funext i; simp⟩
  exact LinearMap.congr_fun h x

/-- The coordinate map descended to the symmetric power `SⁿV`. Together with `ofFinsupp` this is one
half of the isomorphism `SⁿV ≃ (Monomial n κ →₀ k)`. -/
noncomputable def toFinsupp (b : Basis κ k V) :
    SymmetricPower k (Fin n) V →ₗ[k] (Monomial n κ →₀ k) where
  toFun := AddCon.lift _ (toFinsuppAux b).toAddMonoidHom (by
    refine AddCon.addConGen_le.mpr (fun a c hac => ?_)
    cases hac with
    | perm σ f =>
      have hswap : (PiTensorProduct.tprod k fun i => f (σ i))
          = PiTensorProduct.reindex k (fun _ : Fin n => V) σ⁻¹ (PiTensorProduct.tprod k f) := by
        rw [PiTensorProduct.reindex_tprod]
        simp [Equiv.Perm.inv_def]
      change toFinsuppAux b (PiTensorProduct.tprod k f)
        = toFinsuppAux b (PiTensorProduct.tprod k fun i => f (σ i))
      rw [hswap, toFinsuppAux_reindex])
  map_add' := fun x y => by
    refine AddCon.induction_on₂ x y (fun a c => ?_)
    change toFinsuppAux b (a + c) = toFinsuppAux b a + toFinsuppAux b c
    rw [map_add]
  map_smul' := fun r x => by
    refine AddCon.induction_on x (fun a => ?_)
    change toFinsuppAux b (r • a) = r • toFinsuppAux b a
    rw [map_smul]

@[simp] lemma toFinsupp_mk (b : Basis κ k V) (x : ⨂[k] (_ : Fin n), V) :
    toFinsupp b (SymmetricPower.mk k (Fin n) V x) = toFinsuppAux b x :=
  rfl

/-- The inverse coordinate map: send the standard basis vector `single ⟦p⟧ 1` to `mk (⨂ₜ i, b(pᵢ))`
and extend linearly. -/
noncomputable def ofFinsupp (b : Basis κ k V) :
    (Monomial n κ →₀ k) →ₗ[k] SymmetricPower k (Fin n) V :=
  Finsupp.linearCombination k (monomialTensor b)

@[simp] lemma ofFinsupp_single (b : Basis κ k V) (m : Monomial n κ) (r : k) :
    ofFinsupp b (Finsupp.single m r) = r • monomialTensor b m := by
  simp only [ofFinsupp, Finsupp.linearCombination_single]

/-- **The coordinate isomorphism.** `SⁿV` is linearly isomorphic to the free module on degree-`n`
monomials, via the symmetrized-orbit coordinates. -/
noncomputable def symEquiv (b : Basis κ k V) :
    SymmetricPower k (Fin n) V ≃ₗ[k] (Monomial n κ →₀ k) :=
  LinearEquiv.ofLinear (toFinsupp b) (ofFinsupp b)
    (by
      -- `toFinsupp ∘ ofFinsupp = id` on the finsupp, checked on `single ⟦p⟧ 1`.
      apply Basis.ext (Finsupp.basisSingleOne)
      intro m
      refine Quotient.inductionOn m (fun p => ?_)
      simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, LinearMap.id_apply,
        ofFinsupp_single, one_smul]
      exact toFinsuppAux_basis b p)
    (by
      -- `ofFinsupp ∘ toFinsupp = id` on `SⁿV`, checked on `mk (tensorBasis b p)`.
      have key : (ofFinsupp b).comp (toFinsuppAux b) = SymmetricPower.mk k (Fin n) V := by
        apply Basis.ext (tensorBasis b)
        intro p
        rw [LinearMap.comp_apply, toFinsuppAux_basis, ofFinsupp_single, one_smul]
        rfl
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := (LinearMap.range_eq_top.mp (SymmetricPower.range_mk k (Fin n) V)) y
      rw [LinearMap.comp_apply, LinearMap.id_apply, toFinsupp_mk]
      exact LinearMap.congr_fun key x)

@[simp] lemma symEquiv_symm_single (b : Basis κ k V) (m : Monomial n κ) :
    (symEquiv b).symm (Finsupp.single m 1) = monomialTensor b m := by
  rw [symEquiv, LinearEquiv.ofLinear_symm_apply, ofFinsupp_single, one_smul]

/-- **The monomial basis of `SⁿV`.** Indexed by degree-`n` monomials in the chosen basis `b` of `V`,
with basis vector `⟦p⟧ ↦ mk (⨂ₜ i, b (p i))`. This is the symmetric-power analogue of
`Module.Basis.exteriorPower`, absent from Mathlib. -/
noncomputable def symmetricPowerMonomialBasis (b : Basis κ k V) :
    Basis (Monomial n κ) k (SymmetricPower k (Fin n) V) :=
  Basis.ofRepr (symEquiv b)

@[simp] lemma symmetricPowerMonomialBasis_apply (b : Basis κ k V) (m : Monomial n κ) :
    symmetricPowerMonomialBasis b m = monomialTensor b m := by
  simp only [symmetricPowerMonomialBasis, Basis.coe_ofRepr, symEquiv_symm_single]

/-- The monomial basis vector at (the class of) an index tuple `p` is the symmetric image of the
pure tensor `⨂ₜ i, b (p i)`. This is the exact form consumed by the `DiagonalCoordinate`
irreducibility criterion. -/
lemma symmetricPowerMonomialBasis_toMonomial (b : Basis κ k V) (p : Fin n → κ) :
    symmetricPowerMonomialBasis b (toMonomial p)
      = SymmetricPower.mk k (Fin n) V (tensorBasis b p) := by
  rw [symmetricPowerMonomialBasis_apply]
  rfl

end Etingof.SymmetricPowerBasis

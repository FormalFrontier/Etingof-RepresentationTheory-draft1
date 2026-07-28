import Mathlib
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

/-!
# Problem 2.5.2: Cyclic vectors and cyclic representations

Let `V ≠ 0` be a representation of `A`. A vector `v ∈ V` is **cyclic** if it generates `V`, i.e.
`Av = V`. A representation admitting a cyclic vector is **cyclic**. The problem asks to show:

* **(a)** `V` is irreducible if and only if all nonzero vectors of `V` are cyclic.
* **(b)** `V` is cyclic if and only if it is isomorphic to `A/I`, where `I` is a left ideal in `A`.
* **(c)** Give an example of an indecomposable representation which is not cyclic.

## Formalization

A vector `v` is cyclic when `Submodule.span A {v} = ⊤` (the `A`-submodule it generates is all of
`V`). Irreducibility is `IsSimpleModule A V`. Left ideals of `A` are `Submodule A A`, and `A/I` is
the quotient module.

Parts (a) and (b) are `irreducible_iff_forall_cyclic` and `cyclic_iff_isoQuotient`
respectively.

Part (c) follows the textbook hint verbatim. The coregular representation of a `k`-algebra `A` —
the linear dual `A^*` with the action `(ρ(a)f)(b) = f(ba)` — is `Etingof.Coregular k A`, defined
below for an arbitrary algebra. The example itself lives in the `PartC` namespace: `PartC.A` is the
three-dimensional algebra `ℂ[x, y]/I₂`, and `PartC.V = Coregular ℂ PartC.A` is shown to be
indecomposable (`PartC.isIndecomposable`) but not cyclic (`PartC.not_cyclic`).
-/

namespace Etingof

/-! ## The coregular representation

The hint to part (c) uses the **coregular** representation of an algebra `A` over a commutative
ring `k`: the linear dual `A^* = A →ₗ[k] k`, with `A` acting by `(a • f) b = f (b * a)`. This is a
left `A`-module for any `A` (the reversal in `f (b * a)` converts the right regular action into a
left one), and is not in Mathlib as of v4.28.
-/

/-- The **coregular representation** of a `k`-algebra `A`: the linear dual `A^* = A →ₗ[k] k`, with
`A` acting by `(a • f) b = f (b * a)`. Etingof, Problem 2.5.2(c) (hint). -/
def Coregular (k A : Type*) [CommRing k] [Ring A] [Algebra k A] : Type _ := Module.Dual k A

namespace Coregular

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

instance : AddCommGroup (Coregular k A) := inferInstanceAs (AddCommGroup (Module.Dual k A))

instance : Module k (Coregular k A) := inferInstanceAs (Module k (Module.Dual k A))

/-- `Coregular k A` is definitionally the dual space `A →ₗ[k] k`; this records the identification
as a `k`-linear equivalence, and is how elements are evaluated. -/
def toDual : Coregular k A ≃ₗ[k] Module.Dual k A := LinearEquiv.refl k _

@[ext]
theorem ext {f g : Coregular k A} (h : ∀ a, toDual f a = toDual g a) : f = g :=
  toDual.injective (LinearMap.ext h)

instance : SMul A (Coregular k A) where
  smul a f := toDual.symm ((toDual f).comp (LinearMap.mulRight k a))

@[simp]
theorem toDual_smul (a : A) (f : Coregular k A) (b : A) :
    toDual (a • f) b = toDual f (b * a) := rfl

@[simp]
theorem toDual_add (f g : Coregular k A) (b : A) :
    toDual (f + g) b = toDual f b + toDual g b := rfl

@[simp]
theorem toDual_zero (b : A) : toDual (0 : Coregular k A) b = 0 := rfl

@[simp]
theorem toDual_kSMul (c : k) (f : Coregular k A) (b : A) :
    toDual (c • f) b = c • toDual f b := rfl

instance : Module A (Coregular k A) where
  one_smul f := by ext b; simp
  mul_smul a a' f := by ext b; simp [mul_assoc]
  smul_zero a := by ext b; simp
  smul_add a f g := by ext b; simp
  add_smul a a' f := by ext b; simp [mul_add]
  zero_smul f := by ext b; simp

instance : IsScalarTower k A (Coregular k A) where
  smul_assoc c a f := by
    ext b
    rw [toDual_kSMul, toDual_smul, toDual_smul, mul_smul_comm, map_smul]

instance : SMulCommClass k A (Coregular k A) where
  smul_comm c a f := by ext b; simp

/-- A `k`-multiple of an element of an `A`-submodule of the coregular module stays in it. -/
theorem smul_mem_of_mem {W : Submodule A (Coregular k A)} (c : k) {w : Coregular k A}
    (hw : w ∈ W) : c • w ∈ W := by
  rw [← algebraMap_smul A c w]
  exact W.smul_mem _ hw

end Coregular

end Etingof

namespace Etingof.Problem2_5_2

section PartsAB

variable {A : Type*} [Ring A]

/-- A vector is **cyclic** when the `A`-submodule it generates is the whole representation.
Etingof, Problem 2.5.2. -/
def IsCyclicVector {V : Type*} [AddCommGroup V] [Module A V] (v : V) : Prop :=
  Submodule.span A {v} = ⊤

/-- A representation is **cyclic** when it admits a cyclic vector. Etingof, Problem 2.5.2. -/
def IsCyclic (V : Type*) [AddCommGroup V] [Module A V] : Prop :=
  ∃ v : V, IsCyclicVector (A := A) v

/-- **Problem 2.5.2(a).** A nonzero representation `V` is irreducible if and only if every nonzero
vector of `V` is cyclic (generates `V`). -/
theorem irreducible_iff_forall_cyclic (V : Type*) [AddCommGroup V] [Module A V] [Nontrivial V] :
    IsSimpleModule A V ↔ ∀ v : V, v ≠ 0 → IsCyclicVector (A := A) v := by
  change IsSimpleModule A V ↔ ∀ v : V, v ≠ 0 → Submodule.span A {v} = ⊤
  constructor
  · -- A simple module: any nonzero `v` spans a nonzero submodule, hence all of `V`.
    intro h v hv
    rcases h.eq_bot_or_eq_top (Submodule.span A {v}) with hbot | htop
    · exfalso
      have hmem : v ∈ Submodule.span A {v} := Submodule.mem_span_singleton_self v
      rw [hbot, Submodule.mem_bot] at hmem
      exact hv hmem
    · exact htop
  · -- Every nonzero submodule contains a nonzero vector, whose span is `⊤`; so it is `⊤`.
    intro h
    exact
      { eq_bot_or_eq_top := fun p => by
          rcases eq_or_ne p ⊥ with hp | hp
          · exact Or.inl hp
          · refine Or.inr ?_
            obtain ⟨v, hvp, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
            have hspan : Submodule.span A {v} = ⊤ := h v hv0
            have hle : Submodule.span A {v} ≤ p :=
              Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvp)
            rw [hspan] at hle
            exact top_le_iff.mp hle }

/-- **Problem 2.5.2(b).** A nonzero representation `V` is cyclic (admits a cyclic vector) if and
only if it is isomorphic to `A/I` for some left ideal `I` of `A`. -/
theorem cyclic_iff_isoQuotient (V : Type*) [AddCommGroup V] [Module A V] [Nontrivial V] :
    IsCyclic (A := A) V ↔
      ∃ I : Submodule A A, Nonempty (V ≃ₗ[A] (A ⧸ I)) := by
  change (∃ v : V, Submodule.span A {v} = ⊤) ↔
    ∃ I : Submodule A A, Nonempty (V ≃ₗ[A] (A ⧸ I))
  constructor
  · -- A cyclic vector `v` makes `a ↦ a • v` a surjection `A → V`; quotient by its kernel.
    rintro ⟨v, hv⟩
    set f := LinearMap.toSpanSingleton A V v with hf
    have hrange : LinearMap.range f = ⊤ := by
      rw [hf, ← LinearMap.span_singleton_eq_range]; exact hv
    have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hrange
    exact ⟨LinearMap.ker f, ⟨(LinearMap.quotKerEquivOfSurjective f hsurj).symm⟩⟩
  · -- `A/I` is cyclic (generated by the class of `1`); transport along the equivalence.
    rintro ⟨I, ⟨e⟩⟩
    have h1 : Submodule.span A {(I.mkQ 1 : A ⧸ I)} = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨a, rfl⟩ := I.mkQ_surjective x
      rw [Submodule.mem_span_singleton]
      refine ⟨a, ?_⟩
      rw [← map_smul]; congr 1; simp
    refine ⟨e.symm (I.mkQ 1), ?_⟩
    have hmap : Submodule.span A {e.symm (I.mkQ 1)}
        = Submodule.map e.symm.toLinearMap (Submodule.span A {I.mkQ 1}) := by
      rw [Submodule.map_span]; simp
    rw [hmap, h1, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.symm.surjective

end PartsAB

/-! ## Part (c): an indecomposable representation that is not cyclic

Following the hint, let `A = ℂ[x, y]/I₂` with `I₂` the ideal spanned by the homogeneous
polynomials of degree `≥ 2`, so that `A` has basis `1, x, y` and `x² = xy = y² = 0`. We model `A`
as the trivial square-zero extension `TrivSqZeroExt ℂ (Fin 2 → ℂ)`, whose elements are pairs
`(c, m)` with `(c, m) * (c', m') = (c c', c • m' + c' • m)`; `algEquiv` identifies it with the
literal quotient `MvPolynomial (Fin 2) ℂ ⧸ I₂`.

The two computations that drive everything are:

* `mul_eq_smul_add`: `b * a = a.fst • b + b.fst • inr a.snd`, and hence
* `smul_eq`: `a • f = a.fst • f + f (inr a.snd) • ε` in `V = A^*`, where `ε : V` is the functional
  `a ↦ a.fst` picking out the coefficient of `1`.

The second formula says that `A • f` lies in the plane spanned by `f` and `ε`, which is a proper
subspace of the three-dimensional `V` — so no `f` is cyclic. It also says that the image of the
maximal ideal `m = span{x, y}` acting on `V` is exactly the line `ℂ ε`, so every nonzero
`A`-submodule of `V` contains `ε` and no two of them can be complementary.
-/

namespace PartC

open TrivSqZeroExt MvPolynomial

/-- The algebra `A = ℂ[x, y]/I₂` of the hint, modelled as the trivial square-zero extension of
`ℂ` by a two-dimensional space. Compare `algEquiv`, which identifies it with the literal
quotient of `ℂ[x, y]`. -/
abbrev A : Type := TrivSqZeroExt ℂ (Fin 2 → ℂ)

/-- The image of `x` in `A = ℂ[x, y]/I₂`. -/
noncomputable def x : A := inr (Pi.single 0 1)

/-- The image of `y` in `A = ℂ[x, y]/I₂`. -/
noncomputable def y : A := inr (Pi.single 1 1)

@[simp] theorem x_mul_x : x * x = 0 := by simp [x, inr_mul_inr]
@[simp] theorem x_mul_y : x * y = 0 := by simp [x, y, inr_mul_inr]
@[simp] theorem y_mul_x : y * x = 0 := by simp [x, y, inr_mul_inr]
@[simp] theorem y_mul_y : y * y = 0 := by simp [y, inr_mul_inr]

/-- `A` is `ℂ × ℂ²` as a vector space. -/
noncomputable def prodEquiv : A ≃ₗ[ℂ] ℂ × (Fin 2 → ℂ) where
  toFun a := (a.fst, a.snd)
  invFun p := (p.1, p.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : Module.Finite ℂ A := Module.Finite.equiv prodEquiv.symm

theorem finrank_A : Module.finrank ℂ A = 3 := by
  rw [prodEquiv.finrank_eq]; simp

theorem linearIndependent_one_x_y : LinearIndependent ℂ ![(1 : A), x, y] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, x, y] at hg
  rw [TrivSqZeroExt.ext_iff] at hg
  obtain ⟨h1, h2⟩ := hg
  simp only [Fin.isValue, fst_add, fst_smul, fst_one, smul_eq_mul, mul_one, fst_inr,
    mul_zero, add_zero, fst_zero] at h1
  have e0 := congrFun h2 0
  have e1 := congrFun h2 1
  simp only [Fin.isValue, snd_add, snd_smul, snd_one, smul_zero, snd_inr, zero_add,
    Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ne_eq, zero_ne_one,
    not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, snd_zero, Pi.zero_apply,
    one_ne_zero] at e0 e1
  fin_cases i
  · exact h1
  · exact e0
  · exact e1

/-- **The basis `1, x, y` of `A = ℂ[x, y]/I₂`.** -/
noncomputable def basis : Module.Basis (Fin 3) ℂ A :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_one_x_y (by simp [finrank_A])

@[simp] theorem coe_basis : ⇑basis = ![(1 : A), x, y] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-! ### Identification with the literal quotient `ℂ[x, y]/I₂` -/

/-- The ideal `I₂ ⊆ ℂ[x, y]` spanned by the homogeneous polynomials of degree `≥ 2`, presented by
its generators `xᵢxⱼ`. -/
noncomputable def I₂ : Ideal (MvPolynomial (Fin 2) ℂ) :=
  Ideal.span (Set.range fun p : Fin 2 × Fin 2 => X p.1 * X p.2)

/-- The quadratic-generator presentation of `I₂` is the square of the ideal generated by the
variables. This is the bridge from the convenient presentation used in the construction to the
book's description by all terms of degree at least two. -/
theorem I₂_eq_idealOfVars_sq :
    I₂ = MvPolynomial.idealOfVars (Fin 2) ℂ ^ 2 := by
  rw [I₂, pow_two, MvPolynomial.idealOfVars, Ideal.span_mul_span']
  congr 1
  ext p
  simp [Set.mem_mul]

/-- The ideal `I₂` is exactly the ideal spanned by all homogeneous polynomials of degree at
least two, as stated in the textbook hint. -/
theorem I₂_eq_span_homogeneous_ge_two :
    I₂ = Ideal.span {p : MvPolynomial (Fin 2) ℂ |
      ∃ d : ℕ, 2 ≤ d ∧ p.IsHomogeneous d} := by
  apply le_antisymm
  · rw [I₂, Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    apply Ideal.subset_span
    exact ⟨2, le_rfl, by simpa using (isHomogeneous_X ℂ i).mul (isHomogeneous_X ℂ j)⟩
  · rw [Ideal.span_le]
    rintro p ⟨d, hd, hp⟩
    rw [I₂_eq_idealOfVars_sq]
    apply (MvPolynomial.mem_pow_idealOfVars_iff 2 p).2
    intro s hs
    have hsd : Finsupp.degree s = d := by
      simpa [MvPolynomial.IsHomogeneous, Finsupp.degree_eq_weight_one, Pi.one_def] using
        hp (MvPolynomial.mem_support_iff.mp hs)
    exact hsd.symm ▸ hd

theorem mk_X_mul_X (i j : Fin 2) :
    (Ideal.Quotient.mk I₂ (X i * X j) : MvPolynomial (Fin 2) ℂ ⧸ I₂) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.subset_span ⟨(i, j), rfl⟩

/-- The linear map `(m₀, m₁) ↦ [m₀ x + m₁ y]` into `ℂ[x, y]/I₂`. -/
noncomputable def linPart : (Fin 2 → ℂ) →ₗ[ℂ] MvPolynomial (Fin 2) ℂ ⧸ I₂ :=
  ∑ i : Fin 2, (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ).smulRight
    (Ideal.Quotient.mk I₂ (X i) : MvPolynomial (Fin 2) ℂ ⧸ I₂)

theorem linPart_apply (m : Fin 2 → ℂ) :
    linPart m = ∑ i : Fin 2, m i • (Ideal.Quotient.mk I₂ (X i) : MvPolynomial (Fin 2) ℂ ⧸ I₂) := by
  simp [linPart]

theorem linPart_mul_linPart (m n : Fin 2 → ℂ) : linPart m * linPart n = 0 := by
  simp only [linPart_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm,
    ← map_mul, mk_X_mul_X, smul_zero, Finset.sum_const_zero]

/-- `A → ℂ[x, y]/I₂`. -/
noncomputable def toQuot : A →ₐ[ℂ] MvPolynomial (Fin 2) ℂ ⧸ I₂ :=
  TrivSqZeroExt.liftEquivOfComm ⟨linPart, linPart_mul_linPart⟩

/-- `ℂ[x, y]/I₂ → A`. -/
noncomputable def ofQuot : (MvPolynomial (Fin 2) ℂ ⧸ I₂) →ₐ[ℂ] A :=
  Ideal.Quotient.liftₐ I₂ (aeval fun i => (inr (Pi.single i 1) : A)) (by
    intro p hp
    refine Submodule.span_induction ?_ (by simp) (by intros; simp_all) (by intros; simp_all) hp
    rintro _ ⟨⟨i, j⟩, rfl⟩
    simp [inr_mul_inr])

@[simp] theorem toQuot_inr (m : Fin 2 → ℂ) : toQuot (inr m) = linPart m := by
  simp [toQuot]

@[simp] theorem ofQuot_mk_X (i : Fin 2) :
    ofQuot (Ideal.Quotient.mk I₂ (X i)) = (inr (Pi.single i 1) : A) := by
  simp [ofQuot]

theorem ofQuot_comp_toQuot : ofQuot.comp toQuot = AlgHom.id ℂ A := by
  apply TrivSqZeroExt.algHom_ext
  intro m
  rw [AlgHom.comp_apply, toQuot_inr, linPart_apply, map_sum]
  simp only [map_smul, ofQuot_mk_X, ← inr_smul, ← inr_sum, AlgHom.id_apply]
  congr 1
  funext i
  fin_cases i <;> simp [Fin.sum_univ_two]

theorem toQuot_comp_ofQuot :
    toQuot.comp ofQuot = AlgHom.id ℂ (MvPolynomial (Fin 2) ℂ ⧸ I₂) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp [toQuot, ofQuot, linPart_apply]

/-- **The model is `ℂ[x, y]/I₂`.** The trivial square-zero extension `A` is isomorphic, as a
`ℂ`-algebra, to the quotient of `ℂ[x, y]` by the ideal generated by the quadratic monomials. -/
noncomputable def algEquiv : A ≃ₐ[ℂ] MvPolynomial (Fin 2) ℂ ⧸ I₂ :=
  AlgEquiv.ofAlgHom toQuot ofQuot toQuot_comp_ofQuot ofQuot_comp_toQuot

@[simp] theorem algEquiv_x : algEquiv x = Ideal.Quotient.mk I₂ (X 0) := by
  simp [algEquiv, x, linPart_apply]

@[simp] theorem algEquiv_y : algEquiv y = Ideal.Quotient.mk I₂ (X 1) := by
  simp [algEquiv, y, linPart_apply]

/-! ### The coregular module `V = A^*` -/

/-- The coregular representation `V = A^*` of the hint: `(ρ(a)f)(b) = f(ba)`. -/
abbrev V : Type := Etingof.Coregular ℂ A

/-- Multiplication in `A`, in the form needed below: `b * a` is `a.fst` times `b`, corrected by a
multiple of the "linear part" of `a`. -/
theorem mul_eq_smul_add (a b : A) : b * a = a.fst • b + b.fst • (inr a.snd : A) := by
  ext
  · simp [mul_comm]
  · simp [mul_comm, add_comm]

/-- `ε : V` is the functional reading off the coefficient of `1`, i.e. the counit `A → A/m = ℂ`.
It spans the socle of `V`. -/
noncomputable def ε : V :=
  Etingof.Coregular.toDual.symm (TrivSqZeroExt.fstHom ℂ ℂ (Fin 2 → ℂ)).toLinearMap

@[simp] theorem toDual_ε (a : A) : Etingof.Coregular.toDual ε a = a.fst := rfl

/-- **The key computation.** Acting by `a` on `f ∈ A^*` gives `a.fst • f` plus a multiple of `ε`.
In particular `A • f ⊆ ℂ f + ℂ ε`, and `m • f ⊆ ℂ ε` for `a` in the maximal ideal. -/
theorem smul_eq (a : A) (f : V) :
    a • f = a.fst • f + (Etingof.Coregular.toDual f (inr a.snd)) • ε := by
  ext b
  rw [Etingof.Coregular.toDual_smul, mul_eq_smul_add]
  simp [mul_comm]

instance : Module.Finite ℂ V := Module.Finite.equiv Etingof.Coregular.toDual.symm

theorem finrank_V : Module.finrank ℂ V = 3 := by
  rw [Etingof.Coregular.toDual.finrank_eq, Subspace.dual_finrank_eq, finrank_A]

theorem ε_ne_zero : ε ≠ (0 : V) := by
  intro h
  have h1 : Etingof.Coregular.toDual ε (1 : A) = 0 := by rw [h]; rfl
  rw [toDual_ε] at h1
  simp at h1

instance : Nontrivial V := ⟨⟨ε, 0, ε_ne_zero⟩⟩

/-! ### `V` is not cyclic -/

/-- The plane `ℂ f + ℂ ε` inside `V`, presented as the range of a map from a two-dimensional
space so that its dimension is visibly at most `2`. -/
noncomputable def plane (f : V) : (ℂ × ℂ) →ₗ[ℂ] V :=
  (LinearMap.fst ℂ ℂ ℂ).smulRight f + (LinearMap.snd ℂ ℂ ℂ).smulRight ε

theorem span_subset_plane (f : V) :
    (Submodule.span A {f} : Set V) ⊆ LinearMap.range (plane f) := by
  intro g hg
  rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hg
  obtain ⟨a, rfl⟩ := hg
  exact ⟨(a.fst, Etingof.Coregular.toDual f (inr a.snd)), by simp [plane, smul_eq]⟩

/-- **Problem 2.5.2(c), first half.** No vector of `V = A^*` is cyclic: `A • f` is contained in the
plane spanned by `f` and `ε`, whereas `V` is three-dimensional. -/
theorem not_cyclic (f : V) : Submodule.span A {f} ≠ ⊤ := by
  intro h
  have hrange : LinearMap.range (plane f) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact span_subset_plane f (by rw [h]; trivial)
  have h1 : Module.finrank ℂ V ≤ 2 := by
    have h2 := LinearMap.finrank_range_le (plane f)
    rw [hrange, finrank_top] at h2
    simpa using h2
  rw [finrank_V] at h1
  omega

/-- `V` is not a cyclic representation. -/
theorem not_isCyclic : ¬ IsCyclic (A := A) V := by
  rw [IsCyclic]
  rintro ⟨f, hf⟩
  exact not_cyclic f hf

/-! ### `V` is indecomposable -/

/-- A functional killing the maximal ideal `m = span{x, y}` is a multiple of `ε`; equivalently the
socle of `V` is the line `ℂ ε`. -/
theorem eq_smul_ε {g : V} (hm : ∀ m : Fin 2 → ℂ, Etingof.Coregular.toDual g (inr m) = 0) :
    g = (Etingof.Coregular.toDual g 1) • ε := by
  ext b
  conv_lhs => rw [← inl_fst_add_inr_snd_eq b]
  rw [map_add, hm, add_zero, ← algebraMap_eq_inl, Algebra.algebraMap_eq_smul_one, map_smul]
  simp [mul_comm]

/-- **Every nonzero submodule of `V` contains `ε`.** Either `g` is killed by the maximal ideal, and
is then itself a nonzero multiple of `ε`, or some `a ∈ m` has `a • g = (g a) • ε ≠ 0`. -/
theorem ε_mem {W : Submodule A V} (hW : W ≠ ⊥) : ε ∈ W := by
  obtain ⟨g, hgW, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  by_cases hm : ∀ m : Fin 2 → ℂ, Etingof.Coregular.toDual g (inr m) = 0
  · set c := Etingof.Coregular.toDual g 1 with hc_def
    have hg : g = c • ε := eq_smul_ε hm
    have hc : c ≠ 0 := fun h0 => hg0 (by rw [hg, h0, zero_smul])
    have h3 : c⁻¹ • g ∈ W := Etingof.Coregular.smul_mem_of_mem _ hgW
    rwa [hg, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
  · push Not at hm
    obtain ⟨m, hmne⟩ := hm
    set c := Etingof.Coregular.toDual g (inr m) with hc_def
    have hmem : (inr m : A) • g ∈ W := W.smul_mem _ hgW
    rw [smul_eq] at hmem
    simp only [fst_inr, snd_inr, zero_smul, zero_add, ← hc_def] at hmem
    have h3 : c⁻¹ • (c • ε) ∈ W := Etingof.Coregular.smul_mem_of_mem _ hmem
    rwa [smul_smul, inv_mul_cancel₀ hmne, one_smul] at h3

/-- **Problem 2.5.2(c), second half.** `V = A^*` is indecomposable: two complementary submodules
would both have to contain `ε`, contradicting disjointness. -/
theorem isIndecomposable : Etingof.IsIndecomposable A V := by
  refine ⟨inferInstance, fun W₁ W₂ hc => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact ε_ne_zero
    (by simpa using hc.disjoint.le_bot (⟨ε_mem h1, ε_mem h2⟩ : ε ∈ W₁ ⊓ W₂))

/-- **Problem 2.5.2(c).** The coregular representation `V = A^*` of `A = ℂ[x, y]/I₂` is an
indecomposable representation which is not cyclic. -/
theorem indecomposable_not_cyclic :
    Etingof.IsIndecomposable A V ∧ ¬ IsCyclic (A := A) V :=
  ⟨isIndecomposable, not_isCyclic⟩

/-! ### Non-vacuity checks -/

-- The representation is genuinely three-dimensional, so "not cyclic" is not a statement about
-- the zero module.
example : Module.finrank ℂ V = 3 := finrank_V

-- The algebra really is `ℂ[x, y]/I₂`, with `x` and `y` linearly independent modulo the constants.
example : x ≠ y := by
  intro h
  have := congrFun (congrArg TrivSqZeroExt.snd h) 0
  simp [x, y] at this

-- Part (a) applies: `V` is not irreducible, since `ε` is not cyclic.
example : ¬ IsSimpleModule A V := by
  rw [irreducible_iff_forall_cyclic]
  push Not
  exact ⟨ε, ε_ne_zero, not_cyclic ε⟩

end PartC

end Etingof.Problem2_5_2

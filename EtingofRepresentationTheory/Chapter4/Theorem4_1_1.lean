import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Theorem 4.1.1: Maschke's Theorem

**Maschke's theorem.** Let G be a finite group and k a field whose characteristic does
not divide |G|. Then:

(i) The group algebra k[G] is semisimple.

(ii) There is an isomorphism k[G] ≅ ⊕ᵢ End(Vᵢ), where Vᵢ are all the irreducible
representations of G. Moreover, the regular representation decomposes as
k[G] ≅ ⊕ᵢ Vᵢ^(dim Vᵢ), giving the dimension formula |G| = Σᵢ (dim Vᵢ)².

## Mathlib correspondence

Mathlib has `IsSemisimpleRing` and `MonoidAlgebra.instIsSemisimpleRing` for part (i).
Part (i) is `Etingof.Theorem4_1_1_semisimple`. Part (ii) is formalized in several forms:
`Etingof.Theorem4_1_1_algebra_iso` gives the full content: the family of irreducible
representations together with the algebra isomorphism `k[G] ≃ₐ[k] ⊕ᵢ End(Vᵢ)` and the
sum-of-squares formula, while `Etingof.Theorem4_1_1_sum_of_squares` records only the
dimension identity `Σᵢ (dim Vᵢ)² = |G|`. `Etingof.Theorem4_1_1_regularRep_iso` upgrades the
algebra isomorphism to an isomorphism of representations `k[G] ≅ ∏ᵢ End(Vᵢ)`, and
`Etingof.Theorem4_1_1_regularRep_isotypic` records the book's final display, the explicit
isotypic decomposition `k[G] ≅ ⊕ᵢ (dim Vᵢ) · Vᵢ`.
-/

open CategoryTheory

universe u

/-- Maschke's theorem, part (i): The group algebra k[G] is semisimple when the
characteristic of k does not divide |G|. (Etingof Theorem 4.1.1) -/
theorem Etingof.Theorem4_1_1_semisimple
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    (h : IsUnit (Fintype.card G : k)) :
    IsSemisimpleRing (MonoidAlgebra k G) := by
  haveI : NeZero (Nat.card G : k) := by
    rw [neZero_iff]
    rw [Fintype.card_eq_nat_card] at h
    exact h.ne_zero
  infer_instance

/-- Maschke's theorem, part (ii): the sum-of-squares formula `|G| = Σᵢ (dim Vᵢ)²`.

Over an algebraically closed field `k` with `char k ∤ |G|`, the Wedderburn-Artin
decomposition `k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k` exhibits the
irreducible representations as the column-vector modules of the matrix blocks,
with `d i` their dimensions. Comparing `k`-dimensions on both sides gives
`Σᵢ (d i)² = |G|`. The decomposition data is packaged by `IrrepDecomp` and the
dimension identity is `IrrepDecomp.sum_sq_eq_card`. -/
theorem Etingof.Theorem4_1_1_sum_of_squares
    (k : Type u) (G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ),
      (∀ i, NeZero (d i)) ∧ ∑ i, (d i) ^ 2 = Fintype.card G :=
  let D : IrrepDecomp k G := IrrepDecomp.mk'
  ⟨D.n, D.d, D.d_pos, D.sum_sq_eq_card⟩

/-- Maschke's theorem, part (ii), **algebra-isomorphism form**.

The full content of part (ii): there is a finite family `V : Fin n → FDRep k G` of the
irreducible representations of `G`, each `Simple`, pairwise non-isomorphic, and complete
(every simple `FDRep` is isomorphic to one of them), together with an isomorphism of
`k`-algebras

  `ψ : k[G] ≃ₐ[k] ⊕ᵢ End(Vᵢ)`,

which is the book's `ψ : k[G] → ⊕ᵢ End(Vᵢ)`, `g ↦ ⊕ᵢ g|_{Vᵢ}`. Comparing dimensions on
the two sides yields the sum-of-squares formula `Σᵢ (dim Vᵢ)² = |G|`.

This statement surfaces the algebra isomorphism and the irreducible enumeration that the
weaker `Etingof.Theorem4_1_1_sum_of_squares` (which only records the dimension identity)
leaves implicit. The representations `Vᵢ` are the column-vector representations of the
Wedderburn-Artin decomposition (`IrrepDecomp.columnFDRep`), and `ψ` is `IrrepDecomp.endIso`,
the Wedderburn-Artin isomorphism with each matrix block read as `End(Vᵢ)`. -/
theorem Etingof.Theorem4_1_1_algebra_iso
    (k : Type u) (G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ W : FDRep k G, Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Module.End k (V i)) ∧
      ∑ i, Module.finrank k (V i) ^ 2 = Fintype.card G :=
  let D : IrrepDecomp k G := IrrepDecomp.mk'
  ⟨D.n, D.columnFDRep, D.columnFDRep_simple, D.columnFDRep_injective,
    D.columnFDRep_surjective, ⟨D.endIso⟩,
    D.sum_finrank_sq_eq_card D.columnFDRep D.columnFDRep_simple D.columnFDRep_injective⟩

/-! ### Representation-level form of part (ii)

The book's part (ii) states that `ψ : k[G] → ⊕ᵢ End(Vᵢ)` is not merely an isomorphism of
`k`-algebras but an isomorphism of representations of `G`, where `G` acts on both sides by
left multiplication. On `k[G]` this is the regular representation `g · x = (of g) * x`; on
`⊕ᵢ End(Vᵢ)` it is `g · (fᵢ) = (ρᵢ(g) ∘ fᵢ)`, i.e. left multiplication by `ψ(g) = ⊕ᵢ ρᵢ(g)`.
The results below package the regular representation as an `FDRep`, equip `∏ᵢ End(Vᵢ)` with this
left-multiplication `G`-action, and upgrade the Wedderburn algebra isomorphism `IrrepDecomp.endIso`
to an isomorphism of representations. -/

/-- The **regular representation** of `G` on the group algebra `k[G]`: `g` acts by left
multiplication `x ↦ (of g) * x`. This is the left-hand side of the book's `ψ`, viewed as a
representation of `G`. -/
noncomputable def MonoidAlgebra.regularRep (k G : Type u) [Field k] [Group G] :
    Representation k G (MonoidAlgebra k G) where
  toFun g := Algebra.lmul k (MonoidAlgebra k G) (MonoidAlgebra.of k G g)
  map_one' := by rw [map_one, map_one]
  map_mul' g h := by rw [map_mul, map_mul]

@[simp]
theorem MonoidAlgebra.regularRep_apply (k G : Type u) [Field k] [Group G]
    (g : G) (x : MonoidAlgebra k G) :
    MonoidAlgebra.regularRep k G g x = MonoidAlgebra.of k G g * x := rfl

/-- The regular representation packaged as a finite-dimensional representation `FDRep k G`. -/
noncomputable def MonoidAlgebra.regularFDRep (k G : Type u) [Field k] [Group G] [Fintype G] :
    FDRep k G :=
  FDRep.of (MonoidAlgebra.regularRep k G)

namespace IrrepDecomp

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [NeZero (Nat.card G : k)]

/-- The **endomorphism-algebra representation**: `∏ᵢ End(Vᵢ)` viewed as a representation of `G`,
where `g` acts by left multiplication by `ψ(g) = ⊕ᵢ ρᵢ(g)` in the product algebra. This is the
right-hand side of the book's `ψ` as a representation of `G`; `endRegRep_apply` certifies that the
action is componentwise post-composition `fᵢ ↦ ρᵢ(g) ∘ fᵢ`. -/
noncomputable def endRegRep (D : IrrepDecomp k G) :
    Representation k G (Π i, Module.End k (D.columnFDRep i)) where
  toFun g := Algebra.lmul k _ (D.endIso (MonoidAlgebra.of k G g))
  map_one' := by rw [map_one, map_one, map_one]
  map_mul' g h := by rw [map_mul, map_mul, map_mul]

/-- The `i`-th component of `ψ(g) = endIso (of g)` is exactly the action `ρᵢ(g)` of `g` on the
`i`-th irreducible representation `Vᵢ = columnFDRep i`. -/
theorem endIso_of_apply (D : IrrepDecomp k G) (g : G) (i : Fin D.n) :
    D.endIso (MonoidAlgebra.of k G g) i = (D.columnFDRep i).ρ g := by
  have hproj : (D.iso (MonoidAlgebra.of k G g)) i = D.projRingHom i (MonoidAlgebra.of k G g) := rfl
  have : D.endIso (MonoidAlgebra.of k G g) i =
      Matrix.toLinAlgEquiv' (D.projRingHom i (MonoidAlgebra.of k G g)) := by
    rw [← hproj]; rfl
  rw [this]
  ext v
  rw [Matrix.toLinAlgEquiv'_apply]
  rfl

/-- The `G`-action of `endRegRep` is componentwise post-composition by `ρᵢ(g)`: for `F = (fᵢ)`,
`(g · F)ᵢ = ρᵢ(g) ∘ fᵢ`. This certifies `endRegRep` is a faithful rendering of `⊕ᵢ End(Vᵢ)` with
its natural left-multiplication `G`-action. -/
theorem endRegRep_apply (D : IrrepDecomp k G) (g : G)
    (F : Π i, Module.End k (D.columnFDRep i)) (i : Fin D.n) :
    D.endRegRep g F i = (D.columnFDRep i).ρ g ∘ₗ F i := by
  change (D.endIso (MonoidAlgebra.of k G g) * F) i = (D.columnFDRep i).ρ g ∘ₗ F i
  rw [Pi.mul_apply, D.endIso_of_apply g i]
  rfl

/-- The Wedderburn algebra isomorphism `endIso` intertwines the regular representation with the
left-multiplication action on `∏ᵢ End(Vᵢ)`: `ψ((of g) * x) = ψ(g) * ψ(x)`. -/
theorem endIso_regularRep_comm (D : IrrepDecomp k G) (g : G) :
    D.endIso.toLinearEquiv.toLinearMap ∘ₗ (MonoidAlgebra.regularRep k G) g =
      D.endRegRep g ∘ₗ D.endIso.toLinearEquiv.toLinearMap := by
  refine LinearMap.ext fun x => ?_
  exact map_mul D.endIso (MonoidAlgebra.of k G g) x

/-- `∏ᵢ End(Vᵢ)` with the left-multiplication `G`-action, packaged as an `FDRep k G`. -/
noncomputable def endRegFDRep (D : IrrepDecomp k G) : FDRep k G :=
  FDRep.of D.endRegRep

/-- **Equivariant Wedderburn isomorphism.** The regular representation `k[G]` is isomorphic, as a
representation of `G`, to `∏ᵢ End(Vᵢ)` with the left-multiplication action. This upgrades the
algebra isomorphism `endIso` of `Theorem4_1_1_algebra_iso` to an isomorphism in `FDRep k G`. -/
noncomputable def regularIso (D : IrrepDecomp k G) :
    MonoidAlgebra.regularFDRep k G ≅ D.endRegFDRep :=
  Action.mkIso D.endIso.toLinearEquiv.toFGModuleCatIso (fun g => by
    ext : 1
    exact D.endIso_regularRep_comm g)

/-! ### Isotypic decomposition `k[G] ≅ ⨁ᵢ Vᵢ^(dim Vᵢ)`

The book's final display for part (ii) reads the equivariant Wedderburn isomorphism as an explicit
decomposition of the regular representation into irreducibles with multiplicities:
`k[G] ≅ ⊕ᵢ (dim Vᵢ) · Vᵢ`. This is obtained from `regularIso` by decomposing each summand
`End(Vᵢ)`, carrying the left-multiplication action `f ↦ ρᵢ(g) ∘ f`, into `dim Vᵢ` copies of `Vᵢ`:
post-composition acts within each "column" `f ↦ f(eⱼ)`, so `End(Vᵢ) ≅ ⊕_{Fin (dᵢ)} Vᵢ` as
representations. Assembling over `i` gives `∏ᵢ End(Vᵢ) ≅ ∏ᵢ Vᵢ^(dᵢ)`. -/

/-- The **isotypic multiplicity representation** `∏ᵢ Vᵢ^(dᵢ)`: for each irreducible
`Vᵢ = columnFDRep i` of dimension `dᵢ`, take `dᵢ` copies indexed by `Fin (D.d i)`, with `G` acting
diagonally `(g · w) i j = ρᵢ(g) (w i j)`. This is the right-hand side of the book's decomposition
`k[G] ≅ ⊕ᵢ (dim Vᵢ) · Vᵢ`, with the action certified by `columnMultRep_apply`. -/
noncomputable def columnMultRep (D : IrrepDecomp k G) :
    Representation k G (Π i, Fin (D.d i) → (D.columnFDRep i)) where
  toFun g := LinearMap.pi fun i =>
    (((D.columnFDRep i).ρ g).compLeft (Fin (D.d i))).comp (LinearMap.proj i)
  map_one' := by
    ext w i j
    simp [map_one]
  map_mul' g h := by
    ext w i j
    simp [map_mul]

/-- The diagonal action of `columnMultRep`: on `w = (wᵢⱼ)`, `(g · w) i j = ρᵢ(g) (w i j)`. Each
index `(i, j)` (with `j : Fin (D.d i)`) is a copy of the irreducible `Vᵢ = columnFDRep i`. -/
theorem columnMultRep_apply (D : IrrepDecomp k G) (g : G)
    (w : Π i, Fin (D.d i) → (D.columnFDRep i)) (i : Fin D.n) (j : Fin (D.d i)) :
    D.columnMultRep g w i j = (D.columnFDRep i).ρ g (w i j) := rfl

/-- `∏ᵢ Vᵢ^(dᵢ)` with the diagonal `G`-action, packaged as an `FDRep k G`. -/
noncomputable def columnMultFDRep (D : IrrepDecomp k G) : FDRep k G :=
  FDRep.of D.columnMultRep

/-- The `k`-linear equivalence `∏ᵢ End(Vᵢ) ≃ ∏ᵢ Vᵢ^(dᵢ)` sending `f : End(Vᵢ)` to its columns
`j ↦ f(eⱼ)` in the standard basis `eⱼ` of `Vᵢ = Fin (D.d i) → k`. This is the underlying linear
equivalence of the isotypic decomposition; it intertwines the two `G`-actions
(`endColumnEquiv_comm`). -/
noncomputable def endColumnEquiv (D : IrrepDecomp k G) :
    (Π i, Module.End k (D.columnFDRep i)) ≃ₗ[k] (Π i, Fin (D.d i) → (D.columnFDRep i)) :=
  LinearEquiv.piCongrRight fun i =>
    ((Pi.basisFun k (Fin (D.d i))).constr (M' := (D.columnFDRep i)) k).symm

/-- `endColumnEquiv` sends `f = (fᵢ)` to the family of columns `i j ↦ fᵢ(eⱼ)`. -/
theorem endColumnEquiv_apply (D : IrrepDecomp k G)
    (F : Π i, Module.End k (D.columnFDRep i)) (i : Fin D.n) (j : Fin (D.d i)) :
    D.endColumnEquiv F i j = F i (Pi.basisFun k (Fin (D.d i)) j) := rfl

/-- The column equivalence intertwines the left-multiplication action on `∏ᵢ End(Vᵢ)`
(`endRegRep`) with the diagonal action on `∏ᵢ Vᵢ^(dᵢ)` (`columnMultRep`): the `(i,j)` column of
`ρᵢ(g) ∘ Fᵢ` is `ρᵢ(g)` applied to the `(i,j)` column of `Fᵢ`. -/
theorem endColumnEquiv_comm (D : IrrepDecomp k G) (g : G)
    (F : Π i, Module.End k (D.columnFDRep i)) :
    D.endColumnEquiv (D.endRegRep g F) = D.columnMultRep g (D.endColumnEquiv F) := by
  ext i j
  rw [columnMultRep_apply, endColumnEquiv_apply, endColumnEquiv_apply, D.endRegRep_apply]
  rfl

/-- **Isotypic decomposition of `∏ᵢ End(Vᵢ)`.** As representations of `G`, `∏ᵢ End(Vᵢ)` with the
left-multiplication action is isomorphic to `∏ᵢ Vᵢ^(dᵢ)` with the diagonal action, via the column
equivalence `endColumnEquiv`. -/
noncomputable def columnMultIso (D : IrrepDecomp k G) :
    D.endRegFDRep ≅ D.columnMultFDRep :=
  Action.mkIso D.endColumnEquiv.toFGModuleCatIso (fun g => by
    ext F
    exact D.endColumnEquiv_comm g F)

/-- **Isotypic decomposition of the regular representation.** Composing the equivariant Wedderburn
isomorphism `regularIso` with the column decomposition `columnMultIso` exhibits the book's final
form of Maschke 4.1.1(ii): `k[G] ≅ ⊕ᵢ (dim Vᵢ) · Vᵢ`. -/
noncomputable def regularColumnMultIso (D : IrrepDecomp k G) :
    MonoidAlgebra.regularFDRep k G ≅ D.columnMultFDRep :=
  D.regularIso ≪≫ D.columnMultIso

end IrrepDecomp

/-- Maschke's theorem, part (ii), **representation-isomorphism form**.

The book's part (ii) asserts that `ψ : k[G] → ⊕ᵢ End(Vᵢ)`, `g ↦ ⊕ᵢ g|_{Vᵢ}`, is an isomorphism
of representations of `G` (both sides carrying the left-multiplication action), not only of
`k`-algebras. This theorem records that content: there is a complete family `V : Fin n → FDRep k G`
of the irreducible representations of `G`, each `Simple`, pairwise non-isomorphic, exhausting the
simples, together with a representation `ρ_end` on `∏ᵢ End(Vᵢ)` whose action is
`(g · F)ᵢ = ρᵢ(g) ∘ Fᵢ`, such that the regular representation `MonoidAlgebra.regularFDRep k G` is
isomorphic in `FDRep k G` to `FDRep.of ρ_end`. The witnesses are the column-vector
representations `columnFDRep` and the
equivariant upgrade `IrrepDecomp.regularIso` of the Wedderburn isomorphism `IrrepDecomp.endIso`. -/
theorem Etingof.Theorem4_1_1_regularRep_iso (k G : Type u)
    [Field k] [IsAlgClosed k] [Group G] [Fintype G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G) (ρ_end : Representation k G (Π i, Module.End k (V i))),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ W : FDRep k G, Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      (∀ (g : G) (F : Π i, Module.End k (V i)) (i : Fin n), ρ_end g F i = (V i).ρ g ∘ₗ F i) ∧
      Nonempty (MonoidAlgebra.regularFDRep k G ≅ FDRep.of ρ_end) :=
  let D : IrrepDecomp k G := IrrepDecomp.mk'
  ⟨D.n, D.columnFDRep, D.endRegRep, D.columnFDRep_simple, D.columnFDRep_injective,
    D.columnFDRep_surjective, D.endRegRep_apply, ⟨D.regularIso⟩⟩

/-- Maschke's theorem, part (ii), **isotypic-decomposition form**, the book's final display.

Beyond the algebra isomorphism `k[G] ≃ₐ[k] ⊕ᵢ End(Vᵢ)` (`Theorem4_1_1_algebra_iso`) and its
equivariant upgrade `k[G] ≅ ∏ᵢ End(Vᵢ)` (`Theorem4_1_1_regularRep_iso`), the book records the
explicit decomposition of the regular representation into irreducibles with multiplicities:

  `k[G] ≅ ⊕ᵢ (dim Vᵢ) · Vᵢ`,

each irreducible `Vᵢ` occurring with multiplicity `dim Vᵢ`. This theorem records that content:
there is a complete family `V : Fin n → FDRep k G` of the irreducible representations of `G`,
each `Simple`, pairwise non-isomorphic, exhausting the simples, together with a representation
`ρ_dec` on `∏ᵢ Vᵢ^(dᵢ)` whose multiplicities are `d i = dim (V i)` and whose action is diagonal
`(g · w) i j = ρᵢ(g) (w i j)` (so each of the `d i` copies at `(i, j)` is `Vᵢ`), such
that the regular representation `MonoidAlgebra.regularFDRep k G` is isomorphic in `FDRep k G` to
`FDRep.of ρ_dec`. The witnesses are the column-vector representations `columnFDRep`, the diagonal
multiplicity representation `IrrepDecomp.columnMultRep`, and the isomorphism
`IrrepDecomp.regularColumnMultIso`. -/
theorem Etingof.Theorem4_1_1_regularRep_isotypic (k G : Type u)
    [Field k] [IsAlgClosed k] [Group G] [Fintype G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G) (d : Fin n → ℕ)
      (ρ_dec : Representation k G (Π i, Fin (d i) → (V i))),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ W : FDRep k G, Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      (∀ i, d i = Module.finrank k (V i)) ∧
      (∀ (g : G) (w : Π i, Fin (d i) → (V i)) (i : Fin n) (j : Fin (d i)),
        ρ_dec g w i j = (V i).ρ g (w i j)) ∧
      Nonempty (MonoidAlgebra.regularFDRep k G ≅ FDRep.of ρ_dec) :=
  let D : IrrepDecomp k G := IrrepDecomp.mk'
  ⟨D.n, D.columnFDRep, D.d, D.columnMultRep, D.columnFDRep_simple, D.columnFDRep_injective,
    D.columnFDRep_surjective, fun i => (D.finrank_columnFDRep i).symm,
    D.columnMultRep_apply, ⟨D.regularColumnMultIso⟩⟩

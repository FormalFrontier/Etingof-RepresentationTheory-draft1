import Mathlib

/-!
# Example 4.3: Irreducible Representations of Finite Abelian Groups

For a finite abelian group `G = ℤ/n₁ℤ × ⋯ × ℤ/nₖℤ`, all irreducible representations
over an algebraically closed field are 1-dimensional. This is the fact the book recalls
("all irreducible representations over `ℂ` (and algebraically closed fields in general) of
commutative algebras and groups are 1-dimensional"), and it uses both the
commutativity of `G` and the algebraic closedness of `k`.

The dual group (Pontryagin dual) `G^∨` consists of all irreducible characters.
For `ℤ/nℤ`: the irreducible characters are `ρₖ(m) = e^(2πimk/n)` for `k = 0, …, n-1`,
giving `ℤ/nℤ^∨ ≅ ℤ/nℤ`. In general `(G₁ × G₂)^∨ = G₁^∨ × G₂^∨`, so `G^∨ ≅ G`
(non-canonically), and `G ≅ (G^∨)^∨` canonically via `φ(g)(χ) = χ(g)`.

## Mathlib correspondence

A representation `ρ : Representation k G V` is the same data as a module over the group
algebra `k[G] = MonoidAlgebra k G`, via `ρ.asModule`. When `G` is commutative, `k[G]` is a
commutative `k`-algebra, so an irreducible (= `IsSimpleModule k[G] ρ.asModule`)
finite-dimensional representation is 1-dimensional by Etingof Corollary 2.3.12, formalized in
Mathlib as `IsSimpleModule.finrank_eq_one_of_isMulCommutative`. This is exactly the book's
argument: by Schur's lemma every `g ∈ G` acts as a scalar, so every line is a subrepresentation.
-/

/-- For a finite abelian group `G` and an algebraically closed field `k`, every irreducible
finite-dimensional representation `ρ : Representation k G V` is 1-dimensional. Irreducibility
is `IsSimpleModule (MonoidAlgebra k G) ρ.asModule`, i.e. simplicity *as a representation* of
`G` (a module over the group algebra `k[G]`), not merely as a `k`-vector space.
(Etingof Example 4.3) -/
theorem Etingof.Example4_3_FiniteAbelianGroups
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [CommGroup G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V)
    [hirr : IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    Module.finrank k V = 1 := by
  -- The group algebra `k[G]` is commutative because `G` is commutative.
  have : IsMulCommutative (MonoidAlgebra k G) := ⟨⟨mul_comm⟩⟩
  -- Corollary 2.3.12: a simple finite-dimensional module over a commutative `k`-algebra over an
  -- algebraically closed field is 1-dimensional. Here the algebra is `k[G]` and the module is
  -- `ρ.asModule` (whose `k`-dimension equals `finrank k V`).
  have h : Module.finrank k ρ.asModule = 1 :=
    IsSimpleModule.finrank_eq_one_of_isMulCommutative
      (k := k) (A := MonoidAlgebra k G) (V := ρ.asModule)
  rwa [ρ.asModuleEquiv.finrank_eq] at h

/-!
## The dual (character) group

The book's second half of Example 4.3(1) develops the **dual group** (character group)
`G^∨` of a finite abelian group `G`. Since every irreducible representation of an abelian
group over `ℂ` is one-dimensional (the theorem above, plus that a line carries the same data
as a homomorphism to scalars), `G^∨` is the same as the group of complex-valued *characters*
`G →* ℂˣ`, and pointwise multiplication and inversion of characters make it an abelian group.
We formalize `G^∨` as `G →* ℂˣ`.

The three claims of the book are:

* duality respects products, `(G₁ × ⋯ × Gₙ)^∨ ≅ G₁^∨ × ⋯ × Gₙ^∨`
  (`Etingof.characterGroupProdEquiv`, `Etingof.characterGroupPiEquiv`);
* `G^∨ ≅ G` noncanonically (`Etingof.nonempty_mulEquiv_characterGroup`), the choice hidden in
  the decomposition of `G` into cyclic factors;
* `G ≅ (G^∨)^∨` **canonically** via evaluation `φ(g)(χ) = χ(g)`
  (`Etingof.characterDoubleDualEquiv` and `Etingof.characterDoubleDualEquiv_apply_apply`).

For a finite abelian group these follow from Mathlib's duality theory of finite commutative
groups, `Mathlib.GroupTheory.FiniteAbelian.Duality`, taking the coefficient monoid to be `ℂ`,
which has enough roots of unity because it is algebraically (hence separably) closed of
characteristic zero.
-/

namespace Etingof

/-- The **dual group** (character group) `G^∨ = G →* ℂˣ` of a group `G`: the group of
complex-valued multiplicative characters, an abelian group under pointwise multiplication.
For a finite abelian group these are exactly the (one-dimensional) irreducible representations
of `G`. (Etingof Example 4.3(1)) -/
abbrev CharacterGroup (G : Type*) [CommGroup G] : Type _ := G →* ℂˣ

/-- The character group is an abelian group, recording the book's observation that the product
`χ₁χ₂` and inverse `χ⁻¹` of characters are again characters. -/
example (G : Type*) [CommGroup G] : CommGroup (CharacterGroup G) := inferInstance

/-- `ℂ` has enough roots of unity of every order coming from a finite group: it is
algebraically (hence separably) closed of characteristic zero, so the exponent of any finite
group is invertible in `ℂ`. This is the hypothesis Mathlib's finite-abelian duality needs. -/
instance instHasEnoughRootsOfUnityComplexExponent (G : Type*) [Group G] [Finite G] :
    HasEnoughRootsOfUnity ℂ (Monoid.exponent G) :=
  have : NeZero ((Monoid.exponent G : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite (G := G)⟩
  inferInstance

/-- **Duality respects binary products**: `(G₁ × G₂)^∨ ≅ G₁^∨ × G₂^∨`. A character of a
product is the same data as a pair of characters, via restriction to the two factors.
(Etingof Example 4.3(1)) -/
def characterGroupProdEquiv (G₁ G₂ : Type*) [CommGroup G₁] [CommGroup G₂] :
    CharacterGroup (G₁ × G₂) ≃* CharacterGroup G₁ × CharacterGroup G₂ where
  toFun φ := (φ.comp (.inl G₁ G₂), φ.comp (.inr G₁ G₂))
  invFun p := p.1.comp (.fst G₁ G₂) * p.2.comp (.snd G₁ G₂)
  left_inv φ := by
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨a, b⟩ := x
    change φ (a, 1) * φ (1, b) = φ (a, b)
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  right_inv p := by
    refine Prod.ext (DFunLike.ext _ _ fun a => ?_) (DFunLike.ext _ _ fun a => ?_)
    · change p.1 a * p.2 1 = p.1 a
      rw [map_one, mul_one]
    · change p.1 1 * p.2 a = p.2 a
      rw [map_one, one_mul]
  map_mul' φ ψ := Prod.ext rfl rfl

/-- **Duality respects finite products**: `(∏ᵢ Gᵢ)^∨ ≅ ∏ᵢ Gᵢ^∨`. This is the book's displayed
`(G₁ × ⋯ × Gₙ)^∨ = G₁^∨ × ⋯ × Gₙ^∨` for an arbitrary finite index set. (Etingof Example 4.3(1)) -/
def characterGroupPiEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → Type*) [∀ i, CommGroup (G i)] :
    CharacterGroup (∀ i, G i) ≃* ∀ i, CharacterGroup (G i) :=
  Pi.monoidHomMulEquiv G ℂˣ

/-- **Noncanonical self-duality**: a finite abelian group is isomorphic to its dual group,
`G ≅ G^∨`. As the book stresses, this isomorphism is not canonical: it depends on a choice of
decomposition of `G` into cyclic factors, so it is stated as mere nonemptiness of the type of
isomorphisms rather than a chosen map. (Etingof Example 4.3(1)) -/
theorem nonempty_mulEquiv_characterGroup (G : Type*) [CommGroup G] [Finite G] :
    Nonempty (G ≃* CharacterGroup G) :=
  (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).map MulEquiv.symm

/-- **Canonical double duality**: a finite abelian group is *canonically* isomorphic to its
double dual, `G ≅ (G^∨)^∨`. The isomorphism is the evaluation map `φ(g)(χ) = χ(g)`; see
`characterDoubleDualEquiv_apply_apply`. (Etingof Example 4.3(1)) -/
noncomputable def characterDoubleDualEquiv (G : Type*) [CommGroup G] [Finite G] :
    G ≃* CharacterGroup (CharacterGroup G) :=
  (CommGroup.monoidHomMonoidHomEquiv G ℂ).symm

/-- The canonical double-dual isomorphism is evaluation: `φ(g)(χ) = χ(g)`, exactly the book's
formula. Here `χ = φ` ranges over `G^∨ = G →* ℂˣ`. -/
@[simp]
theorem characterDoubleDualEquiv_apply_apply (G : Type*) [CommGroup G] [Finite G]
    (g : G) (χ : CharacterGroup G) :
    characterDoubleDualEquiv G g χ = χ g :=
  CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply G ℂ g χ

end Etingof

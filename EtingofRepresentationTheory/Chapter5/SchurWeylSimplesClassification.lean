import EtingofRepresentationTheory.Chapter5.FormalCharacterIso

/-!
# Highest-weight classification of the Schur-Weyl simple summands

This file carves out the **conceptual crux** of Schur-Weyl #6
(`iso_of_formalCharacter_eq_schurPoly`, issue #2483): identifying the *abstract*
simple summands `L i` produced by the equivariant decomposition
`glTensorRep_equivariant_schurWeyl_decomposition`
(`Chapter5/FormalCharacterIso.lean`) of `V^{⊗n}` (`V = Fin N → k`, `n ≤ N`) with
concrete Schur modules, at the level of their formal characters.

The decomposition gives a `GL_N(k)`-equivariant iso
`V^{⊗n} ≃ₗ[k] ⨁ i, S i ⊗[k] L i` with each `L i` a simple polynomial
`GL_N(k)`-representation. The genuine mathematical content here is the
highest-weight theorem "a simple polynomial `GL_N`-rep is determined by its
character," which pins each `char(L i)` to a Schur polynomial `schurPoly N λᵢ`
for an injective partition assignment `λ`.

## Contents

* `formalCharacter_linearIndependent_of_eq_schurPoly` — the **reduction**
  (sorry-free): if the characters of a family `L` equal distinct Schur
  polynomials, they are linearly independent over `ℚ`. This is the mechanical
  half noted in the strategy ("the classification gives linear independence for
  free via `schurPoly_linearIndependent` + `schurPoly_injective`").
* `schurWeyl_simples_formalCharacter_classification_core` — the **crux**
  (isolated `sorry`): the abstract simples are character-classified by an
  injective Schur-polynomial assignment. This is the deferred highest-weight
  classification; see the issue tracking its proof.
* `glTensorRep_schurWeyl_simples_formalCharacter_linearIndependent` — the
  **headline** consumed by the #2483 assembly: the characters of the abstract
  simple summands of `V^{⊗n}` are linearly independent over `ℚ` (sorry-free
  given the crux).
-/

open CategoryTheory MvPolynomial

open scoped TensorProduct

namespace Etingof

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in
/-- **Reduction (sorry-free).** If each character `formalCharacter k N (L i)`
equals a Schur polynomial `schurPoly N (lam i)` along an *injective* assignment
`lam` of antitone partitions, then the characters are linearly independent over
`ℚ`.

This is the mechanical half of the highest-weight classification: it turns the
identification `char(L i) = schurPoly N λᵢ` (the hard
`schurWeyl_simples_formalCharacter_classification_core`) into the
`LinearIndependent` statement the Schur-Weyl assembly (#2483) consumes, using
the linear independence of Schur polynomials (`schurPoly_linearIndependent`). -/
theorem formalCharacter_linearIndependent_of_eq_schurPoly
    (N : ℕ) {ι : Type*}
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (lam : ι → {l : Fin N → ℕ // Antitone l})
    (hlam : Function.Injective lam)
    (hchar : ∀ i, formalCharacter k N (L i) = schurPoly N (lam i).val) :
    LinearIndependent ℚ (fun i => formalCharacter k N (L i)) := by
  have hcomp :
      (fun i => formalCharacter k N (L i))
        = (fun p : {l : Fin N → ℕ // Antitone l} => schurPoly N p.val) ∘ lam := by
    funext i; exact hchar i
  rw [hcomp]
  exact (schurPoly_linearIndependent N).comp lam hlam

/-- **Highest-weight classification of the Schur-Weyl simples (crux, isolated
`sorry`).** Given the equivariant decomposition data of `V^{⊗n}` from
`glTensorRep_equivariant_schurWeyl_decomposition` — the multiplicity spaces
`S i`, the abstract simple polynomial `GL_N`-reps `L i`, and the equivariant iso
`e` — there is an *injective* assignment `lam` of antitone partitions with
`char(L i) = schurPoly N (lam i)` for every `i`.

This is the deferred highest-weight classification: "a simple polynomial
`GL_N`-rep is determined by its character, and the simples of `V^{⊗n}` are
exactly the `SchurModule k N λ` for antitone `λ`, `|λ| = n`, `length ≤ N`."

Well-posedness (issue #4721, replacing #4704): the conclusion needs two
hypotheses on the abstract simples `L` that the bare equivariance data `(e, he)`
does not pin down, so they are taken explicitly:
* `hLsimp` — each `L i` is a simple polynomial `GL_N`-rep. Without it `char(L i)`
  need not be a single `schurPoly` (a reducible `A ⊕ B` summand absorbs into the
  equivariance), so `char(L i) = schurPoly N λᵢ` would be false.
* `hLdist` — the `L i` are pairwise non-isomorphic. Without it an isotypic
  component `S ⊗ L` with `dim S ≥ 2` re-presents as two indices sharing one `L`,
  forcing `L i ≅ L j` and making `Function.Injective lam` impossible.
Both are surfaced by `glTensorRep_equivariant_schurWeyl_decomposition` (simplicity
now, distinctness pending the Schur-Weyl GL-side injectivity sub-issue).

Proof strategy (per #4698 / #2483): each `SchurModule k N λ` is simple
(`schurModule_isSimple`), algebraic, and homogeneous of degree `n = ∑ λ`, so under
the abstract decomposition it lands as a single summand `L i₀` with
`char(L i₀) = formalCharacter k N (SchurModule k N λ) = schurPoly N λ`
(`formalCharacter_schurModule_eq_schurPoly`). Injectivity of `lam` follows from
`hLdist` and `schurPoly_injective`.

The deep step — "a simple polynomial `GL_N`-rep is character-determined ⇒
`char = schurPoly`" — is the deferred Tier-4 highest-weight content; the single
residual `sorry` is isolated here so the reduction and headline corollary remain
otherwise sorry-free. Tracked by issue #4721. -/
theorem schurWeyl_simples_formalCharacter_classification_core
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ))
    (hLdist : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j)))) :
    ∃ lam : ι → {l : Fin N → ℕ // Antitone l},
      Function.Injective lam ∧
      ∀ i, formalCharacter k N (L i) = schurPoly N (lam i).val := by
  -- Well-posed (issue #4721) once the highest-weight classification is supplied:
  -- `hLsimp` (each `L i` simple) pins `char(L i)` to a single `schurPoly N λᵢ`;
  -- `hLdist` (the `L i` pairwise non-isomorphic) gives `Function.Injective lam`
  -- via `schurPoly_injective`. The deep step "a simple polynomial `GL_N`-rep is
  -- character-determined ⇒ `char = schurPoly`" is the deferred Tier-4 content.
  sorry

/-- **Pairwise distinctness of the Schur-Weyl simples (deferred, isolated
`sorry`).** The abstract simple summands `L i` of `V^{⊗n}` produced by the
equivariant decomposition `glTensorRep_equivariant_schurWeyl_decomposition` are
pairwise non-isomorphic.

This is the GL-side distinctness output targeted by issue #4731. Part 1
(`SchurWeylLDistinct.lean`, the GL-equivariant ⟹ centralizer-linear reduction)
has landed; the remaining B-side step `M_i ≅_C M_j ⟹ i = j` (the symmetric
double-centralizer argument) is in flight as #4849/#4859/#4862. Until that chain
lands, the `Pairwise` conclusion is isolated here as a single `sorry`, mirroring
`schurWeyl_simples_formalCharacter_classification_core`, so the downstream
schurPoly-classification API (`decompose_polynomial_gl_rep`, issue #4758) stays
otherwise sorry-free. -/
theorem glTensorRep_schurWeyl_simples_pairwise_distinct
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ)) :
    Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))) := by
  -- Deferred: the B-side distinctness `M_i ≅_C M_j ⟹ i = j` (#4849/#4859/#4862)
  -- transported to the GL-side `L i ≇ L j` via the Part-1 centralizer-linear
  -- reduction (`SchurWeylLDistinct.lean`, #4731). Isolated here as one `sorry`.
  sorry

/-- **schurPoly-classification of the Schur-Weyl simples (from the bare
equivariance data).** Combines the deferred distinctness
(`glTensorRep_schurWeyl_simples_pairwise_distinct`) with the classification crux
(`schurWeyl_simples_formalCharacter_classification_core`) to produce, from only
the decomposition data `(e, he)` and per-summand simplicity `hLsimp`, an
injective antitone-partition assignment `lam` with
`char(L i) = schurPoly N (lam i)`.

This is the form consumed by `decompose_polynomial_gl_rep` (issue #4758): it lets
the Schur-Weyl #6 assembly read the partition classification of the abstract
simples without re-deriving the tensor-power decomposition data `(e, he, hLsimp,
hLdist)` itself. -/
theorem glTensorRep_schurWeyl_simples_schurPoly_classified
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ)) :
    ∃ lam : ι → {l : Fin N → ℕ // Antitone l},
      Function.Injective lam ∧
      ∀ i, formalCharacter k N (L i) = schurPoly N (lam i).val :=
  schurWeyl_simples_formalCharacter_classification_core k N n hN L e he hLsimp
    (glTensorRep_schurWeyl_simples_pairwise_distinct k N n hN L e he hLsimp)

/-- **Headline (sorry-free given the crux).** The formal characters of the
abstract simple summands `L i` of `V^{⊗n}` (from
`glTensorRep_equivariant_schurWeyl_decomposition`) are linearly independent over
`ℚ`. This is the minimal form consumed by the Schur-Weyl #6 assembly (#2483).

The proof obtains the partition classification from
`schurWeyl_simples_formalCharacter_classification_core` and feeds it to the
reduction `formalCharacter_linearIndependent_of_eq_schurPoly`. -/
theorem glTensorRep_schurWeyl_simples_formalCharacter_linearIndependent
    (N n : ℕ) (hN : n ≤ N)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type u} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : TensorPower k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type u))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ))
    (hLdist : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j)))) :
    LinearIndependent ℚ (fun i => formalCharacter k N (L i)) := by
  obtain ⟨lam, hlam_inj, hlam_char⟩ :=
    schurWeyl_simples_formalCharacter_classification_core k N n hN L e he hLsimp hLdist
  exact formalCharacter_linearIndependent_of_eq_schurPoly k N L lam hlam_inj hlam_char

end Etingof

import EtingofRepresentationTheory.Chapter8.KoszulContraction
import EtingofRepresentationTheory.Chapter8.KoszulDifferential
import EtingofRepresentationTheory.Chapter8.KoszulAugmentation
import EtingofRepresentationTheory.Chapter8.KoszulBasis
import EtingofRepresentationTheory.Chapter8.KoszulResolution

/-!
# Problem 8.2.10: Koszul resolution and the Hilbert syzygies theorem

> Let `V` be a finite dimensional vector space over a field `k`. Let
> `Cᵢ = SV ⊗ ⋀ⁱ V`, with the contraction differential `dᵢ : Cᵢ → Cᵢ₋₁`.
> (i) `C_•` is a free resolution of `k` as an `SV`-module (the **Koszul
> resolution**). (ii) A free `SV`-resolution of `SW` for `V = U ⊕ W`.
> (iii) The Koszul **bimodule** resolution of `SV` over `SV ⊗ SV`.
> (iv) For any `SV`-modules `M, N` and `i > dim V`,
> `Torᵢ^{SV}(M, N) = Extⁱ_{SV}(M, N) = 0` (the **Hilbert syzygies theorem**).
> (v) Compute `Extⁱ_{SV}(k, k)` and `Torᵢ^{SV}(k, k)`.

## Relation to Example 9.4.4

The main narrative cites Problem 8.2.10 only in Example 9.4.4:

> "By the Hilbert syzygies theorem (see Problem 8.2.10(iv)), the homological
> dimension of the polynomial algebra `k[x₁, …, xₙ]` is `n`."

That conclusion is formalized in `Chapter9/Example9_4_4.lean` as

  `Etingof.Example_9_4_4 (k : Type u) [Field k] (n : ℕ) :`
  `    Etingof.homologicalDimension (MvPolynomial (Fin n) k) = n`

For a finite dimensional `V` over a field, `SV` is a polynomial ring
`k[x₁, …, xₙ]` with `n = dim V`, so `Etingof.Example_9_4_4` is exactly the
statement Example 9.4.4 extracts from Problem 8.2.10(iv): the global (homological)
dimension of `SV` equals `dim V`. In particular the vanishing half,
`Extⁱ_{SV}(M, N) = 0` for all `M, N` and `i > dim V`, is the content of
`Etingof.HasHomologicalDimensionLE (MvPolynomial (Fin n) k) n`, established by
`Etingof.mvPolynomial_hasHomologicalDimensionLE`.

The Chapter 9 proof does not use the explicit Koszul resolution of Problem 8.2.10.
Instead it proves the polynomial-ring case by a degree-one Koszul short exact
sequence (`koszulSES_shortExact`) together with induction on the number of
variables and the polynomial-extension theorem
(`hasHomologicalDimensionLE_polynomial`), a self-contained proof of the required
conclusion.

The explicit Koszul resolution (i), the `SW` resolution (ii), the Koszul bimodule
resolution (iii), and the computation of `Ext_{SV}(k, k)` and `Tor_{SV}(k, k)` (v)
are self-contained and are not used elsewhere in the book.

## State of the source-level formalization

The exercise itself is being formalized bottom-up. Landed so far:

* `Chapter8/KoszulContraction.lean` — the contraction operator `ιᵤ : ⋀ⁱ V → ⋀ⁱ⁻¹ V` that the
  problem statement defines, in the form
  `Etingof.exteriorContraction (u : Module.Dual R M) (n : ℕ) : ⋀[R]^(n+1) M →ₗ[R] ⋀[R]^n M`,
  together with the book's defining alternating-sum formula
  (`Etingof.exteriorContraction_ιMulti`), `ιᵤ ∘ ιᵤ = 0`
  (`Etingof.exteriorContraction_exteriorContraction`) and the anticommutation
  `ιᵤ ∘ ιᵤ' = - ιᵤ' ∘ ιᵤ` (`Etingof.exteriorContraction_comm`). The last two are exactly what
  makes the Koszul differential `d = ∑ₐ xₐ ⊗ ι_{xₐ*}` square to zero.

* `Chapter8/KoszulDifferential.lean` — the terms `Etingof.koszulX k V i = SV ⊗[k] ⋀ⁱ V` as
  `SV`-modules and the Koszul differential
  `Etingof.koszulD b i : koszulX k V (i + 1) →ₗ[SV] koszulX k V i`, the algebraic form
  `d = ∑ₐ (multiplication by xₐ) ⊗ ι_{xₐ*}` of the book's `dᵢ(f)(u) = ιᵤ (f u)`, together with
  `Etingof.koszulD_comp_koszulD : d ∘ d = 0`. The cancellation is characteristic-free
  (`Finset.sum_ninvolution` on the off-diagonal pairs, `ιᵤ ∘ ιᵤ = 0` on the diagonal). The
  complex itself is `Etingof.koszulComplex b : ChainComplex (ModuleCat SV) ℕ`.

* `Chapter8/KoszulAugmentation.lean` — the rest of the "free resolution" data of part (i), short
  of exactness:

  * the trivial `SV`-module `Etingof.KoszulAugModule k V` (the book's "`k` with trivial action of
    `V`"): `k`, with `SV` acting through the counit `SymmetricAlgebra.algebraMapInv`, which kills
    `V`;
  * the augmentation `Etingof.koszulAug : C₀ = SV ⊗ ⋀⁰ V →ₗ[SV] k`, which is surjective
    (`Etingof.koszulAug_surjective`) and annihilates the image of `d₀`
    (`Etingof.koszulAug_comp_koszulD`), so the augmented complex is a complex;
  * freeness of the terms: `Etingof.koszulXBasis` base-changes the standard `k`-basis of `⋀ⁱ V`
    to an `SV`-basis of `Cᵢ`, giving `Etingof.koszulX_free` and hence
    `Etingof.koszulX_projective` — the "projective (in fact, free)" of the statement;
  * basis-independence of `d`. `Etingof.koszulD` is defined from a chosen basis, but
    `Etingof.koszulD_one_tmul_ιMulti` evaluates it on the generators `1 ⊗ v₁ ∧ ⋯ ∧ v_{i+1}` by the
    basis-free formula `∑ⱼ (-1)ʲ vⱼ ⊗ v₁ ∧ ⋯ v̂ⱼ ⋯ ∧ v_{i+1}`, matching the book's
    `dᵢ(f)(u) = ιᵤ (f u)`. Since `SV`-linear maps out of `Cᵢ₊₁` are determined by those values
    (`Etingof.koszulX_hom_ext`), this gives `Etingof.koszulD_eq_of_basis` and
    `Etingof.koszulComplex_eq_of_basis`.

* `Chapter8/KoszulBasis.lean` — the complex in coordinates, which is what a characteristic-free
  exactness proof needs. A finite basis `b : Module.Basis κ k V` on a linearly ordered `κ` gives
  the monomial `k`-basis of `SV` and the subset `k`-basis of `⋀ⁱ V`, hence the `k`-basis
  `Etingof.koszulKBasis` of `Cᵢ` indexed by pairs `(α, s)` of a monomial exponent and an
  `i`-element subset. On it, `Etingof.koszulD_koszulKBasis` reads

    `d (x^α ⊗ e_s) = ∑_{a ∈ s} (-1)^(pos(a, s) + 1) x^(α + xₐ) ⊗ e_(s \ {a})`,

  where `pos(a, s) = #{c ∈ s : c < a}` is `Etingof.finsetPos`; the sign is the book's `(-1)ʲ`,
  since deleting `a` deletes the entry in position `pos(a, s)`. The two contraction lemmas
  behind it, `Etingof.exteriorContraction_basis_of_notMem` and
  `Etingof.exteriorContraction_basis_of_mem`, say that `ι_{xₐ*}` kills `e_s` for `a ∉ s` and
  sends it to `(-1)^(pos(a,s)+1) e_(s \ {a})` for `a ∈ s`. The augmentation is
  `Etingof.koszulAug_koszulKBasis`: `ε (x^α ⊗ 1) = 1` if `α = 0` and `0` otherwise.

* `Chapter8/KoszulHomotopy.lean` — the `k`-linear contracting homotopy `Etingof.koszulH` of the
  augmented complex, together with the splitting `Etingof.koszulEta` of the augmentation. On the
  basis vector `x^α ⊗ e_s` it is `-(x^(α - eₚ) ⊗ e_(insert p s))` when `p = min (supp α)` lies
  strictly below every element of `s` (the pivot condition `Etingof.IsKoszulPivot`), and `0`
  otherwise. The two identities it satisfies are
  `Etingof.koszulD_koszulH_add_koszulH_koszulD` (`d h + h d = id` on `Cᵢ₊₁`) and
  `Etingof.koszulD_koszulH_add_eta_aug` (`d h + η ε = id` on `C₀`). No `SV`-linear homotopy can
  exist — the complex resolves `k` and is not `SV`-split — and the construction is
  characteristic-free, unlike the Euler-operator homotopy `dκ + κd = (p + q) • id`.

* `Chapter8/KoszulResolution.lean` — **part (i), complete**. The homotopy gives exactness, since
  exactness is a statement about the underlying additive groups: a cycle `x` satisfies
  `x = d (h x) + h (d x) = d (h x)`, so `Etingof.koszulD_range_eq_ker` (`range dᵢ₊₁ = ker dᵢ`) and
  `Etingof.koszulD_zero_range_eq_ker_koszulAug` (`range d₀ = ker ε`), the two ranges and kernels
  being honest `SV`-submodules because `d` and `ε` are `SV`-linear. Packaged categorically, the
  augmentation `Etingof.koszulPi : C_• ⟶ k[0]` is a quasi-isomorphism
  (`Etingof.koszulPi_quasiIso`), giving `Etingof.koszulResolution` — see `Etingof.Problem_8_2_10_i`
  below.

Still to come: the `SW` resolution (ii), the bimodule resolution (iii), Hilbert syzygies (iv), and
the `Ext`/`Tor` computation (v). See the child issues linked from
<https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/issues/5723>.
-/

universe u v w

namespace Etingof

/-- **Problem 8.2.10(i).** For a vector space `V` with a finite basis `b` over a commutative ring
`k`, the Koszul complex `Cᵢ = SV ⊗ ⋀ⁱ V` with the contraction differential `dᵢ(f)(u) = ιᵤ (f u)` is
a **free resolution of `k`** as an `SV`-module, `k` carrying the trivial action of `V` — the
*Koszul resolution*.

This is `Etingof.koszulResolution`. The three components of the assertion are recorded separately
below: the underlying complex is the Koszul complex itself (`Etingof.Problem_8_2_10_i_complex`),
its terms are free and not merely projective (`Etingof.Problem_8_2_10_i_free`), and the
augmentation is the counit `ε : SV ⊗ ⋀⁰ V → k` (`Etingof.Problem_8_2_10_i_π`). The book states
this for a finite dimensional `V` over a field, which is
`Etingof.koszulResolutionOfFiniteDimensional`. -/
noncomputable def Problem_8_2_10_i {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V]
    [Module k V] {κ : Type w} [LinearOrder κ] [Fintype κ] (b : Module.Basis κ k V) :
    CategoryTheory.ProjectiveResolution
      (ModuleCat.of (SymmetricAlgebra k V) (KoszulAugModule k V)) :=
  koszulResolution b

section

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]
variable {κ : Type w} [LinearOrder κ] [Fintype κ] (b : Module.Basis κ k V)

/-- The resolving complex of Problem 8.2.10(i) is the Koszul complex `Cᵢ = SV ⊗ ⋀ⁱ V` of the
problem statement, not some abstract resolution produced by `EnoughProjectives`. -/
theorem Problem_8_2_10_i_complex : (Problem_8_2_10_i b).complex = koszulComplex b := rfl

/-- The resolution of Problem 8.2.10(i) is by **free** `SV`-modules — the parenthetical
"(in fact, free)" of the problem statement. -/
theorem Problem_8_2_10_i_free (i : ℕ) :
    Module.Free (SymmetricAlgebra k V) ((Problem_8_2_10_i b).complex.X i) :=
  koszulResolution_free b i

/-- The map resolving `k` is the augmentation `ε : C₀ = SV ⊗ ⋀⁰ V → k`, the counit of `SV`. -/
theorem Problem_8_2_10_i_π : (Problem_8_2_10_i b).π.f 0 = ModuleCat.ofHom (koszulAug k V) :=
  koszulPi_f_zero b

end

end Etingof

import EtingofRepresentationTheory.Chapter8.KoszulContraction

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

Still to come: the complex `Cᵢ = SV ⊗ ⋀ⁱ V` with `d² = 0` and its exactness (i), the `SW`
resolution (ii), the bimodule resolution (iii), Hilbert syzygies (iv), and the `Ext`/`Tor`
computation (v). See the child issues linked from
<https://github.com/kim-em/Etingof-RepresentationTheory-draft1/issues/5723>.
-/

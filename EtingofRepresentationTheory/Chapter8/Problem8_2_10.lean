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

## Coverage status (completeness audit, epic #5338)

The only place the main narrative cites Problem 8.2.10 is **Example 9.4.4**:

> "By the Hilbert syzygies theorem (see Problem 8.2.10(iv)), the homological
> dimension of the polynomial algebra `k[x₁, …, xₙ]` is `n`."

That load-bearing conclusion is formalized directly and completely in
`Chapter9/Example9_4_4.lean` as

  `Etingof.Example_9_4_4 (k : Type u) [Field k] (n : ℕ) :`
  `    Etingof.homologicalDimension (MvPolynomial (Fin n) k) = n`

For a finite dimensional `V` over a field, `SV` *is* a polynomial ring
`k[x₁, …, xₙ]` with `n = dim V`, so `Etingof.Example_9_4_4` is exactly the
statement Example 9.4.4 extracts from Problem 8.2.10(iv): the global (homological)
dimension of `SV` equals `dim V`. In particular the vanishing half —
`Extⁱ_{SV}(M, N) = 0` for all `M, N` and `i > dim V` — is the content of
`Etingof.HasHomologicalDimensionLE (MvPolynomial (Fin n) k) n`, established by
`Etingof.mvPolynomial_hasHomologicalDimensionLE` inside that proof.

The Chapter 9 formalization does **not** route through the explicit Koszul
resolution of Problem 8.2.10. Instead it proves the polynomial-ring case by a
degree-one Koszul short exact sequence (`koszulSES_shortExact`) together with
induction on the number of variables and the polynomial-extension theorem
(`hasHomologicalDimensionLE_polynomial`). This is a self-contained proof of the
needed conclusion, so Example 9.4.4 does not silently assume Problem 8.2.10 — it
reproves the required result.

Consequently Problem 8.2.10 is **not load-bearing** for the main narrative beyond
its part (iv), whose narrative use is fully covered above. The remaining parts of
the problem — the explicit Koszul resolution (i), the `SW` resolution (ii), the
Koszul bimodule resolution (iii), and the computation of `Ext_{SV}(k, k)` and
`Tor_{SV}(k, k)` (v) — are not separately formalized. They are self-contained
exercises that no later item in the book depends on.

This file records the audit conclusion and carries no proof; the machine-checked
citation target is `Etingof.Example_9_4_4`.
-/

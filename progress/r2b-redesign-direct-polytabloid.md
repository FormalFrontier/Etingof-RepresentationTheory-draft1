# Wall 3 R2.b redesign — `Δ ∈ V` via direct polytabloid identification

Meditate deliverable for issue
[#4584](https://github.com/FormalFrontier/Etingof-RepresentationTheory-draft1/issues/4584).
Supersedes the R2.b.i / R2.b.ii split (#2769 / #2770) and the cross-region
involution strategy of `progress/r3-bis-residual-cancellation.md` (#2776),
**both of which rest on a false pointwise-vanishing premise** (refuted in
`progress/20260614T113454Z_646f769f.md`, script
`progress/r2bi-counterexample-check.py`).

**Mandatory reading before re-attempting any R2.b issue.**

---

## TL;DR

1. **R2.b.i (`twistedPolytabloid_residual_no_colStd_zero`, #2769) is FALSE.**
   The residual `Δ` does *not* vanish pointwise at no-col-std tabloids below
   `[σ]`. Brute force on the canonical example (λ=(2,2), σ=swap(0,1), w=(0 2 1))
   gives `Δ = −ψ_{(0 1 3 2)}`, nonzero at three no-col-std tabloids.

2. **The r3-bis "cross-region involution" claim (#2776 §3) is ALSO false.**
   It asserted R2.b.i is *true* via the pair involution `(q,r) ↔ (q·r⁻¹, r⁻¹)`,
   "validated on the running example; sign reversal verified". That hand
   validation was not faithful: the brute-force check on the *same* example
   refutes the conclusion. A hand-checked confirmation of a tricky combinatorial
   truth-claim is no more trustworthy than a hand-checked refutation — brute
   force both directions.

3. **`Δ ∈ V` is TRUE** and is the genuine crux (it is equivalent to
   `f_w(σ) ∈ V`, the Garnir content). The correct route is **candidate 1 —
   direct polytabloid identification**: exhibit `Δ` as an explicit signed sum
   of generalized polytabloids `ψ_{τ'}` of column-standard `τ'`, each discharged
   by the inductive hypothesis on `(srRank, rowInvCount')` or by the base
   straightening lemma. No pointwise vanishing anywhere.

4. **Issue #4584's "candidate 2" (apply `tabloidSupport_straightening` to `Δ`)
   is circular** and must not be pursued as a route to `Δ ∈ V`:
   `tabloidSupport_straightening` (`SpechtModuleBasis.lean:1260`) takes
   `v ∈ V` as a *hypothesis* and only refines the span to dominance-bounded
   SYTs. It is the R1 bridge (`in_L_of_in_V_of_supp_bounded`), consumed *after*
   `Δ ∈ V` is known — never a way to establish it.

---

## 1. Logical structure (what actually needs proving)

From `garnir_polytabloid_identity` (`SpechtModuleBasis.lean:1364`):

```
ψ_σ = − Σ_{w ≠ 1, w supported on G} sign(w) · f_w(σ)
```

so `garnir_twisted_in_lower_span` (R2.c, #2703) reduces to: each
`f_w(σ) ∈ L_σ` (the strict-dominance-or-smaller-rowInv col-std span).
The R1 bridge `in_L_of_in_V_of_supp_bounded` (`:1438`) delivers
`f_w(σ) ∈ L_σ` from two inputs:

* **support bound** `∀ α, f_w(σ)([α]) ≠ 0 → tabloidDominates σ α` — already in
  hand via `twistedPolytabloid_support_bound`; and
* **V-membership** `f_w(σ) ∈ V` (V = SYT polytabloid span = the Specht module).

R2.a (`twistedPolytabloid_per_q_decomp`, `:1828`, merged) splits
`f_w(σ) = twistedIHPart σ w + Δ` with `twistedIHPart ∈ V` (IH-discharged) and
`Δ` support-bounded by `[σ]`. Hence

> **the only missing fact in the entire Wall-3 Garnir argument is `Δ ∈ V`**,
> equivalently `f_w(σ) ∈ V`.

Pointwise vanishing of `Δ` was the *attempted* route and it is dead.

## 2. Why candidate 1 is the right route (and is validated)

On the canonical example the predecessor computed, exactly,

```
Δ = − ψ_{(0 1 3 2)},   (0 1 3 2) column-standard,   [τ] strictly below [σ].
```

So `Δ` is a *single* generalized polytabloid of a column-standard `τ` whose
tabloid is strictly dominated by `[σ]`, i.e. `srRank τ < srRank σ`. That
polytabloid lies in `V` immediately by the **outer inductive hypothesis** (the
same `ih` already threaded through `twistedIHPart_mem_span`,
`SpechtModuleBasis.lean:1772`). No support-cancellation, no involution.

The general claim to formalize:

> **R2.b (corrected), `twistedPolytabloid_residual_in_V`.** For column-standard
> `σ`, positive `rowInvCount' σ`, arbitrary `w`, and the standard outer/inner
> IH on `(srRank, rowInvCount')`, the residual
> `Δ := twistedPolytabloid w σ − twistedIHPart σ w` lies in `V`
> (the SYT polytabloid span).

Proof strategy (no pointwise vanishing):

1. **Express `Δ` in the generalized-polytabloid basis at strictly smaller
   rank.** `Δ` is support-bounded by `[σ]` and has integer/ℂ coefficients on
   tabloids. Run leading-tabloid straightening (Algorithm A, the same loop
   behind `tabloidSupport_straightening`) *as a construction*, not as a
   consumer: repeatedly peel the dominance-maximal tabloid `[β]` in `supp Δ`.
   Because `supp Δ ⪯ [σ]` and the diagonal coefficient of `ψ_β` is 1
   (`generalizedPolytabloidTab_leading_tabloid`, `:1244`), each peel subtracts
   `c_β · ψ_{β'}` for a column-standard representative `β'` of `[β]` with
   `[β'] ⪯ [σ]`, leaving a strictly-lower-supported remainder. Every peeled
   `ψ_{β'}` has either `[β'] ≺ [σ]` (⟹ `srRank β' < srRank σ`, outer IH) or
   `[β'] = [σ]` with `rowInvCount' β' < rowInvCount' σ` (inner IH) — the same
   two-branch dispatch as `twistedIHPart_mem_span` and
   `polytabloidTab_in_lower_span_of_dominates` (`:1410`).
2. **Discharge each peeled polytabloid by the IH**, or — for a column-standard
   `β'` not strictly below `σ` and not covered by the IH — by the base
   straightening lemma `generalizedPolytabloidTab_mem_span_polytabloidTab`
   (`:2617`), which gives `ψ_{β'} ∈ V` unconditionally.
3. **Conclude `Δ ∈ V`** as a finite ℂ-combination of `V`-members.

The crux is step 1: that the straightening peel of a support-bounded element
terminates with every intermediate leading polytabloid IH-discharged. This is
*exactly* the content already proved inside `tabloidSupport_straightening`'s
`hclaim` (every nonzero SYT coefficient is dominance-bounded). The redesign is
therefore largely a **re-packaging of existing Algorithm A internals** to emit
`Δ ∈ V` directly, rather than a new combinatorial theorem.

### Cheaper alternative to evaluate first

`Δ ∈ V` ⟺ `f_w(σ) ∈ V` and `twistedIHPart ∈ V` is already proved. So an
equivalent, possibly shorter, deliverable is to prove `f_w(σ) ∈ V` directly via
the base straightening lemma applied after re-expressing `f_w(σ)` (a signed sum
of tabloids) through Algorithm A, then obtain `Δ ∈ V = f_w − twistedIHPart` by
subtraction. Whichever of `Δ` or `f_w(σ)` is cleaner to feed to Algorithm A
should be the formalization target; they are interchangeable.

## 3. Validate any redesign before formalizing

Per the refutation lesson (lean-formalization SKILL §"Counterexample-first",
point 6): before committing a session to the corrected proof, extend
`progress/r2bi-counterexample-check.py` to *compute the candidate polytabloid
decomposition of `Δ`* on (a) the (2,2) example and (b) a genuine λ ≥ (3,2)
example, and confirm every peeled `ψ_{β'}` sits at strictly smaller
`(srRank, rowInvCount')`. Do **not** hand-validate — the r3-bis episode shows a
hand check of a combinatorial claim (in either direction) is unreliable.

## 4. Issue re-scoping (planner actions)

* **#2769** (R2.b.i pointwise vanishing): statement is FALSE — close, do not
  re-file. Already `replan`. The successor is the corrected R2.b below.
* **#2770** (R2.b.ii assembly via R2.b.i + inner induction): premise is gone.
  Close or narrow to the corrected R2.b; its "given R2.b.i" framing is void.
* **Corrected R2.b** (new `feature` issue, filed by this meditate): prove
  `twistedPolytabloid_residual_in_V` via §2 candidate 1. Unblocks #2703 (R2.c).
* **#2776 / `progress/r3-bis-residual-cancellation.md`**: superseded; its §3
  involution does not exist. Header note added.

"""
R2.b validation (issue #4593, candidate 1 "direct polytabloid identification").

Mandated by the issue's "Validate before formalizing" step: extend
progress/r2bi-counterexample-check.py to compute the *peeled polytabloid
decomposition of Δ* and confirm every peeled ψ_{β'} sits at strictly smaller
(srRank, rowInvCount'), on the (2,2) example AND a genuine λ≥(3,2) example.

Δ := twistedPolytabloid w σ − twistedIHPart σ w   (R2.a residual)
   = Σ_{q∈Q} sign(q)·[w q⁻¹ σ]
       − Σ_{q∈R} sign(q)·ψ_{w q⁻¹ σ},   R = perQ_low ∪ perQ_eq.

Goal of the check: run leading-tabloid (dominance-maximal) elimination on Δ
using column-standard polytabloids ψ_{β'}, and confirm:
  (a) at every step the dominance-maximal support tabloid is column-standard
      (so a polytabloid can be subtracted — the peel never gets stuck);
  (b) the loop terminates at the zero vector (⟹ Δ ∈ V);
  (c) every peeled ψ_{β'} is column-standard with (srRank β', rowInv β')
      strictly below (srRank σ, rowInv σ) in the lex order, OR equal to σ's
      measure (discharged unconditionally by the base straightening lemma).
"""
from itertools import permutations


def make_shape(rowOf, colOf):
    n = len(rowOf)
    return rowOf, colOf, n


def run(rowOf, colOf, sigma, w, label):
    n = len(rowOf)
    print(f"\n{'='*70}\n{label}: n={n}, rowOf={rowOf}, colOf={colOf}")
    print(f"  sigma={sigma}  w={w}")

    def mul(a, b): return tuple(a[b[k]] for k in range(n))
    def inv(a):
        r = [0]*n
        for k in range(n): r[a[k]] = k
        return tuple(r)
    def sign(a):
        s = 1
        for i in range(n):
            for j in range(i+1, n):
                if a[i] > a[j]: s = -s
        return s
    def tab(a): return tuple(rowOf[a[k]] for k in range(n))  # entry k -> row

    def isColStd(a):
        ai = inv(a)
        for p1 in range(n):
            for p2 in range(n):
                if colOf[p1] == colOf[p2] and rowOf[p1] < rowOf[p2]:
                    if not ai[p1] < ai[p2]: return False
        return True

    allp = list(permutations(range(n)))
    Q = [p for p in allp if all(colOf[p[k]] == colOf[k] for k in range(n))]
    P = [p for p in allp if all(rowOf[p[k]] == rowOf[k] for k in range(n))]

    def cumul(a, k, i): return sum(1 for e in range(n) if e <= k and rowOf[a[e]] < i)
    def dominates(a, b): return all(cumul(b, k, i) <= cumul(a, k, i)
                                    for k in range(n) for i in range(n+1))
    def strictDom(a, b): return dominates(a, b) and tab(a) != tab(b)

    def rowInv(a):
        ai = inv(a); c = 0
        for p1 in range(n):
            for p2 in range(n):
                if rowOf[p1] == rowOf[p2] and colOf[p1] < colOf[p2] and ai[p2] < ai[p1]:
                    c += 1
        return c

    # srRank σ := #{ tabloids strictly dominating [σ] }.
    all_tabs = sorted(set(tab(a) for a in allp))
    def srRank_tab(t):
        a0 = next(a for a in allp if tab(a) == t)
        return sum(1 for s in all_tabs
                   if s != t and dominates(next(a for a in allp if tab(a) == s), a0))
    def srRank(a): return srRank_tab(tab(a))

    tabs_with_colstd = set(tab(a) for a in allp if isColStd(a))
    no_colstd = set(all_tabs) - tabs_with_colstd

    assert isColStd(sigma), "sigma must be column-standard"
    assert rowInv(sigma) > 0, "need positive rowInv"
    assert w not in Q and w not in P and w != tuple(range(n)), "w generic"

    # garnirColReindex: γ_q ∈ Q with γ_q·(w q⁻¹ σ) column-standard; τ_q = that.
    def gamma(q):
        base = mul(w, mul(inv(q), sigma))
        cands = [g for g in Q if isColStd(mul(g, base))]
        assert len(cands) == 1, (q, len(cands))
        return cands[0]
    def tau(q): return mul(gamma(q), mul(w, mul(inv(q), sigma)))

    def inR(q):
        t = tau(q)
        if strictDom(sigma, t): return True
        if tab(t) == tab(sigma) and rowInv(t) < rowInv(sigma): return True
        return False
    R = [q for q in Q if inR(q)]

    # ψ_τ as a dict tabloid -> coeff:  ψ_τ(α) = Σ_{p∈Q} sign(p)·[p⁻¹τ ≡ α].
    def psi(tauperm):
        d = {}
        for p in Q:
            t = tab(mul(inv(p), tauperm))
            d[t] = d.get(t, 0) + sign(p)
        return {t: c for t, c in d.items() if c != 0}

    # f_w(σ) = Σ_{q∈Q} sign(q)·[w q⁻¹ σ]  (single tabloids).
    fw = {}
    for q in Q:
        t = tab(mul(w, mul(inv(q), sigma)))
        fw[t] = fw.get(t, 0) + sign(q)
    fw = {t: c for t, c in fw.items() if c != 0}

    # twistedIHPart = Σ_{q∈R} sign(q)·ψ_{w q⁻¹ σ}.
    ihpart = {}
    for q in R:
        wq = mul(w, mul(inv(q), sigma))
        for t, c in psi(wq).items():
            ihpart[t] = ihpart.get(t, 0) + sign(q)*c
    ihpart = {t: c for t, c in ihpart.items() if c != 0}

    Delta = {}
    for t in set(fw) | set(ihpart):
        c = fw.get(t, 0) - ihpart.get(t, 0)
        if c != 0: Delta[t] = c

    # support bound check: every support tabloid weakly dominated by [σ].
    a_sig = next(a for a in allp if tab(a) == tab(sigma))
    for t in Delta:
        at = next(a for a in allp if tab(a) == t)
        assert dominates(a_sig, at), ("support bound violated", t)
    print(f"  |Q|={len(Q)} |P|={len(P)} |R|={len(R)}  "
          f"srRank(σ)={srRank(sigma)} rowInv(σ)={rowInv(sigma)}")
    print(f"  supp(Δ) size={len(Delta)}; "
          f"nonzero at no-colstd tabloids: "
          f"{sorted(t for t in Delta if t in no_colstd)}")

    # column-standard representative of a tabloid class [t]: the unique colStd a
    # with tab(a)=t.
    def colstd_rep(t):
        reps = [a for a in allp if tab(a) == t and isColStd(a)]
        # A tabloid can have several column-standard representatives; any one
        # works for the peel (generalizedPolytabloidTab_leading_tabloid holds
        # for every column-standard rep). Return one if it exists.
        return reps[0] if reps else None

    # dominance order on tabloids: pick a maximal support tabloid.
    def dom_tab(t1, t2):
        a1 = next(a for a in allp if tab(a) == t1)
        a2 = next(a for a in allp if tab(a) == t2)
        return dominates(a1, a2)

    # leading-tabloid elimination.
    sig_measure = (srRank(sigma), rowInv(sigma))
    cur = dict(Delta)
    peeled = []
    steps = 0
    stuck = None
    while cur:
        steps += 1
        if steps > 5000:
            stuck = "NONTERMINATION"; break
        # dominance-maximal support tabloid (no other support tabloid dominates it).
        supp = list(cur)
        maximals = [t for t in supp
                    if not any(s != t and dom_tab(s, t) for s in supp)]
        beta = maximals[0]
        if beta in no_colstd:
            stuck = ("STUCK at no-colstd maximal", beta, cur[beta]); break
        bp = colstd_rep(beta)
        c = cur[beta]
        meas = (srRank(bp), rowInv(bp))
        below = (meas < sig_measure) or (meas == sig_measure)  # lex; == ok (base lemma)
        strictly_below = (srRank(bp) < srRank(sigma)) or \
                         (srRank(bp) == srRank(sigma) and rowInv(bp) < rowInv(sigma))
        peeled.append((bp, c, meas, strictly_below, tab(bp) == tab(sigma)))
        # subtract c·ψ_{bp}.
        for t, v in psi(bp).items():
            cur[t] = cur.get(t, 0) - c*v
        cur = {t: v for t, v in cur.items() if v != 0}

    print(f"  peel steps={steps} stuck={stuck} terminated_at_zero={not cur and stuck is None}")
    ok = stuck is None and not cur
    for bp, c, meas, sb, eqsig in peeled:
        marker = "IH" if sb else ("BASE(=σ)" if eqsig else "??ABOVE??")
        print(f"    peel ψ_{bp}  coeff={c:+d}  (srRank,rowInv)={meas} "
              f"{'strictly-below' if sb else ('= σ measure' if eqsig else 'NOT BELOW!')} [{marker}]")
        if not sb and not eqsig:
            ok = False
    print(f"  RESULT: {'PASS' if ok else 'FAIL'}  "
          f"(Δ ∈ V via {len(peeled)} polytabloids, all col-std & dischargeable)")
    return ok


if __name__ == "__main__":
    results = []

    # ---- (2,2): canonical example from the refutation. ----
    # rows {0,1},{2,3}; cols {0,2},{1,3}.
    results.append(run(
        rowOf=[0, 0, 1, 1], colOf=[0, 1, 0, 1],
        sigma=(1, 0, 2, 3),   # swap(0,1)
        w=(2, 0, 1, 3),       # (0 2 1)
        label="(2,2)"))

    # ---- (3,2): genuine larger example. ----
    # positions 0..4: rows {0,1,2},{3,4}; cols {0,3},{1,4},{2}.
    rowOf = [0, 0, 0, 1, 1]
    colOf = [0, 1, 2, 0, 1]
    n = 5
    allp = list(permutations(range(n)))
    def _tab(a): return tuple(rowOf[a[k]] for k in range(n))
    def _inv(a):
        r = [0]*n
        for k in range(n): r[a[k]] = k
        return tuple(r)
    def _isColStd(a):
        ai = _inv(a)
        for p1 in range(n):
            for p2 in range(n):
                if colOf[p1] == colOf[p2] and rowOf[p1] < rowOf[p2]:
                    if not ai[p1] < ai[p2]: return False
        return True
    def _rowInv(a):
        ai = _inv(a); c = 0
        for p1 in range(n):
            for p2 in range(n):
                if rowOf[p1] == rowOf[p2] and colOf[p1] < colOf[p2] and ai[p2] < ai[p1]:
                    c += 1
        return c
    Q = [p for p in allp if all(colOf[p[k]] == colOf[k] for k in range(n))]
    P = [p for p in allp if all(rowOf[p[k]] == rowOf[k] for k in range(n))]
    # find a col-std sigma with rowInv>0 and a generic w with a unique col-restd.
    def _gamma_ok(sigma, w):
        for q in Q:
            base = tuple(w[_inv(q)[sigma[k]]] for k in range(n))  # w q^{-1} sigma
            cands = [g for g in Q if _isColStd(tuple(g[base[k]] for k in range(n)))]
            if len(cands) != 1: return False
        return True
    chosen = None
    ident = tuple(range(n))
    for sigma in allp:
        if not _isColStd(sigma) or _rowInv(sigma) == 0: continue
        for w in allp:
            if w in Q or w in P or w == ident: continue
            try:
                if _gamma_ok(sigma, w):
                    chosen = (sigma, w); break
            except AssertionError:
                continue
        if chosen: break
    assert chosen, "no (3,2) example found"
    results.append(run(rowOf, colOf, chosen[0], chosen[1], label="(3,2)"))

    print(f"\n{'='*70}\nALL PASS: {all(results)}")

"""
R2.b validation (issue #4593) — TRUE polytabloid decomposition of Δ and f_w(σ).

Rather than naive leading-tabloid peeling (which is ambiguous: a tabloid class
can have several column-standard representatives, e.g. (0,1,0,1) on (2,2)), we
solve the linear system directly:

  express  Δ  and  f_w(σ)  in the basis  { ψ_τ : τ column-standard }  of V,

using exact rational linear algebra over the tabloid coordinates.  We then read
off which τ appear and check each has (srRank τ, rowInv τ) ≤lex (srRank σ, rowInv σ)
— i.e. each is dischargeable by the inductive hypothesis (strictly below) or by
the unconditional base lemma (= σ measure).  This is the structural fact R2.b
needs: Δ ∈ V is witnessed by polytabloids at ≤ σ rank.
"""
from itertools import permutations
from fractions import Fraction


def run(rowOf, colOf, sigma, w, label):
    n = len(rowOf)
    print(f"\n{'='*70}\n{label}: n={n} rowOf={rowOf} colOf={colOf} sigma={sigma} w={w}")

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
    def tab(a): return tuple(rowOf[a[k]] for k in range(n))
    def isColStd(a):
        ai = inv(a)
        for p1 in range(n):
            for p2 in range(n):
                if colOf[p1] == colOf[p2] and rowOf[p1] < rowOf[p2]:
                    if not ai[p1] < ai[p2]: return False
        return True
    def isRowStd(a):
        ai = inv(a)
        for p1 in range(n):
            for p2 in range(n):
                if rowOf[p1] == rowOf[p2] and colOf[p1] < colOf[p2]:
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

    all_tabs = sorted(set(tab(a) for a in allp))
    tab_index = {t: i for i, t in enumerate(all_tabs)}
    def srRank_tab(t):
        # codebase srRank σ = #{ tabloids strictly dominated BY [σ] } (below σ).
        a0 = next(a for a in allp if tab(a) == t)
        return sum(1 for s in all_tabs
                   if s != t and dominates(a0, next(a for a in allp if tab(a) == s)))

    # ψ_τ as a coordinate vector over all_tabs.
    def psi_vec(tauperm):
        v = [Fraction(0)]*len(all_tabs)
        for p in Q:
            v[tab_index[tab(mul(inv(p), tauperm))]] += sign(p)
        return v

    assert isColStd(sigma) and rowInv(sigma) > 0
    assert w not in Q and w not in P and w != tuple(range(n))

    def gamma(q):
        base = mul(w, mul(inv(q), sigma))
        cands = [g for g in Q if isColStd(mul(g, base))]
        assert len(cands) == 1
        return cands[0]
    def tau(q): return mul(gamma(q), mul(w, mul(inv(q), sigma)))
    def inR(q):
        t = tau(q)
        return strictDom(sigma, t) or (tab(t) == tab(sigma) and rowInv(t) < rowInv(sigma))
    R = [q for q in Q if inR(q)]

    # f_w(σ) and twistedIHPart and Δ as coordinate vectors.
    fw = [Fraction(0)]*len(all_tabs)
    for q in Q:
        fw[tab_index[tab(mul(w, mul(inv(q), sigma)))]] += sign(q)
    ihp = [Fraction(0)]*len(all_tabs)
    for q in R:
        wq = mul(w, mul(inv(q), sigma))
        pv = psi_vec(wq)
        for i in range(len(all_tabs)): ihp[i] += sign(q)*pv[i]
    Delta = [fw[i] - ihp[i] for i in range(len(all_tabs))]

    # Basis of V: ψ_τ over column-standard τ.  We want the (unique) expansion of
    # a target in terms of a triangular basis indexed by SYTs would be cleanest;
    # but to expose ALL constituents we solve target = Σ x_τ ψ_τ over col-std τ,
    # using the SYT polytabloids as a genuine basis (they are independent and
    # span V).  Map each col-std τ contribution; here we use SYT basis.
    SYT = [a for a in allp if isColStd(a) and isRowStd(a)]
    cols = [psi_vec(a) for a in SYT]

    # Solve [cols] x = target by Gaussian elimination (exact).
    def solve(target):
        m = len(all_tabs); k = len(cols)
        A = [[cols[j][i] for j in range(k)] + [target[i]] for i in range(m)]
        piv = []
        r = 0
        for col in range(k):
            pr = next((rr for rr in range(r, m) if A[rr][col] != 0), None)
            if pr is None: continue
            A[r], A[pr] = A[pr], A[r]
            pivval = A[r][col]
            A[r] = [x/pivval for x in A[r]]
            for rr in range(m):
                if rr != r and A[rr][col] != 0:
                    f = A[rr][col]
                    A[rr] = [A[rr][c] - f*A[r][c] for c in range(k+1)]
            piv.append((r, col)); r += 1
        # consistency
        for rr in range(r, m):
            if A[rr][k] != 0: return None
        x = [Fraction(0)]*k
        for (rr, col) in piv: x[col] = A[rr][k]
        return x

    sig_meas = (srRank_tab(tab(sigma)), rowInv(sigma))
    print(f"  |Q|={len(Q)} |R|={len(R)} |SYT|={len(SYT)}  σ measure (srRank,rowInv)={sig_meas}")

    for name, target in [("f_w(σ)", fw), ("Δ", Delta)]:
        x = solve(target)
        if x is None:
            print(f"  {name}: NOT IN V  <-- unexpected!"); continue
        terms = [(SYT[j], x[j]) for j in range(len(SYT)) if x[j] != 0]
        print(f"  {name} ∈ V as {len(terms)} SYT-polytabloid(s):")
        ok = True
        for tperm, coeff in terms:
            meas = (srRank_tab(tab(tperm)), rowInv(tperm))
            rel = ("strictly-below" if meas < sig_meas else
                   ("= σ measure (base lemma)" if meas == sig_meas else "ABOVE σ!"))
            if meas > sig_meas: ok = False
            print(f"     {coeff:+} · e_{tperm}   measure={meas}  [{rel}]")
        print(f"     => {name}: {'PASS (all ≤ σ)' if ok else 'FAIL (constituent above σ)'}")


if __name__ == "__main__":
    run([0, 0, 1, 1], [0, 1, 0, 1], (1, 0, 2, 3), (2, 0, 1, 3), "(2,2)")

    # (3,2): find first valid (sigma, w).
    rowOf = [0, 0, 0, 1, 1]; colOf = [0, 1, 2, 0, 1]; n = 5
    allp = list(permutations(range(n)))
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
                if rowOf[p1] == rowOf[p2] and colOf[p1] < colOf[p2] and ai[p2] < ai[p1]: c += 1
        return c
    Q = [p for p in allp if all(colOf[p[k]] == colOf[k] for k in range(n))]
    P = [p for p in allp if all(rowOf[p[k]] == rowOf[k] for k in range(n))]
    ident = tuple(range(n))
    def gamma_ok(sigma, w):
        for q in Q:
            base = tuple(w[_inv(q)[sigma[k]]] for k in range(n))
            if len([g for g in Q if _isColStd(tuple(g[base[k]] for k in range(n)))]) != 1:
                return False
        return True
    chosen = None
    for sigma in allp:
        if not _isColStd(sigma) or _rowInv(sigma) == 0: continue
        for w in allp:
            if w in Q or w in P or w == ident: continue
            if gamma_ok(sigma, w): chosen = (sigma, w); break
        if chosen: break
    run(rowOf, colOf, chosen[0], chosen[1], "(3,2)")

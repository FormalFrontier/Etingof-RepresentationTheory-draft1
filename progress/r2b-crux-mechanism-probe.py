# Find the REAL reason the dominance-maximal tabloid of Delta is col-std-izable.
# Investigate: what IS beta_max?  Is it [sigma]?  Is it some [tau_q]?  Is the
# maximal tabloid of Delta always EQUAL to the maximal tabloid of f_w, and is
# that maximal-of-f_w col-std-izable (even though lower f_w terms are not)?
from itertools import permutations
import random

def test_shape(rowOf, colOf, trials):
    n = len(rowOf)
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
                if colOf[p1] == colOf[p2] and rowOf[p1] < rowOf[p2] and not ai[p1] < ai[p2]:
                    return False
        return True
    allp = list(permutations(range(n)))
    Q = [p for p in allp if all(colOf[p[k]] == colOf[k] for k in range(n))]
    Pset = set(p for p in allp if all(rowOf[p[k]] == rowOf[k] for k in range(n)))
    def cumul(a, k, i): return sum(1 for e in range(n) if e <= k and rowOf[a[e]] < i)
    def dom(a, b): return all(cumul(b, k, i) <= cumul(a, k, i) for k in range(n) for i in range(n+1))
    def strictDom(a, b): return dom(a, b) and tab(a) != tab(b)
    def rowInv(a):
        ai = inv(a); c = 0
        for p1 in range(n):
            for p2 in range(n):
                if rowOf[p1] == rowOf[p2] and colOf[p1] < colOf[p2] and ai[p2] < ai[p1]: c += 1
        return c
    tabs = sorted(set(tab(a) for a in allp))
    rep = {t: next(a for a in allp if tab(a) == t) for t in tabs}
    colstd_tabs = {t for t in tabs if any(tab(a) == t and isColStd(a) for a in allp)}
    def psi(tauperm):
        v = {}
        for p in Q:
            t = tab(mul(inv(p), tauperm)); v[t] = v.get(t, 0) + sign(p)
        return {t: c for t, c in v.items() if c}
    def gamma_unique(sigma, w):
        for q in Q:
            base = mul(w, mul(inv(q), sigma))
            if len([g for g in Q if isColStd(mul(g, base))]) != 1: return False
        return True
    def tau(sigma, w, q):
        base = mul(w, mul(inv(q), sigma))
        g = [g for g in Q if isColStd(mul(g, base))][0]
        return mul(g, base)

    sigmas = [s for s in allp if isColStd(s) and rowInv(s) > 0]
    tested = 0
    fwmax_colstd_viol = 0      # is the MAXIMAL tabloid of f_w col-std-izable?
    deltamax_eq_fwmax = 0      # does max(Delta) == max(f_w) ?
    deltamax_eq_sigma = 0
    n_deltamax = 0
    for _ in range(trials):
        sigma = random.choice(sigmas)
        ws = [w for w in allp if w not in Q and w not in Pset and w != tuple(range(n))]
        random.shuffle(ws)
        w = None
        for cand in ws:
            if gamma_unique(sigma, cand): w = cand; break
        if w is None: continue
        tested += 1
        sig_t = tab(sigma)
        def inR(q):
            t = tau(sigma, w, q)
            return strictDom(sigma, t) or (tab(t) == tab(sigma) and rowInv(t) < rowInv(sigma))
        R = [q for q in Q if inR(q)]
        fw = {}
        for q in Q:
            t = tab(mul(w, mul(inv(q), sigma))); fw[t] = fw.get(t, 0) + sign(q)
        fw = {t: c for t, c in fw.items() if c}
        tIH = {}
        for q in R:
            for t, c in psi(mul(w, mul(inv(q), sigma))).items():
                tIH[t] = tIH.get(t, 0) + sign(q)*c
        delta = {t: fw.get(t, 0) - tIH.get(t, 0) for t in set(fw) | set(tIH)}
        delta = {t: c for t, c in delta.items() if c}
        if not delta: continue

        def maxima(d):
            supp = list(d)
            return [t for t in supp if not any(s != t and dom(rep[s], rep[t]) for s in supp)]
        dmax = maxima(delta)
        fmax = maxima(fw) if fw else []
        for bt in dmax:
            n_deltamax += 1
            if bt == sig_t: deltamax_eq_sigma += 1
            if bt in fmax: deltamax_eq_fwmax += 1
        # is each maximal tabloid of f_w col-std-izable?
        for bt in fmax:
            if bt not in colstd_tabs:
                fwmax_colstd_viol += 1
    print(f"shape {rowOf}: tested={tested} deltamax_count={n_deltamax}")
    print(f"   max(Delta)==[sigma]: {deltamax_eq_sigma}/{n_deltamax}")
    print(f"   max(Delta) in max(f_w): {deltamax_eq_fwmax}/{n_deltamax}")
    print(f"   max(f_w) NOT col-std-izable (violations): {fwmax_colstd_viol}")

random.seed(2)
test_shape([0,0,1,1], [0,1,0,1], 120)
test_shape([0,0,0,1,1], [0,1,2,0,1], 80)
test_shape([0,0,1,1,2], [0,1,0,1,0], 80)
test_shape([0,0,0,1,1,1], [0,1,2,0,1,2], 50)

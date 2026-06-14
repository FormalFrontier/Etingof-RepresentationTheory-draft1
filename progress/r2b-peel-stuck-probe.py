"""
R2.b peel "never-stuck" probe (issue #4605 / #4593 / sub-A #4630).

The leading-term-elimination Lean proof of `twistedPolytabloid_residual_in_V`
(Δ ∈ V) recurses: peel the dominance-maximal tabloid [β] of the *current*
residual, subtract c·ψ_{β'} for a column-standard rep β' of [β]. Each peeled
ψ_{β'} ∈ V unconditionally by `generalizedPolytabloidTab_mem_span_polytabloidTab`
(sorry-free), so the `ih` parameter is in fact redundant.

The ONLY structural fact the proof needs is: the peel never gets STUCK — i.e.
every dominance-maximal tabloid of every *intermediate* residual is
column-standardizable (has a col-std rep with the same tabloid). sub-A (#4630)
only guarantees this for the GLOBAL max of the ORIGINAL Garnir residual Δ;
intermediate residuals are NOT Garnir residuals. This probe stress-tests the
property on many random larger examples to see whether the recursion is sound.

Reports: stuck cases (non-col-std-izable maximal at some step), nontermination,
and the distribution of peel-step counts (to confirm multi-step peels occur).
"""
from itertools import permutations
import random


def build(rowOf, colOf):
    n = len(rowOf)
    allp = list(permutations(range(n)))

    def mul(a, b): return tuple(a[b[k]] for k in range(n))
    def inv(a):
        r = [0] * n
        for k in range(n): r[a[k]] = k
        return tuple(r)
    def sign(a):
        s = 1
        for i in range(n):
            for j in range(i + 1, n):
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
    def cumul(a, k, i): return sum(1 for e in range(n) if e <= k and rowOf[a[e]] < i)
    def dominates(a, b):
        return all(cumul(b, k, i) <= cumul(a, k, i) for k in range(n) for i in range(n + 1))
    def rowInv(a):
        ai = inv(a); c = 0
        for p1 in range(n):
            for p2 in range(n):
                if rowOf[p1] == rowOf[p2] and colOf[p1] < colOf[p2] and ai[p2] < ai[p1]:
                    c += 1
        return c
    Q = [p for p in allp if all(colOf[p[k]] == colOf[k] for k in range(n))]
    P = [p for p in allp if all(rowOf[p[k]] == rowOf[k] for k in range(n))]
    all_tabs = sorted(set(tab(a) for a in allp))
    rep = {t: next(a for a in allp if tab(a) == t) for t in all_tabs}
    colstd_tabs = {t for t in all_tabs if any(isColStd(a) for a in allp if tab(a) == t)}

    def psi(tp):
        d = {}
        for p in Q:
            t = tab(mul(inv(p), tp))
            d[t] = d.get(t, 0) + sign(p)
        return {t: c for t, c in d.items() if c != 0}

    return dict(n=n, allp=allp, mul=mul, inv=inv, sign=sign, tab=tab,
                isColStd=isColStd, dominates=dominates, rowInv=rowInv, Q=Q, P=P,
                all_tabs=all_tabs, rep=rep, colstd_tabs=colstd_tabs, psi=psi)


def colstd_rep(E, t):
    for a in E["allp"]:
        if E["tab"](a) == t and E["isColStd"](a):
            return a
    return None


def residual(E, sigma, w):
    """Δ := f_w(σ) − twistedIHPart σ w, as a dict tabloid->coeff."""
    mul, inv, sign, tab = E["mul"], E["inv"], E["sign"], E["tab"]
    Q, psi, dominates, rowInv = E["Q"], E["psi"], E["dominates"], E["rowInv"]

    def strictDom(a, b): return dominates(a, b) and tab(a) != tab(b)

    # τ_q via the canonical column-restandardizer γ_q ∈ Q.
    def tau(q):
        base = mul(w, mul(inv(q), sigma))
        g = next(g for g in Q if E["isColStd"](mul(g, base)))
        return mul(g, base)

    def inR(q):
        t = tau(q)
        if strictDom(sigma, t): return True
        if tab(t) == tab(sigma) and rowInv(t) < rowInv(sigma): return True
        return False
    R = [q for q in Q if inR(q)]

    fw = {}
    for q in Q:
        t = tab(mul(w, mul(inv(q), sigma)))
        fw[t] = fw.get(t, 0) + sign(q)
    ih = {}
    for q in R:
        for t, c in psi(mul(w, mul(inv(q), sigma))).items():
            ih[t] = ih.get(t, 0) + sign(q) * c
    D = {}
    for t in set(fw) | set(ih):
        c = fw.get(t, 0) - ih.get(t, 0)
        if c != 0: D[t] = c
    return D


def peel(E, D):
    """Run leading-term elimination. Return (status, steps)."""
    dominates, rep = E["dominates"], E["rep"]
    cur = dict(D)
    steps = 0
    while cur:
        steps += 1
        if steps > 100000:
            return ("NONTERM", steps)
        supp = list(cur)
        maximals = [t for t in supp
                    if not any(s != t and t != s and dominates(rep[s], rep[t]) and rep_tab_ne(E, s, t)
                               for s in supp)]
        beta = maximals[0]
        bp = colstd_rep(E, beta)
        if bp is None:
            return (("STUCK", beta, len(supp), steps), steps)
        c = cur[beta]
        for t, v in E["psi"](bp).items():
            cur[t] = cur.get(t, 0) - c * v
        cur = {t: v for t, v in cur.items() if v != 0}
    return ("OK", steps)


def rep_tab_ne(E, s, t):
    return s != t


def main():
    random.seed(20260615)
    shapes = [
        ([0, 0, 1, 1], [0, 1, 0, 1]),                 # (2,2)
        ([0, 0, 0, 1, 1], [0, 1, 2, 0, 1]),           # (3,2)
        ([0, 0, 1, 1, 2], [0, 1, 0, 1, 0]),           # (2,2,1)
        ([0, 0, 0, 1, 1, 1], [0, 1, 2, 0, 1, 2]),     # (3,3)
        ([0, 0, 0, 1, 1, 2], [0, 1, 2, 0, 1, 0]),     # (3,2,1)
    ]
    total = stuck = nonterm = 0
    maxsteps = 0
    multistep = 0
    stuck_examples = []
    for rowOf, colOf in shapes:
        E = build(rowOf, colOf)
        allp, Q, P, isColStd, rowInv = E["allp"], E["Q"], E["P"], E["isColStd"], E["rowInv"]
        n = E["n"]
        idp = tuple(range(n))
        sigmas = [a for a in allp if isColStd(a) and rowInv(a) > 0]
        ws = [a for a in allp if a not in Q and a not in P and a != idp]
        # sample to keep runtime reasonable on the larger shapes
        pairs = [(s, w) for s in sigmas for w in ws]
        random.shuffle(pairs)
        pairs = pairs[:400]
        sc = 0
        for sigma, w in pairs:
            D = residual(E, sigma, w)
            if not D:
                total += 1
                continue
            status, steps = peel(E, D)
            total += 1
            maxsteps = max(maxsteps, steps)
            if steps > 1:
                multistep += 1
            if status == "NONTERM":
                nonterm += 1
            elif isinstance(status, tuple) and status[0] == "STUCK":
                stuck += 1; sc += 1
                if len(stuck_examples) < 5:
                    stuck_examples.append((rowOf, colOf, sigma, w, status))
        print(f"shape rowOf={rowOf} colOf={colOf}: tested {len(pairs)} (σ,w) pairs, stuck={sc}")
    print(f"\nTOTAL tested={total}  stuck={stuck}  nonterm={nonterm}  "
          f"multistep-peels={multistep}  max-steps={maxsteps}")
    for ex in stuck_examples:
        print("  STUCK:", ex)
    print("VERDICT:", "PEEL NEVER STUCK ✓" if (stuck == 0 and nonterm == 0)
          else "PEEL CAN GET STUCK ✗ — route unsound as stated")


if __name__ == "__main__":
    main()

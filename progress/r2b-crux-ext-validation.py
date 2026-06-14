# Extension of /tmp/r2b_crux.py per issue #4604:
# For every NON-column-standardizable tabloid [beta] in supp(Delta), confirm
#   (a) [beta] is NON-maximal in supp(Delta)  (so the maximal one is always col-std-izable)
#   (b) the coset {q in Q : [w q^-1 sigma] = [beta]} has stabiliser
#         H = Q cap w^-1 (Row) w  containing an odd element
#       => the f_w coefficient at [beta] is 0 (the col-antisymmetry cancellation).
# Also confirm the clean lemma: f_w([beta]) != 0  =>  [beta] is col-std-izable.
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
    P = [p for p in allp if all(rowOf[p[k]] == rowOf[k] for k in range(n))]
    Pset = set(P)
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
    # H = Q cap w^-1 P w  (stabiliser of the fiber [w q^-1 sigma])
    def stabiliser(w):
        wi = inv(w)
        H = [h for h in Q if mul(w, mul(h, wi)) in Pset]
        return H

    sigmas = [s for s in allp if isColStd(s) and rowInv(s) > 0]
    n_fw_nonzero_check = 0   # f_w coeff != 0 => col-std-izable
    n_fw_violation = 0
    n_noncs_in_delta = 0     # non-col-std tabloids appearing in supp(Delta)
    n_noncs_maximal = 0      # ... that are MAXIMAL (should be 0)
    n_coset_cancel_ok = 0    # fiber stabiliser has odd elt => f_w coeff 0 (verify)
    n_coset_cancel_bad = 0
    tested = 0
    for _ in range(trials):
        sigma = random.choice(sigmas)
        ws = [w for w in allp if w not in Q and w not in Pset and w != tuple(range(n))]
        random.shuffle(ws)
        w = None
        for cand in ws:
            if gamma_unique(sigma, cand): w = cand; break
        if w is None: continue
        tested += 1
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

        # --- clean lemma: f_w coeff != 0 => col-std-izable ---
        for t, c in fw.items():
            n_fw_nonzero_check += 1
            if t not in colstd_tabs:
                n_fw_violation += 1
                print(f"  FW-VIOLATION sigma={sigma} w={w} beta={t} coeff={c}")

        # --- coset cancellation mechanism: stabiliser odd-elt => fw coeff 0 ---
        H = stabiliser(w)
        H_has_odd = any(sign(h) == -1 for h in H)
        if H_has_odd:
            # every fiber sum must vanish => fw identically 0 on all tabloids
            if all(c == 0 for c in fw.values()) and len(fw) == 0:
                n_coset_cancel_ok += 1
            else:
                # fw nonempty: check each present coeff really used a fiber w/o odd stab.
                # Recompute per-fiber: group q by tab(w q^-1 sigma); the present ones
                # must have coset-sum != 0 which forces (for that coset) all-even -- but
                # H is global. If H has an odd elt, EVERY fiber sum is 0 => fw empty.
                n_coset_cancel_bad += 1
                print(f"  COSET-BAD sigma={sigma} w={w}: H has odd but fw nonempty {fw}")
        else:
            n_coset_cancel_ok += 1

        # --- non-col-std tabloids in Delta must be non-maximal ---
        supp = list(delta)
        maximals = [t for t in supp if not any(s != t and dom(rep[s], rep[t]) for s in supp)]
        for t in supp:
            if t not in colstd_tabs:
                n_noncs_in_delta += 1
                if t in maximals:
                    n_noncs_maximal += 1
                    print(f"  MAXIMAL-NONCS sigma={sigma} w={w} beta={t}")
    print(f"shape rowOf={rowOf}: tested={tested}")
    print(f"   f_w nonzero coeffs checked={n_fw_nonzero_check} violations(non-colstd)={n_fw_violation}")
    print(f"   coset-cancel: ok={n_coset_cancel_ok} bad={n_coset_cancel_bad}")
    print(f"   non-colstd-in-Delta={n_noncs_in_delta}  of which MAXIMAL={n_noncs_maximal}")

random.seed(1)
test_shape([0,0,1,1], [0,1,0,1], 80)
test_shape([0,0,0,1,1], [0,1,2,0,1], 60)
test_shape([0,0,1,1,2], [0,1,0,1,0], 60)   # (2,2,1)
test_shape([0,0,0,1,1,1], [0,1,2,0,1,2], 30) # (3,3)

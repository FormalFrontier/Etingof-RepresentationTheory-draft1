# Decisive test: is the dominance-MAXIMAL support tabloid of Delta (and of every
# leading-term elimination remainder) always column-standardizable AND
# IH-available (strictly below sigma, or =sigma)?  If yes broadly, the crux
# structural lemma holds and the elimination never gets stuck.
from itertools import permutations
import random
def test_shape(rowOf,colOf,trials):
    n=len(rowOf)
    def mul(a,b): return tuple(a[b[k]] for k in range(n))
    def inv(a):
        r=[0]*n
        for k in range(n): r[a[k]]=k
        return tuple(r)
    def sign(a):
        s=1
        for i in range(n):
            for j in range(i+1,n):
                if a[i]>a[j]: s=-s
        return s
    def tab(a): return tuple(rowOf[a[k]] for k in range(n))
    def isColStd(a):
        ai=inv(a)
        for p1 in range(n):
            for p2 in range(n):
                if colOf[p1]==colOf[p2] and rowOf[p1]<rowOf[p2] and not ai[p1]<ai[p2]: return False
        return True
    allp=list(permutations(range(n)))
    Q=[p for p in allp if all(colOf[p[k]]==colOf[k] for k in range(n))]
    P=[p for p in allp if all(rowOf[p[k]]==rowOf[k] for k in range(n))]
    def cumul(a,k,i): return sum(1 for e in range(n) if e<=k and rowOf[a[e]]<i)
    def dom(a,b): return all(cumul(b,k,i)<=cumul(a,k,i) for k in range(n) for i in range(n+1))
    def strictDom(a,b): return dom(a,b) and tab(a)!=tab(b)
    def rowInv(a):
        ai=inv(a); c=0
        for p1 in range(n):
            for p2 in range(n):
                if rowOf[p1]==rowOf[p2] and colOf[p1]<colOf[p2] and ai[p2]<ai[p1]: c+=1
        return c
    tabs=sorted(set(tab(a) for a in allp)); idx={t:i for i,t in enumerate(tabs)}
    rep={t:next(a for a in allp if tab(a)==t) for t in tabs}
    colstd_tabs={t for t in tabs if any(tab(a)==t and isColStd(a) for a in allp)}
    def psi(tauperm):
        v={}
        for p in Q:
            t=tab(mul(inv(p),tauperm)); v[t]=v.get(t,0)+sign(p)
        return {t:c for t,c in v.items() if c}
    def gamma_unique(sigma,w):
        for q in Q:
            base=mul(w,mul(inv(q),sigma))
            if len([g for g in Q if isColStd(mul(g,base))])!=1: return False
        return True
    def tau(sigma,w,q):
        base=mul(w,mul(inv(q),sigma))
        g=[g for g in Q if isColStd(mul(g,base))][0]
        return mul(g,base)
    sigmas=[s for s in allp if isColStd(s) and rowInv(s)>0]
    stuck=0; above=0; ok=0; tested=0
    for _ in range(trials):
        sigma=random.choice(sigmas)
        ws=[w for w in allp if w not in Q and w not in P and w!=tuple(range(n))]
        random.shuffle(ws)
        w=None
        for cand in ws:
            if gamma_unique(sigma,cand): w=cand; break
        if w is None: continue
        def inR(q):
            t=tau(sigma,w,q); return strictDom(sigma,t) or (tab(t)==tab(sigma) and rowInv(t)<rowInv(sigma))
        R=[q for q in Q if inR(q)]
        fw={}
        for q in Q:
            t=tab(mul(w,mul(inv(q),sigma))); fw[t]=fw.get(t,0)+sign(q)
        tIH={}
        for q in R:
            for t,c in psi(mul(w,mul(inv(q),sigma))).items():
                tIH[t]=tIH.get(t,0)+sign(q)*c
        cur={t:fw.get(t,0)-tIH.get(t,0) for t in set(fw)|set(tIH)}
        cur={t:c for t,c in cur.items() if c}
        tested+=1
        sig_t=tab(sigma)
        # elimination
        bad=False
        steps=0
        while cur and not bad:
            steps+=1
            if steps>2000: bad="loop"; break
            supp=list(cur)
            maximals=[t for t in supp if not any(s!=t and dom(rep[s],rep[t]) for s in supp)]
            beta=maximals[0]
            if beta not in colstd_tabs:
                bad="STUCK-noColStd-maximal"; stuck+=1; break
            # IH-availability: need a col-std rep strictly below sigma, or =sigma(SYT route)
            # check tabloid relation
            if beta==sig_t:
                pass # =sigma branch: handled via SYT (rowInv 0 < rowInv sigma) — OK
            elif strictDom(sig_t and rep[sig_t], rep[beta]) if False else dom(rep[sig_t],rep[beta]) and beta!=sig_t:
                pass # strictly below sigma -> IH ok
            else:
                bad="MAXIMAL-not-below-sigma"; above+=1; break
            # peel using SOME col-std rep
            bp=next(a for a in allp if tab(a)==beta and isColStd(a))
            c=cur[beta]
            for t,v in psi(bp).items(): cur[t]=cur.get(t,0)-c*v
            cur={t:v for t,v in cur.items() if v}
        if not bad and not cur: ok+=1
        elif not bad and cur: bad="nonzero-remainder"
        if bad: print(f"  FAIL sigma={sigma} w={w}: {bad}")
    print(f"shape rowOf={rowOf}: tested={tested} ok={ok} stuck={stuck} above={above}")
random.seed(1)
test_shape([0,0,1,1],[0,1,0,1],60)
test_shape([0,0,0,1,1],[0,1,2,0,1],40)
test_shape([0,0,1,1,2],[0,1,0,1,0],40)   # (2,2,1)
test_shape([0,0,0,1,1,1],[0,1,2,0,1,2],20) # (3,3)

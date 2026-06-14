from itertools import permutations

rowOf=[0,0,1,1]; colOf=[0,1,0,1]; n=4
def mul(a,b): return tuple(a[b[k]] for k in range(n))   # (a*b)(k)=a(b(k))
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
def tab(a): return tuple(rowOf[a[k]] for k in range(n))   # entry k -> row
def isColStd(a):
    ai=inv(a)
    for p1 in range(n):
        for p2 in range(n):
            if colOf[p1]==colOf[p2] and rowOf[p1]<rowOf[p2]:
                if not ai[p1]<ai[p2]: return False
    return True
allp=list(permutations(range(n)))
Q=[p for p in allp if all(colOf[p[k]]==colOf[k] for k in range(n))]
Rsub=[p for p in allp if all(rowOf[p[k]]==rowOf[k] for k in range(n))]
def cumul(a,k,i): return sum(1 for e in range(n) if e<=k and rowOf[a[e]]<i)
def dominates(a,b): return all(cumul(b,k,i)<=cumul(a,k,i) for k in range(n) for i in range(n+1))
def strictDom(a,b): return dominates(a,b) and tab(a)!=tab(b)
def rowInv(a):
    ai=inv(a); c=0
    for p1 in range(n):
        for p2 in range(n):
            if rowOf[p1]==rowOf[p2] and colOf[p1]<colOf[p2] and ai[p2]<ai[p1]: c+=1
    return c
# tabloid with no col-std rep:
tabs_with_colstd=set(tab(a) for a in allp if isColStd(a))
all_tabs=set(tab(a) for a in allp)
no_colstd=all_tabs-tabs_with_colstd

sigma=(1,0,2,3)  # swap(0,1)
w=(2,0,1,3)      # (0 2 1): w(0)=2,w(1)=0,w(2)=1,w(3)=3
assert isColStd(sigma)

def gamma(q):
    base=mul(w,mul(inv(q),sigma))     # w q^{-1} sigma
    cands=[g for g in Q if isColStd(mul(g,base))]
    assert len(cands)==1, (q,len(cands))
    return cands[0]
def tau(q): return mul(gamma(q),mul(w,mul(inv(q),sigma)))

# regions
def inR(q):
    t=tau(q)
    if strictDom(sigma,t): return True
    if tab(t)==tab(sigma) and rowInv(t)<rowInv(sigma): return True
    return False
R=[q for q in Q if inR(q)]

def fw(alpha_tab):
    return sum(sign(q)*(1 if tab(mul(w,mul(inv(q),sigma)))==alpha_tab else 0) for q in Q)
def psi(tauperm, alpha_tab):
    return sum(sign(p)*(1 if tab(mul(inv(p),tauperm))==alpha_tab else 0) for p in Q)
def IHpart(alpha_tab):
    return sum(sign(q)*psi(mul(w,mul(inv(q),sigma)), alpha_tab) for q in R)
def Delta(alpha_tab):
    return fw(alpha_tab)-IHpart(alpha_tab)

print("rowInv(sigma)=",rowInv(sigma))
print("no-col-std tabloids:",sorted(no_colstd))
print("all tabloids:",sorted(all_tabs))
bad=[]
for t in sorted(all_tabs):
    d=Delta(t)
    flag=""
    if t in no_colstd: flag="NO-COLSTD"
    # strictly below sigma?
    below = strictDom(sigma, next(a for a in allp if tab(a)==t)) if t!=tab(sigma) else False
    print(f"tab={t} Delta={d:2d} fw={fw(t):2d} IH={IHpart(t):2d} {flag} below={below}")
    if t in no_colstd and d!=0:
        bad.append((t,d))
print("VIOLATIONS (no-colstd & Delta!=0):", bad)

print("\n=== region debug ===")
print("|Q|=",len(Q),"|R|=",len(R))
for q in Q:
    base=mul(w,mul(inv(q),sigma))
    g=gamma(q); t=tau(q)
    reg="low" if strictDom(sigma,t) else ("eq" if (tab(t)==tab(sigma) and rowInv(t)<rowInv(sigma)) else ("eqHi" if tab(t)==tab(sigma) else "high"))
    print(f"q={q} sgn={sign(q):2d} base_tab={tab(base)} gamma={g} tau={t} tau_tab={tab(t)} rowInv_tau={rowInv(t)} region={reg} inR={q in R}")

# validate against meditate: Delta should equal -psi_{(1,3,0,2)} ((0 1 3 2) cycle)
t0=(1,3,0,2)
print("\n(0132) isColStd:",isColStd(t0),"tab=",tab(t0))
print("compare Delta vs -psi_(0132):")
ok=True
for t in sorted(all_tabs):
    d=Delta(t); e=-psi(t0,t)
    if d!=e: ok=False
    print(f"tab={t} Delta={d:2d} -psi={e:2d} {'OK' if d==e else 'MISMATCH'}")
print("Delta == -psi_(0132) everywhere:", ok)

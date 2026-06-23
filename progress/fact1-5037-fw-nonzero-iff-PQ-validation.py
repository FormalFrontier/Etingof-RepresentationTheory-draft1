import itertools, random
def make_shape(parts):
    n=sum(parts); rowOfPos=[]; colOfPos=[]
    for r,length in enumerate(parts):
        for c in range(length):
            rowOfPos.append(r); colOfPos.append(c)
    return n,rowOfPos,colOfPos
def sign(perm):
    n=len(perm); seen=[False]*n; s=1
    for i in range(n):
        if not seen[i]:
            l=0; j=i
            while not seen[j]:
                seen[j]=True; j=perm[j]; l+=1
            if l%2==0: s=-s
    return s
def compose(a,b): return tuple(a[b[i]] for i in range(len(a)))
def inv(a):
    r=[0]*len(a)
    for i,v in enumerate(a): r[v]=i
    return tuple(r)
def subgroup_within(n, key):
    groups={}
    for p in range(n): groups.setdefault(key[p],[]).append(p)
    gl=list(groups.values()); result=[]
    for choice in itertools.product(*[list(itertools.permutations(g)) for g in gl]):
        q=[0]*n
        for g,perm in zip(gl,choice):
            for orig,img in zip(g,perm): q[orig]=img
        result.append(tuple(q))
    return result
def is_colstd(sigma,n,rowOfPos,colOfPos):
    sinv=inv(sigma)
    for p1 in range(n):
        for p2 in range(n):
            if colOfPos[p1]==colOfPos[p2] and rowOfPos[p1]<rowOfPos[p2]:
                if not (sinv[p1]<sinv[p2]): return False
    return True
def tabloid(sigma,n,rowOfPos): return tuple(rowOfPos[sigma[e]] for e in range(n))
def fw(w,sigma,Q,n,rowOfPos):
    coeff={}
    for q in Q:
        perm=compose(w,compose(inv(q),sigma))
        t=tabloid(perm,n,rowOfPos)
        coeff[t]=coeff.get(t,0)+sign(q)
    return {t:c for t,c in coeff.items() if c!=0}

def run(parts, wsample=None):
    n,rowOfPos,colOfPos=make_shape(parts)
    Q=subgroup_within(n,colOfPos)       # column subgroup (within columns)
    P=subgroup_within(n,rowOfPos)       # row subgroup (within rows)
    PQ=set(compose(p,q) for p in P for q in Q)
    allperms=list(itertools.permutations(range(n)))
    colstd=[s for s in allperms if is_colstd(s,n,rowOfPos,colOfPos)]
    if wsample is None: ws=allperms
    else:
        random.seed(0); ws=random.sample(allperms, min(wsample,len(allperms)))
    bad_iff=0; bad_coeff=0; total=0; coeff_vals=set()
    for sigma in colstd:
        tsig=tabloid(sigma,n,rowOfPos)
        for w in ws:
            total+=1
            supp=fw(w,sigma,Q,n,rowOfPos)
            nonzero = len(supp)>0
            inPQ = w in PQ
            # iff test
            if nonzero != inPQ: bad_iff+=1
            # coeff at [sigma]
            c = supp.get(tsig,0)
            coeff_vals.add(c)
            if nonzero != (c!=0): bad_coeff+=1
    print(f"shape {parts}: total={total}  (fw!=0 <=> w in PQ) violations={bad_iff}  "
          f"(fw!=0 <=> coeff_sig!=0) violations={bad_coeff}  coeff_sig values={sorted(coeff_vals)}")

for parts in [(2,2),(3,2),(2,2,1),(3,1),(2,1,1),(3,3)]:
    run(parts, wsample=(800 if sum(parts)>=6 else None))
for parts in [(4,2),(3,2,1),(2,2,2)]:
    run(parts, wsample=600)

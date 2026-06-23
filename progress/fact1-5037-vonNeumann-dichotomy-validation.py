import itertools, random
def make_shape(parts):
    n=sum(parts); rowOfPos=[]; colOfPos=[]
    for r,length in enumerate(parts):
        for c in range(length): rowOfPos.append(r); colOfPos.append(c)
    return n,rowOfPos,colOfPos
def compose(a,b): return tuple(a[b[i]] for i in range(len(a)))
def subgroup_within(n, key):
    groups={}
    for p in range(n): groups.setdefault(key[p],[]).append(p)
    gl=list(groups.values()); result=[]
    for choice in itertools.product(*[list(itertools.permutations(g)) for g in gl]):
        q=[0]*n
        for g,perm in zip(gl,choice):
            for o,im in zip(g,perm): q[o]=im
        result.append(tuple(q))
    return result
def run(parts,wsample=None):
    n,rowOfPos,colOfPos=make_shape(parts)
    Q=set(subgroup_within(n,colOfPos)); P=set(subgroup_within(n,rowOfPos))
    PQ=set(compose(p,q) for p in P for q in Q)
    allperms=list(itertools.permutations(range(n)))
    if wsample is None: ws=allperms
    else: random.seed(0); ws=random.sample(allperms,min(wsample,len(allperms)))
    viol=0
    for w in ws:
        # (a): exists a!=b same column, w(a),w(b) same row
        exists_pair=False
        for a in range(n):
            for b in range(a+1,n):
                if colOfPos[a]==colOfPos[b] and rowOfPos[w[a]]==rowOfPos[w[b]]:
                    exists_pair=True; break
            if exists_pair: break
        inPQ = w in PQ
        # dichotomy: exists_pair OR inPQ ; and they should be mutually exclusive
        if not (exists_pair or inPQ): viol+=1   # neither -> violation
        if exists_pair and inPQ: viol+=1        # both -> violation (should be exclusive)
    print(f"shape {parts}: dichotomy violations={viol} / {len(ws)}")
for parts in [(2,2),(3,2),(2,2,1),(3,1),(2,1,1),(3,3),(1,1,1,1),(4,1),(2,2,2),(3,2,1),(4,2)]:
    run(parts, wsample=(3000 if sum(parts)>6 else None))

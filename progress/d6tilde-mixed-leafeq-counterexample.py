#!/usr/bin/env python3
"""Exact-arithmetic refutation of `d6tildeRep_kQ_leaf_equalities` (and the d5
analog) in the MIXED-direction branches (combo C / combo C').

Context: issue #4631 asked for a "mixed-direction forcing lemma" to close
combo C (`FieldGenericD6Tilde.lean:710`) and combo C' (`:719`). No such lemma
can exist: the leaf-equality statement is FALSE in those branches because the
current under-coupled `d6tildeRep_kQ` is decomposable at m=1 (dimension vector
2*delta, delta = D~6 null root), and some direct-sum decompositions break the
claimed leaf equality.

We exhibit, over exact arithmetic, a complementary invariant pair
(W1 = im P, W2 = im (I-P)) for a rep-endomorphism idempotent P, with unequal
leaf subspaces. m = 1 throughout (leaf dim = 2, center dim = 4).

Run: python3 d6tilde-mixed-leafeq-counterexample.py   (needs sympy)

Verified results:
  combo C  (over Q): W1(leaf 0) = span{(7/6,1)} but W1(leaf 1) = 0  -> <0>=<1> FALSE
  combo C' :         W1(0)=W1(1)=W1(5) but W1(6) is the (I-N)-twisted line -> <0>=<6> FALSE

The fix is the homogeneous-tube redesign of the D~ family (#4597), not a
forcing lemma on the current construction.
"""
import sympy as sp

# m = 1. Vertices: leaves 0,1 -> center 2; path 2-3-4; leaves 5,6 -> center 4.
dim = {0: 2, 1: 2, 2: 4, 3: 4, 4: 4, 5: 2, 6: 2}

# Block maps (mirror FieldGenericStar.lean / FieldGenericD5Tilde.lean at m=1).
e1 = sp.Matrix([[1, 0], [0, 1], [0, 0], [0, 0]])          # starEmbed1_F : x -> (x,0)
e2 = sp.Matrix([[0, 0], [0, 0], [1, 0], [0, 1]])          # starEmbed2_F : x -> (0,x)
sFirst = sp.Matrix([[1, 0, 0, 0], [0, 1, 0, 0]])          # starFirst_F  : (a,b)->a
sSecond = sp.Matrix([[0, 0, 1, 0], [0, 0, 0, 1]])         # starSecond_F : (a,b)->b
gamma = sp.Matrix([[1, 0, 1, 0], [0, 1, 0, 1],            # d5tildeGamma_F = [[I,I],[I,N]]
                   [1, 0, 0, 1], [0, 1, 0, 0]])
I4 = sp.eye(4)


def endo_algebra(edges):
    verts = list(dim)
    sl = {}
    o = 0
    for v in verts:
        sl[v] = (o, o + dim[v] ** 2)
        o += dim[v] ** 2
    X = sp.symbols(f'x0:{o}')
    phi = {v: sp.Matrix(dim[v], dim[v],
                        lambda i, j: X[sl[v][0] + i * dim[v] + j]) for v in verts}
    eqs = [c for (a, b, M) in edges for c in list(M * phi[a] - phi[b] * M)]
    sols = list(sp.linsolve(eqs, X))[0]
    return X, phi, sols


def spectral_idem(edges, pt):
    """A rep-endomorphism idempotent P from a spectral projection of a generic
    point `pt` of the endomorphism algebra."""
    X, phi, sols = endo_algebra(edges)
    free = sorted(set().union(*[s.free_symbols for s in sols]), key=lambda t: t.name)
    sub = dict(zip(free, [sp.Rational(v) for v in pt]))
    phic = {v: phi[v].subs(dict(zip(X, sols))).subs(sub) for v in dim}
    lams = list(phic[2].eigenvals().keys())
    lam, others = lams[0], [mu for mu in lams if mu != lams[0]]
    P = {}
    for v in dim:
        Pv = sp.eye(dim[v])
        for mu in others:
            Pv = Pv * (phic[v] - mu * sp.eye(dim[v])) / (lam - mu)
        P[v] = sp.simplify(Pv)
    okE = all(sp.simplify(M * P[a] - P[b] * M) == sp.zeros(dim[b], dim[a])
              for (a, b, M) in edges)
    okI = all(sp.simplify(P[v] * P[v] - P[v]) == sp.zeros(dim[v], dim[v]) for v in dim)
    return P, okE, okI


def report(name, edges, pt):
    P, okE, okI = spectral_idem(edges, pt)
    print(f"=== {name} ===")
    print(f"  P is rep-endomorphism: {okE}; P idempotent: {okI}")
    for v in [0, 1, 5, 6]:
        cs = P[v].columnspace()
        print(f"  W1(leaf {v}) = " +
              ("0  (zero subspace)" if not cs else f"span{list(cs[0].T)}"))
    print()


if __name__ == "__main__":
    report("combo C  (5->4 canonical e1, 4->6 reversed starSecond)",
           [(0, 2, e1), (1, 2, e2), (2, 3, gamma), (3, 4, I4),
            (5, 4, e1), (4, 6, sSecond)], [2, 3, 5, 7, 11])
    report("combo C' (4->5 reversed starFirst, 6->4 canonical e2)",
           [(0, 2, e1), (1, 2, e2), (2, 3, gamma), (3, 4, I4),
            (4, 5, sFirst), (6, 4, e2)], [2, 3, 5, 7])

# Refutation of the per-summand vanishing route for fact 2 (#5097).
#
# The prior skip comment on #5097 proposed: show X(t)=0 for non-column-
# standardizable dominance-maximal t by "applying the column-violation Garnir
# involution to both f_w(σ)'s tabloid expansion and each e_T in M" — i.e. that
# every polytabloid e_T (and f_w(σ)) vanishes at every non-standardizable
# tabloid, so the vanishing is per-summand and fact 2 "follows in one line".
#
# This is FALSE. For λ=(2,1), T = [[0,1],[2]], the standard polytabloid e_T has
# coefficient -1 at the tabloid {{1,2},{0}}, which is NOT column-standardizable.
# Hence the residual vanishing X(t₁)=0 must come from genuine cross-cancellation
# between f_w(σ) and M, not from per-summand vanishing — exactly the issue body's
# "top term created by cancellation against M". Run with `python3`.
from itertools import permutations


def tabloid_of_rowsets(r0, r1):
    return (frozenset(r0), frozenset(r1))


def col_standardizable(tab):
    # shape (2,1): col0 spans rows {0,1}, col1 spans row {0}. Row r holds a SET
    # of values; column-standardizable = some within-row arrangement makes each
    # column strictly increase downward.
    r0 = sorted(tab[0])
    r1 = sorted(tab[1])
    for a in permutations(r0):           # a[0] -> (row0,col0), a[1] -> (row0,col1)
        if a[0] < r1[0]:                 # col0: (row0) < (row1)
            return True
    return False


# T = [[0,1],[2]]; Q_λ = {id, swap col0 (values 0,2)}; e_T = [T] - [swapped].
T_tab = tabloid_of_rowsets({0, 1}, {2})        # [T]
S_tab = tabloid_of_rowsets({2, 1}, {0})        # column swap of T's filling
print("T tabloid        ", T_tab, "standardizable:", col_standardizable(T_tab))
print("swapped (coeff -1)", S_tab, "standardizable:", col_standardizable(S_tab))
assert col_standardizable(T_tab)
assert not col_standardizable(S_tab)
print("REFUTED: e_T carries coeff -1 at a non-standardizable tabloid;",
      "per-summand vanishing is false.")

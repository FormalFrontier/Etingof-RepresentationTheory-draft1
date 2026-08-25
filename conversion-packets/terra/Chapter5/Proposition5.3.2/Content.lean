import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Proposition532

#doc (Manual) "The numbers lambda\\_i are algebraic integers" =>

# The numbers lambda\_i are algebraic integers
%%%
tag := "Chapter5/Proposition5.3.2"
number := false
%%%
**Proposition 5.3.2.** _The numbers $`\lambda_i` are algebraic integers for all $`i`._

**Proof.** Let $`C` be a conjugacy class in $`G`, and let $`P = \sum_{h \in C} h`. Then $`P` is a central element of $`\mathbb{Z}[G]`, so it acts on $`V` by some scalar $`\lambda`, which is an algebraic integer (indeed, since $`\mathbb{Z}[G]` is a finitely generated $`\mathbb{Z}`-module, any element of $`\mathbb{Z}[G]` is integral over $`\mathbb{Z}`, i.e., satisfies a monic polynomial equation with integer coefficients). On the other hand, taking the trace of $`P` in $`V`, we get $`|C|\chi_V(g) = \lambda \dim V`, $`g \in C`, so $`\lambda = \frac{|C|\chi_V(g)}{\dim V}`. $`\square`

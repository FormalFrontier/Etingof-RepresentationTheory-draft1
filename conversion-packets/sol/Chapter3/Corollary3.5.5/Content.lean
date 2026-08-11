import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Corollary355

#doc (Manual) "Sum of squares of dimensions of irreducibles bounded by dim A" =>
# Sum of squares of dimensions of irreducibles bounded by dim A
%%%
tag := "Chapter3/Corollary3.5.5"
number := false
%%%
**Corollary 3.5.5.** _$`\sum_i (\dim V_i)^2 \leq \dim A`, where the $`V_i`'s are the irreducible representations of $`A`._

## 3.5. Finite dimensional algebras
%%%
tag := "Chapter3/Corollary3.5.5/heading-1"
%%%

**Proof.** As $`\dim \operatorname{End} V_i = (\dim V_i)^2`, Theorem 3.5.4 implies that $`\dim A - \dim \operatorname{Rad}(A) = \sum_i \dim \operatorname{End} V_i = \sum_i (\dim V_i)^2`. As $`\dim \operatorname{Rad}(A) \geq 0`, $`\sum_i (\dim V_i)^2 \leq \dim A`. $`\square`

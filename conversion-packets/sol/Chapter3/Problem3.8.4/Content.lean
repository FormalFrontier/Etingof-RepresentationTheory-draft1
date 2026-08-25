import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Problem384

#doc (Manual) "Scalar extension and the Noether-Deuring theorem" =>

# Scalar extension and the Noether-Deuring theorem
%%%
tag := "Chapter3/Problem3.8.4"
number := false
%%%
**Problem 3.8.4.** (i) Let $`V, W` be finite dimensional representations of an algebra $`A` over a (not necessarily algebraically closed) field $`K`. Let $`L` be a field extension of $`K`. Suppose that $`V \otimes_K L` is isomorphic to $`W \otimes_K L` as a module over the $`L`-algebra $`A \otimes_K L`. Show that $`V` and $`W` are isomorphic as $`A`-modules.

Hint: Reduce to the case of finitely generated, then finite extension, of some degree $`n`. Then regard $`V \otimes_K L` and $`W \otimes_K L` as
$`A`-modules, and show that they are isomorphic to $`V^n` and $`W^n`, respectively. Deduce that $`V^n` is isomorphic to $`W^n`, and use the Krull-Schmidt theorem (valid over any field by Problem 3.8.3) to deduce that $`V` is isomorphic to $`W`.

(ii) (The Noether-Deuring theorem) In the setting of (i), suppose that $`V \otimes_K L` is a direct summand in $`W \otimes_K L` (i.e., $`W \otimes_K L \cong V \otimes_K L \oplus Y`, where $`Y` is a module over $`A \otimes_K L`). Show that $`V` is a direct summand in $`W`.

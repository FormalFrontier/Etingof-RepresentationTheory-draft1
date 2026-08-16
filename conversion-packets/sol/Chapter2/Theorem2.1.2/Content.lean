import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

-- The aligned inductive's constructors have no independent approved declaration docs.
set_option verso.docstring.allowMissing true

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Theorem212

#doc (Manual) "Gabriel's theorem: classification of quivers of finite type by Dynkin diagrams" =>
# Gabriel's theorem: classification of quivers of finite type by Dynkin diagrams
%%%
tag := "Chapter2/Theorem2.1.2"
number := false
%%%
We will prove the following striking theorem, proved by P. Gabriel in early 1970s.[^Chapter2/Theorem2.1.2/footnote-1]

**Theorem 2.1.2.** _The finite type property of $`Q` does not depend on the orientation of edges. The connected graphs that yield quivers of finite type are given by the following list:_

- _$`A_n`:_

  $$`\circ \text{---} \circ \text{---} \circ \text{-} \cdots \text{-} \circ \text{---} \circ \text{---} \circ`

- _$`D_n`:_

  $$`\begin{array}{ccccccccc}
  \circ & \text{---} & \circ & \text{---} & \circ & \text{-} & \cdots & \text{-} & \circ \\
  &&&& | \\
  &&&& \circ
  \end{array}`

- _$`E_6`:_

  $$`\begin{array}{ccccccccc}
  \circ & \text{---} & \circ & \text{---} & \circ & \text{---} & \circ & \text{---} & \circ \\
  &&&& | \\
  &&&& \circ
  \end{array}`

- _$`E_7`:_

  $$`\begin{array}{ccccccccccc}
  \circ & \text{---} & \circ & \text{---} & \circ & \text{---} & \circ & \text{---} & \circ & \text{---} & \circ \\
  &&&& | \\
  &&&& \circ
  \end{array}`

- _$`E_8`:_

  ```
  o——o——o——o——o——o——o
           |
           o
  ```

[^Chapter2/Theorem2.1.2/footnote-1]: We will prove this theorem when the field $`k` is algebraically closed, but it is valid even without this assumption.

The graphs listed in the theorem are called (simply laced) **Dynkin diagrams**. These graphs arise in a multitude of classification problems in mathematics, such as the classification of simple Lie algebras, singularities, platonic solids, reflection groups, etc. In fact, if we needed to make contact with an alien civilization and show them how sophisticated our civilization is, perhaps showing them Dynkin diagrams would be the best choice!

# Stage 3.4 kernel proof-term review

Completed 2026-08-01 using imported Lean kernel terms with opaque/theorem bodies enabled.

- Current root-imported modules: 840
- Declarations inspected: 33034
- Import-DAG edges: 521
- Mapped proof/type edges beyond the old import DAG: 209
- Old import edges not recovered through owned-module proof/type mapping (trimmed): 133
- Mapped proof/type relation edges: 597
- Cyclic item components in that relation: 6
- Explicitly recorded cycle edges excluded from the DAG: 8
- Shipped acyclic proof-term edges: 589
- Current sources outside the root import: 2
- Stale imported modules without source: 0

The JSON companion conservatively covers every source-level theorem/opaque declaration and its direct cross-module project-local type and proof-body constants, plus every other declaration that contributes a cross-module edge and the source, extractor, toolchain, raw-extraction, and build-log identity. Re-export implementation modules are attributed to the closest unambiguous explicit provider item; 209 root-imported modules without an unambiguous item owner remain in the declaration inventory but are not projected into the item graph. The shipped graph trims import edges not recovered through owned-module kernel mapping and includes every mapped proof edge compatible with acyclicity; each edge excluded for an item-coarsening cycle is named with its cycle path in the certificate.

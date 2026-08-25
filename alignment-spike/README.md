# Book reference attribute spike

This isolated Lean 4.32.2 package prototypes:

- `@[book_ref "Chapter6/Theorem6.5.2" (role := primary)]` and `supporting`;
- persistent declaration/reference/role metadata in an environment extension;
- canonical `@book-ref {JSON}` lines appended to compiled docstrings;
- deterministic JSON export of the complete example corpus, captured at compile time and printed by
  `lake exe export_book_refs`;
- build-time checks in `Tests.lean`.

Run `lake build`, `lake exe book_ref_tests`, and `lake exe export_book_refs`.

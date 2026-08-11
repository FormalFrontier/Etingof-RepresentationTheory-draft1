/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import RepresentationTheory

/-! Export the pinned formalization's declaration-to-source associations as JSON. -/

open RepresentationTheory.Alignment

set_option linter.hashCommand false

#define_source_refs_json sourceReferences

def main : IO Unit :=
  IO.println sourceReferences

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import RepresentationTheory

/-! Export declaration-to-source associations as JSON. -/

open RepresentationTheory.Alignment

set_option linter.hashCommand false

#define_source_refs_json sourceReferences

def main : IO Unit :=
  IO.println sourceReferences

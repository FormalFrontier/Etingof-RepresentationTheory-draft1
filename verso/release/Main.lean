/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import IntroductionToRepresentationTheoryVerso

open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 3

def main := manualMain (%doc IntroductionToRepresentationTheoryVerso) (config := config)

/-
  Sqrt2DocsMain.lean - Entry point for building documentation site

  Run with: lake exe sqrt2docs
-/

import VersoManual
import Sqrt2Docs

open Verso Doc
open Verso.Genre Manual

def config : Config where
  emitTeX := false
  emitHtmlSingle := true
  emitHtmlMulti := true
  htmlDepth := 2
  destination := "_out"

def main := manualMain (%doc Sqrt2Docs) (config := config)

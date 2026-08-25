import Mathlib.Lean.CoreM

open Lean

#check CoreM.toIO
#check CoreM.withImportModules
#check MetaM.toIO
#check MetaM.run
#check Meta.ppExpr
#check CoreM.run
#check liftM
#print MetaM
#check Meta.Context
#check Meta.State
#check ReaderT.run
#check StateRefT'.run

def runMeta {α : Type} (x : MetaM α) : CoreM α := do
  let stateful := ReaderT.run x ({} : Meta.Context)
  let (result, _) ← StateRefT'.run stateful ({} : Meta.State)
  return result

def ppInCore (e : Expr) : CoreM Format := runMeta (Meta.ppExpr e)

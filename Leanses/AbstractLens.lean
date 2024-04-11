import Lean
import Init.Meta
import Lean.Data.Options
import Leanses.Options
import Leanses.Lens

namespace Leanses.AbstractLens

export Leanses (Const Const.get Lens Lens' Traversal Traversal' lens lens'
                over set view LawfulLens comp)

syntax (name := mkAbstractLens) "mkabstractlenses" ident : command

open Lean.Elab Command in
@[command_elab mkAbstractLens] def mkAbstractLensHandler : CommandElab
  | `(mkabstractlenses $i:ident) => do elabCommand <| ← `(mklenses $i:ident)
  | _ => throwUnsupportedSyntax

end Leanses.AbstractLens

/-
Copyright (c) 2024 Yann Herklotz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Init.Meta
import Lean.Data.Options
import Leanses.Options
import Leanses.Lens

namespace Leanses.AbstractLens

export Leanses (Const Const.get Lens Lens' Traversal Traversal' lens lens'
                over set view fview LawfulLens comp fin_at)

syntax (name := mkAbstractLens) "mkabstractlenses" ident : command

open Lean.Elab Command in
@[command_elab mkAbstractLens] def mkAbstractLensHandler : CommandElab
  | `(mkabstractlenses $i:ident) => do elabCommand <| ← `(mklenses $i:ident)
  | _ => throwUnsupportedSyntax

end Leanses.AbstractLens

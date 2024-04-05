import Lean
import Init.Meta
import Lean.Data.Options
import Leanses.Options

namespace Leanses.Lens

structure Lens (s t a b: Type _) where
  set : b → s → t
  view : s → a

def set (x: Lens s t a b) := x.set
def view (x: Lens s t a b) := x.view

def compose (l1: Lens s t a b) (l2: Lens a b c d): Lens s t c d :=
  Lens.mk (fun bv sv => l1.set (l2.set bv (l1.view sv)) sv) (fun sv => l2.view (l1.view sv))

abbrev Lens' a b := Lens a a b b

syntax (priority := high) "<{ " term " with " (term " := " term),+ " }>" : term
syntax (priority := high) "<{ " term " ... }>" : term

macro_rules
  | `(<{$y with $x := $z}>) => `(set $x $z $y)
  | `(<{$y with $x := $z, $[$xs:term := $zs:term],*}>) => 
    `(set $x $z (<{ $y with $[$xs:term := $zs:term],* }>))

@[app_unexpander Leanses.Lens.Lens.set]
def unexpanderSet : Lean.PrettyPrinter.Unexpander
  | `($(_) $lens:term $item:term <{ $rest:term with $[$xs:term := $zs:term],* }>) =>
    `(<{ $rest:term with $lens:term := $item:term, $[$xs:term := $zs:term],* }>)
  | `($(_) $lens:term $item:term $rest:term) =>
    `(<{ $rest:term with $lens:term := $item:term }>)
  | _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.Leanses.Lens.Lens.set] def delabExpandSet : Delab := do
  let o ← getOptions
  if o.get pp.hideLensUpdates.name pp.hideLensUpdates.defValue then do
    let e ← getExpr
    guard $ e.getAppNumArgs == 7
    let y ← withAppArg $ withOptionAtCurrPos pp.zeroLensUpdates.name true delab
    let oc ← getOptionsAtCurrPos
    if oc.get pp.zeroLensUpdates.name pp.zeroLensUpdates.defValue then
      `($y)
    else
      `(<{ $y ... }>)
  else failure

-- set_option trace.Elab.match true in
set_option trace.debug true
-- set_option trace.Meta.synthInstance true
-- set_option trace.profiler true

open Lean Elab Command
open Parser Meta

syntax (name := mkLens) "mklenses" ident : command

open Lean.Elab.Term in
def toSyntax (e : Expr) : TermElabM Syntax.Term := withFreshMacroScope do
  let stx ← `(?a)
  let mvar ← elabTermEnsuringType stx (← Meta.inferType e)
  mvar.mvarId!.assign e
  pure stx

@[command_elab mkLens] def mkReprInstanceHandler : CommandElab
  | `(mklenses $i) => do
    if ← isInductive i.getId then
      if isStructure (← getEnv) i.getId then
        let indVal ← getConstInfoInduct i.getId
        let structureFieldsM := getStructureInfo? (← getEnv) indVal.name
        match structureFieldsM with
        | some structureFields =>
          for field in structureFields.fieldInfo do
            let fieldType ← liftTermElabM (liftMetaM (inferType (mkConst field.projFn)))
            let fieldTypeName ← match fieldType with
                     | Expr.forallE _ _ b _ => pure b
                     | _ => throwUnsupportedSyntax
            let structType ← match fieldType with
                     | Expr.forallE _ b _ _ => pure b
                     | _ => throwUnsupportedSyntax
            trace[debug] "{structType} {fieldTypeName}"
            let fieldTypeIdent := mkIdent (toString fieldTypeName)
            let fieldNameIdent := mkIdent field.fieldName
            let accessor ← `(fun a : $i => a.$fieldNameIdent)
            --let fieldAccess := `(Term.structInstField| $fieldNameIdent:structInstLVal := $r)
            --let fieldAccess := mkNode ``Term.structInstLVal #[mkAtom (toString field.fieldName)]
            trace[debug] "{fieldTypeIdent}"
            let x ← liftTermElabM $ toSyntax structType
            let setter ←
              `(fun b : $fieldTypeIdent =>
                (fun a : $i =>
                  { a with $fieldNameIdent:ident := b }))
            let lens ← `(def $(mkIdent field.fieldName) : Lens' $i $fieldTypeIdent := Lens.mk $setter $accessor)
            trace[debug] "{lens}"
            elabCommand <| lens
        | _ => throwUnsupportedSyntax
        -- for typeName in indVal.all do
        --   trace[debug] "{typeName}"
      else
        throwUnsupportedSyntax
    else throwError "not inductive 2"
  | _ => throwUnsupportedSyntax

structure SubEx where
  c : String
  deriving Repr

--def c : Lens' Leanses.Lens.SubEx String :=
--      Lens.mk (fun b : String => (fun a : Leanses.Lens.SubEx => { a with c := b }))
--        fun a : Leanses.Lens.SubEx => a.c
--
--def clens : Lens' SubEx String := Lens.mk (fun y => fun x => {x with c := y}) (fun x => x.c)

-- `mklenses` automatically generates lenses for a structure.
mklenses Leanses.Lens.SubEx

theorem subexcviewset : ∀ v s, view c (set c v s) = v := by
  simp [view, set, c]

theorem subexcsetset : ∀ v v' s, set c v' (set c v s) = set c v' s := by
  simp [view, set, c]

theorem subexcsetview : ∀ s, set c (view c s) s = s := by
  simp [view, set, c]

--structure Example where
--  s1 : String
--  s2 : Int
--  s3 : SubEx
--  deriving Repr
--
--mklenses Example
--
--def v := Example.mk "a" 1 {c := "c"}
--
---- Structure update syntax built into Lean
--#check { v with s2 := 5, s1 := "b" }
-----> let src := v;
-----> { s1 := "b", s2 := 5, s3 := src.s3 } : Example
--#check { v with s3.c := "deep", s1 := "c" }
-----> let src := v;
-----> { s1 := "c", s2 := src.s2,
----->   s3 :=
----->     let src := src.s3;
----->     { c := "deep" } } : Example
--
---- Structure updates using lenses
--#check <{ v with s2 := 5, s1 := "b" }>
-----> <{ v with s2 := 5, s1 := "b" }> : Example
--#check <{ v with s3 ∘ c := "deep", s1 := "c" }>
-----> <{ v with s3 ∘ c := "deep", s1 := "c" }> : Example
--
--set_option pp.hideLensUpdates true
--
--#check <{ v with s2 := 5, s1 := "b" }>
-----> <{ v ... }> : Example
--#check <{ v with s3 ∘ c := "deep", s1 := "c" }>
-----> <{ v ... }> : Example  

end Leanses.Lens

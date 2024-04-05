import Lean
import Init.Meta
import Lean.Data.Options
import Leanses.Options

namespace Leanses.AbstractLens

structure Const (α β: Type _) where
  get : α

instance ConstFunctor : Functor (Const α) where
  map _ a := Const.mk a.get

instance ConstApplicative [Inhabited α] [Append α] : Applicative (Const α) where
  pure _ := Const.mk default
  seq f a := Const.mk $ f.get ++ (a ()).get

abbrev Setter s t a b := (a → Id b) → s → Id t
abbrev Setter' a b := Setter a a b b

abbrev Getter r s a := (a → Const r a) → s → Const r s

abbrev Lens s t a b := ∀ {f}, [Functor f] → (a → f b) → s → f t
abbrev Lens' a b := Lens a a b b

abbrev Traversal s t a b := ∀ {f}, [Applicative f] → (a → f b) → s → f t
abbrev Traversal' a b := Lens a a b b

def lens (get: s → a) (set: s → b → t): Lens s t a b :=
  fun afb s => Functor.map (set s) (afb (get s))

def over (setter: Setter s t a b) (upd: a → b): s → t :=
  Id.run ∘ setter (pure ∘ upd)

def set (setter: Setter s t a b) (v: b): s → t :=
  Id.run ∘ setter (fun _ => pure v)

def view (getting: Getter a s a): s → a := Const.get ∘ getting Const.mk

--------------------------------------------------------------------------------

syntax (priority := high) "<{ " term " with " (term " := " term),+ " }>" : term
syntax (priority := high) "<{ " term " ... }>" : term

macro_rules
  | `(<{$y with $x := $z}>) => `(set $x $z $y)
  | `(<{$y with $x := $z, $[$xs:term := $zs:term],*}>) => 
    `(set $x $z (<{ $y with $[$xs:term := $zs:term],* }>))

@[app_unexpander Leanses.AbstractLens.set]
def unexpanderSet : Lean.PrettyPrinter.Unexpander
  | `($(_) $lens:term $item:term <{ $rest:term with $[$xs:term := $zs:term],* }>) =>
    `(<{ $rest:term with $lens:term := $item:term, $[$xs:term := $zs:term],* }>)
  | `($(_) $lens:term $item:term $rest:term) =>
    `(<{ $rest:term with $lens:term := $item:term }>)
  | _ => throw ()

--@[app_unexpander _root_.set] def unexpanderSetHide : Lean.PrettyPrinter.Unexpander
--  | `($(_) $_:term $_:term <{ $rest:term ... }>) => do
--    `(<{ $rest ... }>)
--  | `($(_) $_:term $_:term $rest:term) =>
--    `(<{ $rest ... }>)
--  | _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.Leanses.AbstractLens.set] def delabExpandSet : Delab := do
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

macro "solvelens" : tactic => `(tactic| simp [view, set, Functor.map, lens, Id.run, Const.get])

syntax (name := mkAbstractLens) "mkabstractlenses" ident : command

@[command_elab mkAbstractLens] def mkAbstractLensHandler : CommandElab
  | `(mkabstractlenses $i) => do
    let name ← resolveGlobalConstNoOverload i
    let Name.str _ name' := name.eraseMacroScopes
      | throwErrorAt i "not name"
    let env ← getEnv
    let some info := getStructureInfo? env name
      | throwErrorAt i "Not a structure"
    logInfo m!"field names: {info.fieldNames}"
    for field in info.fieldInfo do
      let proj := (env.find? field.projFn).get!
      let fieldNameIdent := mkIdent field.fieldName
      let freshName ← liftCoreM <| mkFreshUserName <| Name.mkSimple <| toString name' ++ "_" ++ toString fieldNameIdent
      trace[debug] "{field.projFn}: {proj.type}"
      match proj.type with
      | Expr.forallE _ (Expr.const structType _) (Expr.const projType _) _ => 
        trace[debug] "types: {structType} {projType}"
        let accessor ← `(fun a : $(mkIdent structType) => a.$fieldNameIdent)
        trace[debug] "{fieldNameIdent}"
        let setter ←
          `(fun a : $(mkIdent structType) =>
            (fun b : $(mkIdent projType) =>
              { a with $fieldNameIdent:ident := b }))
        elabCommand <| ← `(def $fieldNameIdent : Lens' $(mkIdent structType) $(mkIdent projType) := lens $accessor $setter)
        elabCommand <| ← `(@[simp] theorem $(mkIdent $ freshName ++ "_view_set") : 
                              ∀ v s, view $fieldNameIdent:ident (set $fieldNameIdent:ident v s) = v := by 
                                simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
        elabCommand <| ← `(@[simp] theorem $(mkIdent $ freshName ++ "_set_set") :
                              ∀ v v' s, set $fieldNameIdent:ident v' (set $fieldNameIdent:ident v s) = set $fieldNameIdent:ident v' s := by 
                                simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
        elabCommand <| ← `(@[simp] theorem $(mkIdent $ freshName ++ "_set_view") :
                              ∀ s, set $fieldNameIdent:ident (view $fieldNameIdent:ident s) s = s := by 
                                simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
        elabCommand <| ← `(@[simp] theorem $(mkIdent $ freshName ++ "_view_set_comp") : 
                              ∀ x y v s (f: Lens' _ x) (g: Lens' _ y), view ($fieldNameIdent:ident ∘ f) (set ($fieldNameIdent:ident ∘ g) v s) = (view f (set g v (view $fieldNameIdent:ident s))) := by 
                                simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
        elabCommand <| ← `(@[simp] theorem $(mkIdent $ freshName ++ "_view_set_comp2") : 
                              ∀ y v s (g: Lens' _ y), view ($fieldNameIdent:ident) (set ($fieldNameIdent:ident ∘ g) v s) = (set g v (view $fieldNameIdent:ident s)) := by 
                                simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
      | _ => throwErrorAt i "Could not destruct types correctly"
    for field in info.fieldInfo do
      let fieldNameIdent := mkIdent field.fieldName
      let freshName ← liftCoreM <| mkFreshUserName <| Name.mkSimple <| toString name' ++ "_" ++ toString fieldNameIdent
      for field' in info.fieldInfo do
        if field.fieldName == field'.fieldName then
          pure ()
        else do
          let fieldName' := mkIdent field'.fieldName
          let freshName' s := (mkIdent $ freshName ++ "_" ++ field'.fieldName ++ s)
          elabCommand <| ← `(@[simp] theorem $(freshName' "_set_view"):ident :
                                ∀ v s, view $fieldNameIdent:ident (set $(fieldName'):ident v s) = view $fieldNameIdent:ident s := by 
                                  simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident, $(fieldName'):ident])
          elabCommand <| ← `(@[simp] theorem $(freshName' "_set_view_comp"):ident :
                                ∀ x v s (f: Lens' _ x), view $fieldNameIdent:ident (set ($(fieldName'):ident ∘ f) v s) = view $fieldNameIdent:ident s := by 
                                  simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident, $(fieldName'):ident])
      trace[debug] "{freshName}"
  | _ => throwUnsupportedSyntax

structure SubEx where
  c : String
  deriving Repr

-- `mklenses` automatically generates lenses for a structure.
mkabstractlenses Leanses.AbstractLens.SubEx

structure Example where
  s1 : String
  s2 : Int
  s3 : SubEx
  deriving Repr

mkabstractlenses Leanses.AbstractLens.Example

example :
  ∀ v s, view s3 (set (s3 ∘ c) v s) = set c v (view s3 s) := by 
    simp [view, set, Functor.map, lens, Id.run, Const.get, s2, s1, s3]

def v := Example.mk "a" 1 {c := "c"}

-- Structure update syntax built into Lean
#check { v with s2 := 5, s1 := "b" }

example : view (s3 ∘ c) <{ v with s3 ∘ c := "deep", s2 := 5, s1 := "b", s3 ∘ c := "deep" }> = "deep" := by
  simp

example : view c (view (s3) <{ v with s3 ∘ c := "deep", s2 := 5, s1 := "b", s3 ∘ c := "deep" }>) = "deep" := by
  simp

---> let src := v;
---> { s1 := "b", s2 := 5, s3 := src.s3 } : Example
#check { v with s3.c := "deep", s1 := "c" }
---> let src := v;
---> { s1 := "c", s2 := src.s2,
--->   s3 :=
--->     let src := src.s3;
--->     { c := "deep" } } : Example

-- Structure updates using lenses
#check <{ v with s2 := 5, s1 := "b" }>
---> <{ v with s2 := 5, s1 := "b" }> : Example
#check <{ v with s3 ∘ c := "deep", s1 := "c" }>
---> <{ v with s3 ∘ c := "deep", s1 := "c" }> : Example

set_option pp.hideLensUpdates true

#check <{ v with s2 := 5, s1 := "b" }>
---> <{ v ... }> : Example
#check <{ v with s3 ∘ c := "deep", s1 := "c" }>
---> <{ v ... }> : Example

end Leanses.AbstractLens

import Lean
import Init.Meta
import Lean.Data.Options
import Leanses.Options

namespace Leanses.Lens

structure Const (α β: Type _) where
  get : α

instance ConstFunctor : Functor (Const α) where
  map _ a := Const.mk a.get

instance ConstApplicative [Inhabited α] [Append α] : Applicative (Const α) where
  pure _ := Const.mk default
  seq f a := Const.mk $ f.get ++ (a ()).get

abbrev ASetter s t a b := (a → Id b) → s → Id t
abbrev ASetter' a b := ASetter a a b b

abbrev Getting r s a := (a → Const r a) → s → Const r s

--abbrev Lens s t a b {f} [Functor f] := (a → f b) → s → f t
--abbrev Lens' a b := Lens a a b b

abbrev Lens s t a b := ∀ f, [Functor f] → (a → f b) → s → f t
abbrev Lens' a b := Lens a a b b

abbrev Traversal s t a b := ∀ f, [Applicative f] → (a → f b) → s → f t
abbrev Traversal' a b := Lens a a b b

-- section
--   variable {f : Type _ → Type _}
--   variable [F : Functor f]
-- 
--   abbrev Lens s t a b := (a → f b) → s → f t
--   abbrev Lens' a b := @Lens f a a b b
-- end

--instance LensPLensCoe : Coe (Lens' a b) (Lens a a b b) where
--  coe a := a

def lens (get: s → a) (set: s → b → t): Lens s t a b :=
  fun _ _ afb s => Functor.map (set s) (afb (get s))

-- def composeCoe ()

def over (setter: ASetter s t a b) (upd: a → b): s → t :=
  Id.run ∘ setter (pure ∘ upd)

def set (setter: ASetter s t a b) (v: b): s → t :=
  Id.run ∘ setter (fun _ => pure v)

def view (getting: Getting a s a): s → a := Const.get ∘ getting Const.mk

instance LensPGettingInst : Coe (Lens' a b) (Getting r a b) where
  coe a := a _

instance LensSetterInst : Coe (Lens s t a b) (ASetter s t a b) where
  coe a := a _

--------------------------------------------------------------------------------

--def getPPHideLenseUpdates (o : Options) : Bool := o.get pp.hideLenseUpdates

syntax (priority := high) "<{ " term " with " (term " := " term),+ " }>" : term
syntax (priority := high) "<{ " term " ... }>" : term

macro_rules
  | `(<{$y with $x := $z}>) => `(set $x $z $y)
  | `(<{$y with $x := $z, $[$xs:term := $zs:term],*}>) => 
    `(set $x $z (<{ $y with $[$xs:term := $zs:term],* }>))

@[app_unexpander Leanses.Lens.set]
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
@[delab app.Leanses.Lens.set] def delabExpandSet : Delab := do
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
-- set_option trace.debug true
-- set_option trace.Meta.synthInstance true
-- set_option trace.profiler true

open Lean Elab Command
open Parser Meta

syntax (name := mkLens) "mklenses" ident : command

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
            let accessor ← `(fun a:$(mkIdent (toString structType)) => a.$fieldNameIdent)
--            let fieldAccess := `(Term.structInstField| $fieldNameIdent:structInstLVal := $r)
            --let fieldAccess := mkNode ``Term.structInstLVal #[mkAtom (toString field.fieldName)]
            trace[debug] "{fieldTypeIdent}"
            let setter ← 
              `(fun a:$(mkIdent (toString structType)) => 
                (fun b:$fieldTypeIdent => 
                  { a with $fieldNameIdent:ident := b }))
            let lens ← `(def $(mkIdent field.fieldName) {f} [Functor f] := lens $accessor $setter f)
            elabCommand <| lens
        | _ => throwUnsupportedSyntax
        -- for typeName in indVal.all do
        --   trace[debug] "{typeName}"
      else
        throwUnsupportedSyntax
    else throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

end Leanses.Lens

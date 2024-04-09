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

def lens' (get: s → a) (set: s → a → s): Lens' s a :=
  lens get set

def over (setter: Setter s t a b) (upd: a → b): s → t :=
  Id.run ∘ setter (pure ∘ upd)

def set (setter: Setter s t a b) (v: b): s → t :=
  Id.run ∘ setter (fun _ => pure v)

def view (getting: Getter a s a): s → a := Const.get ∘ getting Const.mk

def setL (setter: Lens s t a b) (v: b): s → t :=
  Id.run ∘ setter (fun _ => pure v)

def viewL (getting: Lens' s a): s → a := Const.get ∘ getting Const.mk

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
-- set_option trace.debug true
-- set_option trace.Meta.synthInstance true
-- set_option trace.profiler true

open Lean Elab Command
open Parser Meta

open Lean Meta PrettyPrinter Delaborator SubExpr in
--#eval do
--  ← delab <| (Lean.Expr.forallE
--      `self
--      (Lean.Expr.app (Lean.Expr.const `Leanses.AbstractLens.SubEx []) (Lean.Expr.bvar 0))
--      (Lean.Expr.forallE
--        `self
--        (Lean.Expr.app (Lean.Expr.const `Fin []) (Lean.Expr.bvar 1))
--        (Lean.Expr.const `String [])
--        (Lean.BinderInfo.default))
--      (Lean.BinderInfo.default))

structure TypeWithBinders where
  typeName : Name
  binders : Array (Name × Expr)
  deriving Inhabited, Repr

--def replaceBvars (binders : Array (Name × Expr)) (typeE : Expr) : Expr :=
--

def generateNamesAndBinders (x : Expr) (index : Int) (arr : Array (Name × Expr)) : CoreM (Array (Name × Expr)) := do
  match x with
  | Expr.forallE _ t r _ => do
    let typeName ← mkFreshUserName "t"
    generateNamesAndBinders r (index + 1) <| arr.push (typeName, t)
  | Expr.sort _ => pure arr
  | l => throwError "Unexpected construct in structure type: {repr l}"

def generateFreshNamesAux (x : Expr) (arr : Array (TSyntax `ident)) : CoreM (Array (TSyntax `ident)) := do
  match x with
  | Expr.forallE _ _ r _ => do
    let typeName := mkIdent <| ← mkFreshUserName "t"
    generateFreshNamesAux r <| arr.push typeName
  | Expr.sort _ => pure arr
  | l => throwError "Unexpected construct in structure type: {repr l}"

def generateFreshNames (x : Expr) : CoreM (Array (TSyntax `ident)) := generateFreshNamesAux x default

syntax (name := mkAbstractLens) "mkabstractlenses" ident : command

open Lean Meta PrettyPrinter Delaborator SubExpr Core in
@[command_elab mkAbstractLens] def mkAbstractLensHandler : CommandElab
  | `(mkabstractlenses $i) => do
    let name ← resolveGlobalConstNoOverload i
    let structureType ← liftTermElabM <| liftMetaM <| inferType (Expr.const name [])
    --let structureBinders ← liftCoreM <| generateNamesAndBinders structureType default
    --let structureBinders ← liftCoreM <| ViewRaw.viewBinders 0 structureType
    --trace[debug] "{structureBinders}"
    let names : TSyntaxArray `ident ← liftCoreM <| generateFreshNames structureType
    let numArgs := structureType.getForallBinderNames.length
    trace[debug] "{numArgs}"
    let Name.str _ name' := name.eraseMacroScopes
      | throwErrorAt i "not name"
    let env ← getEnv
    let some info := getStructureInfo? env name
      | throwErrorAt i "Not a structure"
    logInfo m!"field names: {info.fieldNames}"
    trace[debug] "{structureType}"
    for field in info.fieldInfo do
      trace[debug] "{repr field}"
      let proj := (env.find? field.projFn).get!
      let some other ← getProjectionFnInfo? field.projFn
        | throwErrorAt i "not raiestn"
      let fieldNameIdent := mkIdent $ name' ++ "l" ++ field.fieldName
      let fieldNameIdent' := mkIdent field.fieldName
      let freshName r := mkIdent <| name' ++ "l" ++ (Name.mkSimple (toString field.fieldName ++ r))
      --let stx ← liftTermElabM <| liftMetaM <| delab <| proj.type.getForallBodyMaxDepth (numArgs + 1)
      --trace[debug] "{field.projFn}: {repr (proj.type.getForallBodyMaxDepth (numArgs + 1))}:::{stx}"
      let accessor ← `(fun a => @$(mkIdent field.projFn) $names:ident* a)
      let setter ←
        `(fun a => (fun b => { a with $fieldNameIdent':ident := b }))
      let appliedLens ← `((@$fieldNameIdent $names:ident* _ _))
      let defn ← `(def $fieldNameIdent $names:ident* := @lens' _ _ $accessor $setter)
      trace[debug] "{defn}"
      let view_set_lemma ←
        `(@[simp] theorem $(freshName "_view_set") $names:ident* :
            ∀ v s,
              @view _ _
                $appliedLens (@set _ _ _ _ $appliedLens v s) = v := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      trace[debug] "{view_set_lemma}"
      let set_set_lemma ←
        `(@[simp] theorem $(freshName "_set_set") $names:ident* :
            ∀ v v' s, @set _ _ _ _ $appliedLens v' (@set _ _ _ _ $appliedLens v s)
                      = @set _ _ _ _ $appliedLens v' s := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      let set_view_lemma ←
        `(@[simp] theorem $(freshName "_set_view") $names:ident* :
            ∀ s, @set _ _ _ _ $appliedLens (@view _ _ $appliedLens s) s
                 = s := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      let view_set_comp_lemma ←
        `(@[simp] theorem $(freshName "_view_set_comp") $names:ident* :
            ∀ x y v s (f: Lens' _ x) (g: Lens' _ y),
              @view x _ ($appliedLens ∘ f)
                (@set _ _ _ _ ($appliedLens ∘ g) v s)
              = @view x _ f (@set _ _ y y g v (@view _ _ $appliedLens s)) := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      let view_set_comp2_lemma ←
        `(@[simp] theorem $(freshName "_view_set_comp2") $names:ident* :
            ∀ y v s (g: Lens' _ y),
              @view _ _ $appliedLens (@set _ _ _ _ ($appliedLens ∘ g) v s)
              = @set _ _ y y g v (@view _ _ $appliedLens s) := by
              simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      trace[debug] "{view_set_comp_lemma}"
      elabCommand <| defn
      elabCommand <| view_set_lemma
      elabCommand <| set_set_lemma
      elabCommand <| set_view_lemma
      elabCommand <| view_set_comp_lemma
      elabCommand <| view_set_comp2_lemma
    for main_field in info.fieldInfo do
      let main_proj := (env.find? main_field.projFn).get!
      let main_ident := mkIdent $ name' ++ "l" ++ main_field.fieldName
      let main_lens ← `((@$main_ident $names:ident* _ _))
      --let main_type ← liftTermElabM <| liftMetaM <| delab <| main_proj.type.getForallBodyMaxDepth (numArgs + 1)
      let freshName r y := mkIdent <| name' ++ "l" ++ (Name.mkSimple (toString main_field.fieldName ++ r ++ y))
      for other_field in info.fieldInfo do
        if main_field.fieldName == other_field.fieldName then
          pure ()
        else do
          let other_proj := (env.find? other_field.projFn).get!
          let other_ident := mkIdent $ name' ++ "l" ++ other_field.fieldName
          let other_lens ← `((@$other_ident $names:ident* _ _))
          let other_type ← liftTermElabM <| liftMetaM <| delab <| other_proj.type.getForallBodyMaxDepth (numArgs + 1)
          let freshName' := freshName ("_" ++ toString other_field.fieldName)
          let contr_set_view_lemma ←
            `(@[simp] theorem $(freshName' "_set_view"):ident $names:ident* :
                ∀ v s,
                  @view _ _ $main_lens
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ $main_lens s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $main_ident:ident, $other_ident:ident])
          let contr_set_view_comp_lemma ←
            `(@[simp] theorem $(freshName' "_set_view_comp"):ident $names:ident* :
                ∀ x v s (f: Lens' _ x),
                  @view _ _ $main_lens
                    (@set _ _ _ _ ($other_lens ∘ f) v s)
                  = @view _ _ $main_lens s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $main_ident:ident, $other_ident:ident])
          let contr_set_view_comp_lemma2 ←
            `(@[simp] theorem $(freshName' "_set_view_comp2"):ident $names:ident* :
                ∀ x y v s (g: Lens' _ y) (f: Lens' _ x),
                  @view _ _ ($main_lens ∘ g)
                    (@set _ _ _ _ ($other_lens ∘ f) v s)
                  = @view _ _ ($main_lens ∘ g) s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $main_ident:ident, $other_ident:ident])
          let contr_set_view_comp_lemma3 ←
            `(@[simp] theorem $(freshName' "_set_view_comp3"):ident $names:ident* :
                ∀ y v s (g: Lens' _ y),
                  @view _ _ ($main_lens ∘ g)
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ ($main_lens ∘ g) s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $main_ident:ident, $other_ident:ident])
          trace[debug] "{contr_set_view_comp_lemma3}"
          elabCommand <| contr_set_view_lemma
          elabCommand <| contr_set_view_comp_lemma
          elabCommand <| contr_set_view_comp_lemma2
          elabCommand <| contr_set_view_comp_lemma3
  | _ => throwUnsupportedSyntax

--structure SubEx1 where
--  c : Fin y → Fin n → String
--  c2 : Fin y → Fin n → String
--
--mkabstractlenses SubEx1
--
--structure SubEx {n : Nat} {f : Fin n} {g : Fin n} where
--  c : String
--  c3 : Fin y → Fin n → String
--  c2 : Fin y → Fin n → String
--
--#check SubEx
--
---- `mklenses` automatically generates lenses for a structure.
--mkabstractlenses SubEx
--
--structure Example (a) (b) (c) where
--  s1 : String
--  s2 : Int
--  s3 : @SubEx a b c
--
--mkabstractlenses Leanses.AbstractLens.Example
--
--open SubEx.l in
--open Example.l in
--example :
--  ∀ a b d v (s : Example a b d), view (s3 _ _ _) (set ((s3 _ _ _) ∘ (c _ _ _)) v s) = set (c _ _ _) v (view (s3 _ _ _) s) := by
--    simp
--
--open SubEx.l in
--open Example.l in
--example : ∀ a b d x (v : Example a b d), view (s2 _ _ _) <{ v with (s3  _ _ _) ∘ (c _ _ _) := "deep", (s2  _ _ _) := 5, (s1 _ _ _) := "b", (s3 _ _ _) ∘ (c _ _ _) := "deep" }> = x := by
--  simp
--
--example : view c (view (s3) <{ v with s3 ∘ c := "deep", s2 := 5, s1 := "b", s3 ∘ c := "deep" }>) = "deep" := by
--  simp
--
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

end Leanses.AbstractLens

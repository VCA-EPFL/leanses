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
set_option trace.debug true
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

syntax (name := mkAbstractLens) "mkabstractlenses" ident : command

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[command_elab mkAbstractLens] def mkAbstractLensHandler : CommandElab
  | `(mkabstractlenses $i) => do
    let name ← resolveGlobalConstNoOverload i
    let structureType ← liftTermElabM <| liftMetaM <| inferType (Expr.const name [])
    let numArgs := structureType.getForallBinderNames.length
    trace[debug] "{numArgs}"
    let Name.str _ name' := name.eraseMacroScopes
      | throwErrorAt i "not name"
    let env ← getEnv
    let some info := getStructureInfo? env name
      | throwErrorAt i "Not a structure"
    logInfo m!"field names: {info.fieldNames}"
    for field in info.fieldInfo do
      trace[debug] "{repr field}"
      let proj := (env.find? field.projFn).get!
      let some other ← getProjectionFnInfo? field.projFn
        | throwErrorAt i "not raiestn"
      let fieldNameIdent := mkIdent $ name' ++ "l" ++ field.fieldName
      let fieldNameIdent' := mkIdent field.fieldName
      let freshName ← liftCoreM <| mkFreshUserName <| Name.mkSimple <| toString name' ++ "_" ++ toString fieldNameIdent
      let stx ← liftTermElabM <| liftMetaM <| delab <| proj.type.getForallBodyMaxDepth (numArgs + 1)
      trace[debug] "{field.projFn}: {repr (proj.type.getForallBodyMaxDepth (numArgs + 1))}:::{stx}"
      let accessor ← `(fun a : $i:ident => ( a.$fieldNameIdent' : ($stx:term)))
      let setter ←
        `(fun a : $i:ident =>
          (fun b : ($stx:term) =>
            { a with $fieldNameIdent':ident := b }))
      let defn ← `(def $fieldNameIdent : Lens' $i:ident ($stx:term) := lens $accessor $setter)
      let view_set_lemma ←
        `(@[simp] theorem $(mkIdent $ freshName ++ "_view_set") :
            ∀ (v : ($stx:term)) (s: $i:ident), @Eq ($stx:term)
              (@view ($stx:term) ($i:ident)
                $fieldNameIdent:ident (set $fieldNameIdent:ident v s)) v := by
            simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
      let set_set_lemma ←
        `(@[simp] theorem $(mkIdent $ freshName ++ "_set_set") :
            ∀ v v' s, set $fieldNameIdent:ident v' (set $fieldNameIdent:ident v s)
                      = set $fieldNameIdent:ident v' s := by
            simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
      let set_view_lemma ←
        `(@[simp] theorem $(mkIdent $ freshName ++ "_set_view") :
            ∀ s, set $fieldNameIdent:ident (@view ($stx:term) ($i:ident)
                     $fieldNameIdent:ident s) s
                 = s := by
            simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
      let view_set_comp_lemma ←
        `(@[simp] theorem $(mkIdent $ freshName ++ "_view_set_comp") :
            ∀ x y v s (f: Lens' ($stx:term) x) (g: Lens' ($stx:term) y),
              @Eq x (@view x ($i:ident) ($fieldNameIdent:ident ∘ f)
                (set ($fieldNameIdent:ident ∘ g) v s))
              (@view x ($stx:term) f (@set ($stx:term) ($stx:term) y y g v (@view ($stx:term) ($i:ident)
                   $fieldNameIdent:ident s))) := by
            simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
      let view_set_comp2_lemma ←
        `(@[simp] theorem $(mkIdent $ freshName ++ "_view_set_comp2") :
            ∀ y v s (g: Lens' _ y),
              @Eq ($stx:term) (@view ($stx:term) ($i:ident) ($fieldNameIdent:ident)
                (set ($fieldNameIdent:ident ∘ g) v s))
              (@set ($stx:term) ($stx:term) y y g v
                (@view ($stx:term) ($i:ident) $fieldNameIdent:ident s)) := by
              simp [view, set, Functor.map, lens, Id.run, Const.get, $fieldNameIdent:ident])
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
      let main_type ← liftTermElabM <| liftMetaM <| delab <| main_proj.type.getForallBodyMaxDepth (numArgs + 1)
      let freshName ← liftCoreM <| mkFreshUserName <| Name.mkSimple <| toString name' ++ "_" ++ toString main_ident
      for other_field in info.fieldInfo do
        if main_field.fieldName == other_field.fieldName then
          pure ()
        else do
          let other_proj := (env.find? other_field.projFn).get!
          let other_ident := mkIdent $ name' ++ "l" ++ other_field.fieldName
          let other_type ← liftTermElabM <| liftMetaM <| delab <| other_proj.type.getForallBodyMaxDepth (numArgs + 1)
          let freshName' s := (mkIdent $ freshName ++ "_" ++ other_field.fieldName ++ s)
          let contr_set_view_lemma ←
            `(@[simp] theorem $(freshName' "_set_view"):ident :
                ∀ v s,
                  @Eq ($main_type) (@view ($main_type) ($i:ident) $main_ident:ident
                    (set $(other_ident):ident v s))
                  (@view ($main_type) ($i:ident) $main_ident:ident s) := by
                  simp [view, set, Functor.map, lens, Id.run, Const.get, $main_ident:ident, $(other_ident):ident])
          let contr_set_view_comp_lemma ←
            `(@[simp] theorem $(freshName' "_set_view_comp"):ident :
                ∀ x v s (f: Lens' ($other_type) x),
                  @Eq ($main_type) (@view ($main_type) ($i:ident) $main_ident:ident
                    (set ($(other_ident):ident ∘ f) v s))
                  (@view ($main_type) ($i:ident) $main_ident:ident s) := by
                  simp [view, set, Functor.map, lens, Id.run, Const.get, $main_ident:ident, $(other_ident):ident])
          elabCommand <| contr_set_view_lemma
          elabCommand <| contr_set_view_comp_lemma
      trace[debug] "{freshName}"
  | _ => throwUnsupportedSyntax

--instance EqFinString : Eq ({n : Nat} → Fin n → String) where
--  eq

structure SubEx (n : Nat) where
  c : String
  c2 : Fin y → String

--def SubEx.l.c2 : Lens' SubEx ({n : Nat} → Fin n → String) :=
--      lens (fun (a : SubEx) => (a.c : {n:Nat} → Fin n → String)) (fun (a : SubEx) =>
--        (fun (b : ({n : Nat} → Fin n → String)) => { a with c := b }))

--#check (SubEx.c : {n : Nat} → SubEx n → (Fin n → String))

-- `mklenses` automatically generates lenses for a structure.
mkabstractlenses Leanses.AbstractLens.SubEx

theorem SubEx_SubEx.l.c._view_set_comp :
        ∀ x y v s (f : Lens' ({n : Nat} → Fin n → String) x) (g : Lens' ({n : Nat} → Fin n → String) y),
          @Eq x (@view x (Leanses.AbstractLens.SubEx) (SubEx.l.c ∘ f) (set (SubEx.l.c ∘ g) v s))
            (@view x ({n : Nat} → Fin n → String) f
              (@set ({n : Nat} → Fin n → String) ({n : Nat} → Fin n → String) y y g v (@view ({n : Nat} → Fin n → String) (Leanses.AbstractLens.SubEx) SubEx.l.c s))) :=
      by simp [view, set, Functor.map, lens, Id.run, Const.get, SubEx.l.c]

#check (SubEx.l.c : Lens' SubEx ({n: Nat} → Fin n → String))

@[simp]
    theorem SubEx_SubEx.l.c._view_set :
        ∀ (v : ({n: Nat} → Fin n → String)) (s: SubEx),
          @Eq (∀ {n : Nat}, Fin n → String)
            (@view ({n: Nat} → Fin n → String) SubEx SubEx.l.c (set SubEx.l.c v s)) v := by
      simp [view, set, Functor.map, lens, Id.run, Const.get, SubEx.l.c]

#check SubEx.l.c

structure Example where
  s1 : String
  s2 : Int
  s3 : (SubEx n)
  deriving Repr

mkabstractlenses Leanses.AbstractLens.Example

open SubEx.l in
open Example.l in
example :
  ∀ v s, view s3 (set (s3 ∘ c) v s) = set c v (view s3 s) := by
    simp [view, set, Functor.map, lens, Id.run, Const.get, s2, s1, s3]

def v := Example.mk "a" 1 {c := "c"}

-- Structure update syntax built into Lean
#check { v with s2 := 5, s1 := "b" }

open SubEx.l in
open Example.l in
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

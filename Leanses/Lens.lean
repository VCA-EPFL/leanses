import Lean
import Init.Meta
import Lean.Data.Options
import Leanses.Options
import Aesop

namespace Leanses

declare_aesop_rule_sets [lens]

structure Const (α β: Type _) where
  get : α

instance : Functor (Const α) where
  map _ a := Const.mk a.get

instance : LawfulFunctor (Const α) where
  id_map := by
    intros; unfold id Functor.map instFunctorConst; simp
  comp_map := by
    intros; unfold Functor.map instFunctorConst; simp
  map_const := by
    unfold Functor.mapConst Functor.map instFunctorConst
    simp

instance [Inhabited α] [Append α] : Applicative (Const α) where
  pure _ := Const.mk default
  seq f a := Const.mk $ f.get ++ (a ()).get

def Lens s t a b := ∀ f [Functor f], (a → f b) → s → f t
abbrev Lens' a b := Lens a a b b

def Traversal s t a b := ∀ f [Applicative f], (a → f b) → s → f t
abbrev Traversal' a b := Lens a a b b

def lens (get: s → a) (set: s → b → t): Lens s t a b :=
  fun F [Functor F] afb s => Functor.map (set s) (afb (get s))

def lens' (get: s → a) (set: s → a → s): Lens' s a :=
  lens get set

def over (setter: Lens s t a b) (upd: a → b): s → t :=
  Id.run ∘ setter Id (pure ∘ upd)

def set (setter: Lens s t a b) (v: b): s → t :=
  Id.run ∘ setter Id (fun _ => pure v)

def view (getting: Lens' s a): s → a := Const.get ∘ getting (Const a) Const.mk

def fview {s a} := flip (@view s a)

class LawfulLens (l : Lens' s a) : Prop where
  view_set : ∀ s v, view l (set l v s) = v
  set_view : ∀ s, set l (view l s) s = s
  set_set : ∀ s v v', set l v' (set l v s) = set l v' s

def comp (f : Lens s t a b) (g : Lens a b x y): Lens s t x y :=
  fun F [Functor F] => f F ∘ g F

infixr:90 "⊚" => comp
infixr:90 "∘∘" => comp

infix:60 "^." => fview

--------------------------------------------------------------------------------

syntax (priority := high) "<{ " term " with " (term " := " term),+ " }>" : term
syntax (priority := high) "<{ " term " ... }>" : term

macro_rules
  | `(<{$y with $x := $z}>) => `(set $x $z $y)
  | `(<{$y with $x := $z, $[$xs:term := $zs:term],*}>) =>
    `(set $x $z (<{ $y with $[$xs:term := $zs:term],* }>))

@[app_unexpander Leanses.set]
def unexpanderSet : Lean.PrettyPrinter.Unexpander
  | `($(_) $lens:term $item:term <{ $rest:term with $[$xs:term := $zs:term],* }>) =>
    `(<{ $rest:term with $lens:term := $item:term, $[$xs:term := $zs:term],* }>)
  | `($(_) $lens:term $item:term $rest:term) =>
    `(<{ $rest:term with $lens:term := $item:term }>)
  | _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.Leanses.set] def delabExpandSet : Delab := do
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

open Lean Elab Command
open Parser Meta

open Lean Meta PrettyPrinter Delaborator SubExpr in

def generateFreshNamesAux (x : Expr) (arr : Array (TSyntax `ident)) : CoreM (Array (TSyntax `ident)) := do
  match x with
  | Expr.forallE _ _ r _ => do
    let typeName := mkIdent <| ← mkFreshUserName "t"
    generateFreshNamesAux r <| arr.push typeName
  | Expr.sort _ => pure arr
  | l => throwError "Unexpected construct in structure type: {repr l}"

def generateFreshNames (x : Expr) : CoreM (Array (TSyntax `ident)) := generateFreshNamesAux x default

syntax (name := mkLens) "mklenses" ident : command

open Lean Meta PrettyPrinter Delaborator SubExpr Core in
@[command_elab mkLens] def mkLensHandler : CommandElab
  | `(mklenses $i) => do
    let name ← resolveGlobalConstNoOverload i
    let structureType ← liftTermElabM <| liftMetaM <| inferType (Expr.const name [])
    let names : TSyntaxArray `ident ← liftCoreM <| generateFreshNames structureType
    let numArgs := structureType.getForallBinderNames.length
    trace[debug] "{numArgs}"
    let Name.str _ name' := name.eraseMacroScopes
      | throwErrorAt i "not name"
    let env ← getEnv
    let some info := getStructureInfo? env name
      | throwErrorAt i "Not a structure"
    trace[debug] "{structureType}"
    for field in info.fieldInfo do
      trace[debug] "{repr field}"
      let fieldNameIdent := mkIdent $ name' ++ "l" ++ field.fieldName
      let fieldNameIdent' := mkIdent field.fieldName
      let freshName r := mkIdent <| name' ++ "l" ++ (Name.mkSimple (toString field.fieldName ++ r))
      let accessor ← `(fun a => @$(mkIdent field.projFn) $names:ident* a)
      let setter ←
        `(fun a => (fun b => { a with $fieldNameIdent':ident := b }))
      let appliedLens ← `((@$fieldNameIdent $names:ident*))
      let defn ← `(def $fieldNameIdent $names:ident* := @lens' _ _ $accessor $setter)
      trace[debug] "{defn}"
      let view_set_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_view_set") $names:ident* :
            ∀ s v,
              @view _ _
                $appliedLens (@set _ _ _ _ $appliedLens v s) = v := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      trace[debug] "{view_set_lemma}"
      let set_set_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_set_set") $names:ident* :
            ∀ s v v', @set _ _ _ _ $appliedLens v' (@set _ _ _ _ $appliedLens v s)
                      = @set _ _ _ _ $appliedLens v' s := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      let set_view_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_set_view") $names:ident* :
            ∀ s, @set _ _ _ _ $appliedLens (@view _ _ $appliedLens s) s = s := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      let lawful_lens_instance ←
        `(instance ($names:ident*) : LawfulLens ($fieldNameIdent $names:ident*) where
            view_set := $(freshName "_view_set") $names:ident*
            set_set := $(freshName "_set_set") $names:ident*
            set_view := $(freshName "_set_view") $names:ident*)
      let comp_view_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_comp_view") $names:ident* :
            ∀ α s (g : Lens' _ α), @view _ _ ($appliedLens ⊚ g) s = @view _ _ g (@view _ _ $appliedLens s) := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, comp, $fieldNameIdent:ident])
      let comp_set_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_comp_set") $names:ident* :
            ∀ α v s (g : Lens' _ α),
              @set _ _ _ _ ($appliedLens ⊚ g) v s
              = @set _ _ _ _ $appliedLens (@set _ _ _ _ g v (@view _ _ $appliedLens s)) s := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, comp, $fieldNameIdent:ident])
      let view_set_comp_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_view_set_comp") $names:ident* :
            ∀ x y v s (f: Lens' _ x) (g: Lens' _ y),
              @view _ _ ($appliedLens ⊚ f)
                (@set _ _ _ _ ($appliedLens ⊚ g) v s)
              = @view _ _ f (@set _ _ y y g v (@view _ _ $appliedLens s)) := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, comp, $fieldNameIdent:ident])
      let view_set_comp2_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_view_set_comp2") $names:ident* :
            ∀ y v s (g: Lens' _ y),
              @view _ _ $appliedLens (@set _ _ _ _ ($appliedLens ⊚ g) v s)
              = @set _ _ y y g v (@view _ _ $appliedLens s) := by
              simp [view, set, Functor.map, lens', lens, Id.run, Const.get, comp, $fieldNameIdent:ident])
      let view_set_comp3_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_view_set_comp3") $names:ident* :
            ∀ y v s (g: Lens' _ y),
              @view _ _ ($appliedLens ⊚ g) (@set _ _ _ _ $appliedLens v s)
              = @view _ _ g v := by
              simp [view, set, Functor.map, lens', lens, Id.run, Const.get, comp, $fieldNameIdent:ident])
      trace[debug] "{defn}"
      trace[debug] "{view_set_lemma}"
      trace[debug] "{set_set_lemma}"
      trace[debug] "{set_view_lemma}"
      trace[debug] "{lawful_lens_instance}"
      trace[debug] "{comp_view_lemma}"
      trace[debug] "{comp_set_lemma}"
      trace[debug] "{view_set_comp_lemma}"
      trace[debug] "{view_set_comp3_lemma}"
      elabCommand <| defn
      elabCommand <| view_set_lemma
      elabCommand <| set_set_lemma
      elabCommand <| set_view_lemma
      elabCommand <| lawful_lens_instance
      elabCommand <| comp_view_lemma
      --elabCommand <| comp_set_lemma
      --elabCommand <| view_set_comp_lemma
      elabCommand <| view_set_comp2_lemma
      --elabCommand <| view_set_comp3_lemma
    for main_field in info.fieldInfo do
      let main_ident := mkIdent $ name' ++ "l" ++ main_field.fieldName
      let main_lens ← `((@$main_ident $names:ident*))
      let freshName r y := mkIdent <| name' ++ "l" ++ (Name.mkSimple (toString main_field.fieldName ++ r ++ y))
      for other_field in info.fieldInfo do
        if main_field.fieldName == other_field.fieldName then
          pure ()
        else do
          let other_ident := mkIdent $ name' ++ "l" ++ other_field.fieldName
          let other_lens ← `((@$other_ident $names:ident*))
          let freshName' := freshName ("_" ++ toString other_field.fieldName)
          let contr_set_view_lemma ←
            `(@[aesop norm (rule_sets := [lens])] theorem $(freshName' "_set_view"):ident $names:ident* :
                ∀ v s,
                  @view _ _ $main_lens
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ $main_lens s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $main_ident:ident, $other_ident:ident])
          let contr_set_view_comp_lemma ←
            `(@[aesop norm (rule_sets := [lens])] theorem $(freshName' "_set_view_comp"):ident $names:ident* :
                ∀ x v s (f: Lens' _ x),
                  @view _ _ $main_lens
                    (@set _ _ _ _ ($other_lens ⊚ f) v s)
                  = @view _ _ $main_lens s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, comp, $main_ident:ident, $other_ident:ident])
          let contr_set_view_comp_lemma2 ←
            `(@[aesop norm (rule_sets := [lens])] theorem $(freshName' "_set_view_comp2"):ident $names:ident* :
                ∀ x y v s (g: Lens' _ y) (f: Lens' _ x),
                  @view _ _ ($main_lens ⊚ g)
                    (@set _ _ _ _ ($other_lens ⊚ f) v s)
                  = @view _ _ ($main_lens ⊚ g) s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, comp, $main_ident:ident, $other_ident:ident])
          let contr_set_view_comp_lemma3 ←
            `(@[aesop norm (rule_sets := [lens])] theorem $(freshName' "_set_view_comp3"):ident $names:ident* :
                ∀ y v s (g: Lens' _ y),
                  @view _ _ ($main_lens ⊚ g)
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ ($main_lens ⊚ g) s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, comp, $main_ident:ident, $other_ident:ident])
          trace[debug] "{contr_set_view_lemma}"
          trace[debug] "{contr_set_view_comp_lemma2}"
          trace[debug] "{contr_set_view_comp_lemma3}"
          elabCommand <| contr_set_view_lemma
          elabCommand <| contr_set_view_comp_lemma
          --elabCommand <| contr_set_view_comp_lemma2
          --elabCommand <| contr_set_view_comp_lemma3
  | _ => throwUnsupportedSyntax

def update_Fin {a} (i' : Fin n)  (e : a) (f : Fin n -> a) : Fin n -> a :=
  fun i =>
    if i == i' then
      e
    else
      f i

@[simp]
theorem update_Fin_gso {a: Type} (i i' : Fin n)  (e : a) (f : Fin n -> a) :
  ¬(i = i') -> update_Fin i' e f i = f i := by intro h1; simp [update_Fin, h1]

@[simp]
theorem update_Fin_gss {a: Type} (i  : Fin n)  (e : a) (f : Fin n -> a) :
  update_Fin i e f i  = e := by simp [update_Fin]

def fin_at {n} (i : Fin n) : Lens' (Fin n → a) a :=
  lens' (fun a => a i) (fun a b => update_Fin i b a)

end Leanses

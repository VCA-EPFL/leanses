/-
Copyright (c) 2024 Yann Herklotz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Init.Meta
import Lean.Data.Options
import Leanses.Options

namespace Leanses

structure Const (α β: Type _) where
  get : α

instance {α} : Functor (Const α) where
  map _ a := Const.mk a.get

instance {α} : LawfulFunctor (Const α) where
  id_map := by
    intros; unfold id Functor.map instFunctorConst; simp
  comp_map := by
    intros; unfold Functor.map instFunctorConst; simp
  map_const := by
    unfold Functor.mapConst Functor.map instFunctorConst
    simp

instance {α} [Inhabited α] [Append α] : Applicative (Const α) where
  pure _ := Const.mk default
  seq f a := Const.mk $ f.get ++ (a ()).get

class IndexedFunctor {a b x y} (f : Type _ → Type _ → Type _) where
    -- | imap is similar to fmap
    imap : (x → y) -- ^ function to apply to first parameter
           → (a → b) -- ^ function to apply to second parameter
           → f x a    -- ^ indexed functor
           → f y b

structure Endo (α: Type _) where
  app : α → α

instance {α} : Append (Endo α) where
  append a b := Endo.mk (a.app ∘ b.app)

instance {α} : Inhabited (Endo α) where
  default := Endo.mk id

def Lens s t a b := ∀ f [Functor f], (a → f b) → s → f t
abbrev Lens' a b := Lens a a b b

def Traversal s t a b := ∀ f [Functor f] [Applicative f], (a → f b) → s → f t
abbrev Traversal' a b := Traversal a a b b

def ITraversal s t a b := ∀ f [Functor f] [Applicative f], (a → f b) → s → f t
abbrev ITraversal' a b := Traversal a a b b

instance {s t a b} : Coe (Lens s t a b) (Traversal s t a b) where
  coe a := fun F => a F

instance {s a} : Coe (Lens' s a) (Traversal' s a) where
  coe a := fun F => a F

def Getting r s a := (a → Const r a) → s → Const r s

instance {a b} : Coe (Lens' a b) (∀ r, Getting r a b) where
  coe a := fun r => a (Const r)

instance {r a b} [Inhabited r] [Append r] : Coe (Traversal' a b) (Getting r a b) where
  coe a := a (Const r)

def ASetter s t a b := (a → Id b) → s → Id t
abbrev ASetter' s a := ASetter s s a a

instance {s t a b} : Coe (Lens s t a b) (ASetter s t a b) where
  coe a := a Id

instance {s t a b} : Coe (Traversal s t a b) (ASetter s t a b) where
  coe a := a Id

def lens {s t a b} (get: s → a) (set: s → b → t): Lens s t a b :=
  fun F [Functor F] afb s => Functor.map (set s) (afb (get s))

def lens' {s a} (get: s → a) (set: s → a → s): Lens' s a :=
  lens get set

def over {s t a b} (setter: Lens s t a b) (upd: a → b): s → t :=
  Id.run ∘ setter Id (pure ∘ upd)

def set {s t a b} (setter: Lens s t a b) (v: b): s → t :=
  Id.run ∘ setter Id (fun _ => pure v)

def gset {s t a b} (setter: ASetter s t a b) (v: b): s → t :=
  Id.run ∘ setter (fun _ => pure v)

def view {s a} (getting: Lens' s a): s → a := Const.get ∘ getting (Const a) Const.mk

def fview {s a} := flip (@view s a)

def fold_map_of {r s a} [Append r] [Inhabited r] (l: Traversal' s a) (f: a → r) :=
  Const.get ∘ l _ (Const.mk ∘ f)

def foldr_of {s a r} (l: Traversal' s a) (f: a → r → r) (z: r) :=
  flip Endo.app z ∘ fold_map_of l (Endo.mk ∘ f)

def to_list_of {s a} (l: Traversal' s a) :=
  foldr_of l List.cons []

def fto_list_of {a s} := flip (@to_list_of a s)

class LawfulLens {s a} (l : Lens' s a) : Prop where
  view_set : ∀ s v, view l (set l v s) = v
  set_view : ∀ s, set l (view l s) s = s
  set_set : ∀ s v v', set l v' (set l v s) = set l v' s

class Composable4 (T: Type _ → Type _ → Type _ → Type _ → Type _) where
  comp4 {s t a b x y : Type _} (f : T s t a b) (g : T a b x y) : T s t x y

class Composable2 (T: Type _ → Type _ → Type _) where
  comp {s a x : Type _} (f : T s a) (g : T a x) : T s x

instance : Composable4 Lens where
  comp4 f g := fun F => f F ∘ g F

instance : Composable4 Traversal where
  comp4 f g := fun F => f F ∘ g F

instance : Composable4 ASetter where
  comp4 f g := f ∘ g

instance {T} [Composable4 T] : Composable2 (fun a b => T a a b b) where
  comp := Composable4.comp4

instance {r} : Composable2 (Getting r) where
  comp f g := f ∘ g

def comp {t a b} [tinst : Composable2 t] := @Composable2.comp t tinst a b

infixr:90 "⊚" => Composable2.comp
infixr:90 "∘∘" => Composable4.comp4

infix:60 "^." => fview
infix:60 "^.." => fto_list_of

--------------------------------------------------------------------------------

syntax (priority := high) "<{ " term " with " (term " := " term),+ " }>" : term
syntax (priority := high) "<{ " term " ... " " }>" : term

syntax (priority := high) "<{ " term " | " term ("." term)* " }>" : term

macro_rules
  | `(<{$y with $x := $z}>) => `(set $x $z $y)
  | `(<{$y with $x := $z, $[$xs:term := $zs:term],*}>) =>
    `(set $x $z (<{ $y with $[$xs:term := $zs:term],* }>))

macro_rules
  | `(<{ $y | $x }>) => `(view $x $y)
  | `(<{ $y | $x . $z $[. $w]* }>) => `(view $x <{ $y | $z $[. $w]* }> )

@[app_unexpander Leanses.set]
def unexpanderSet : Lean.PrettyPrinter.Unexpander
  | `($(_) $lens:term $item:term <{ $rest:term with $[$xs:term := $zs:term],* }>) =>
    `(<{ $rest:term with $lens:term := $item:term, $[$xs:term := $zs:term],* }>)
  | `($(_) $lens:term $item:term $rest:term) =>
    `(<{ $rest:term with $lens:term := $item:term }>)
  | _ => throw ()

--@[app_unexpander Leanses.view]
--def unexpanderView : Lean.PrettyPrinter.Unexpander
--  | `($(_) $lens:term <{ $rest:term | $a:term $[. $z:term]* }>) =>
--    `(<{ $rest:term | $lens:term . $a:term $[. $z:term]* }>)
--  | `($(_) $lens:term $rest:term) =>
--    `(<{ $rest:term | $lens:term }>)
--  | _ => throw ()

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
    let typeName := mkIdent <| ← mkFreshUserName (Name.mkSimple "t")
    generateFreshNamesAux r <| arr.push typeName
  | Expr.sort _ => pure arr
  | l => throwError "Unexpected construct in structure type: {repr l}"

def generateFreshNames (x : Expr) : CoreM (Array (TSyntax `ident)) := generateFreshNamesAux x default

def generateNFreshNamesAux (x : Nat) (arr : Array (TSyntax `ident)) : CoreM (Array (TSyntax `ident)) := do
  match x with
  | y + 1 => do
    let typeName := mkIdent <| ← mkFreshUserName (Name.mkSimple "v")
    generateNFreshNamesAux y <| arr.push typeName
  | 0 => pure arr

def generateNFreshNames (x : Nat) : CoreM (Array (TSyntax `ident)) := generateNFreshNamesAux x default

addlensunfoldrule view
addlensunfoldrule set
addlensunfoldrule Functor.map
addlensunfoldrule lens'
addlensunfoldrule lens
addlensunfoldrule Id.run
addlensunfoldrule Const.get
addlensunfoldrule fview
addlensunfoldrule over
addlensunfoldrule comp
addlensunfoldrule Composable2.comp
addlensunfoldrule Composable4.comp4
addlensunfoldrule flip
addlensunfoldrule Function.comp
addlensunfoldrule pure

def getConstructors {m} [Monad m] [MonadEnv m] [MonadError m] (constName : Name) : m (Option InductiveVal) := do
  let cinfo ← getConstInfo constName
  match cinfo with
  | ConstantInfo.inductInfo val => return some val
  | _ => return none

syntax (name := mkLens) "mklenses" ident : command

open Lean Meta PrettyPrinter Delaborator SubExpr Core in
@[command_elab mkLens] def mkLensHandler : CommandElab
  | `(mklenses $i) => do
    let name ← resolveGlobalConstNoOverload i
    let nameInst ← liftTermElabM <| liftMetaM <| mkConstWithFreshMVarLevels name
    let structureType ← liftTermElabM <| liftMetaM <| inferType nameInst
    let names : TSyntaxArray `ident ← liftCoreM <| generateFreshNames structureType
    let numArgs := structureType.getForallBinderNames.length
    trace[debug] "{numArgs}"
    let Name.str _ name' := name.eraseMacroScopes
      | throwErrorAt i "not name"
    let env ← getEnv
    let some info := getStructureInfo? env name
      | throwErrorAt i "Not a structure"
    let some ctorinfo ← getConstructors name
      | throwErrorAt i "No constructors found"
    trace[debug] "{structureType}"
    trace[debug] "{ctorinfo.ctors}, {ctorinfo.numParams}, {ctorinfo.numIndices}"
    let [ctorname] := ctorinfo.ctors
      | throwErrorAt i "Inductive types not supported"
    let freshFieldNameVars ← liftCoreM <| generateNFreshNames info.fieldNames.size
    for field in info.fieldInfo do
      let some field_idx := info.fieldNames.indexOf? field.fieldName
        | throwErrorAt i "Could not find field name index"
      let field_fresh_var := freshFieldNameVars.get! field_idx
      trace[debug] "field_idx: {field_idx}"
      trace[debug] "{repr field}"
      let fieldNameIdent := mkIdent $ Name.mkSimple name' ++ Name.mkSimple "l" ++ field.fieldName
      let fieldNameIdent' := mkIdent field.fieldName
      let freshName r := mkIdent <| Name.mkSimple name' ++ Name.mkSimple "l" ++ (Name.mkSimple (toString field.fieldName ++ r))
      let accessor ← `(fun a => @$(mkIdent field.projFn) $names:ident* a)
      let setter ←
        `(fun a => (fun b => { a with $fieldNameIdent':ident := b }))
      let appliedLens ← `((@$fieldNameIdent $names:ident*))
      let defn ← `(def $fieldNameIdent $names:ident* := @lens' _ _ $accessor $setter)
      trace[debug] "{defn}"
      trace[Leanses.traceNames] "{freshName "_view_set"}"
      let view_set_lemma ←
        `(theorem $(freshName "_view_set") $names:ident* :
            ∀ s v,
              @view _ _
                $appliedLens (@set _ _ _ _ $appliedLens v s) = v := by intros; rfl)
      trace[debug] "{view_set_lemma}"
      trace[Leanses.traceNames] "{freshName "_set_set"}"
      let set_set_lemma ←
        `(theorem $(freshName "_set_set") $names:ident* :
            ∀ s v v', @set _ _ _ _ $appliedLens v' (@set _ _ _ _ $appliedLens v s)
                      = @set _ _ _ _ $appliedLens v' s := by intros; rfl)
      trace[Leanses.traceNames] "{freshName "_set_view"}"
      let set_view_lemma ←
        `(theorem $(freshName "_set_view") $names:ident* :
            ∀ s, @set _ _ _ _ $appliedLens (@view _ _ $appliedLens s) s = s := by intros; rfl)
      let lawful_lens_instance ←
        `(instance ($names:ident*) : LawfulLens ($fieldNameIdent $names:ident*) where
            view_set := $(freshName "_view_set") $names:ident*
            set_set := $(freshName "_set_set") $names:ident*
            set_view := $(freshName "_set_view") $names:ident*)
      let view_constr_lemma ←
        `(theorem $(freshName "_view_constr") $names:ident* :
            ∀ $freshFieldNameVars:ident*, @view _ _ $appliedLens (@$(mkIdent ctorname):ident $(names ++ freshFieldNameVars):ident*) = $field_fresh_var:ident := by intros; rfl)
      trace[Leanses.traceNames] "{freshName "_comp_view"}"
      let comp_view_lemma ←
        `(theorem $(freshName "_comp_view") $names:ident* :
            ∀ α s (g : Lens' _ α), @view _ _ ($appliedLens ∘∘ g) s = @view _ _ g (@view _ _ $appliedLens s) := by intros; rfl)
      let comp_set_lemma ←
        `(theorem $(freshName "_comp_set") $names:ident* :
            ∀ α v s (g : Lens' _ α),
              @set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ α α $appliedLens g) v s
              = @set _ _ _ _ $appliedLens (@set _ _ _ _ g v (@view _ _ $appliedLens s)) s := by intros; rfl)
      --let _set_set_comp_lemma ←
      --  `(theorem $(freshName "_comp_set_set") $names:ident* :
      --      ∀ α s (v v': α) (g : Lens' _ α), @set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ α α $appliedLens g) v' (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ α α $appliedLens g) v s)
      --                = @set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ α α $appliedLens g) v' s := by
      --      simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4, $fieldNameIdent:ident])
      let view_set_comp_lemma ←
        `(theorem $(freshName "_view_set_comp") $names:ident* :
            ∀ x y v s (f: Lens' _ x) (g: Lens' _ y),
              @view _ _ ($appliedLens ∘∘ f)
                (@set _ _ _ _ (Composable4.comp4 Lens _ _ _ _ _ y y $appliedLens g) v s)
              = @view _ _ f (@set _ _ y y g v (@view _ _ $appliedLens s)) := by intros; rfl)
      trace[Leanses.traceNames] "{freshName "_view_set_comp2"}"
      let view_set_comp2_lemma ←
        `(theorem $(freshName "_view_set_comp2") $names:ident* :
            ∀ y v s (g: Lens' _ y),
              @view _ _ $appliedLens (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ y y $appliedLens g) v s)
              = @set _ _ y y g v (@view _ _ $appliedLens s) := by intros; rfl)
      let view_set_comp3_lemma ←
        `(theorem $(freshName "_view_set_comp3") $names:ident* :
            ∀ y v s (g: Lens' _ y),
              @view _ _ ($appliedLens ∘∘ g) (@set _ _ _ _ $appliedLens v s)
              = @view _ _ g v := by intros; rfl)
      trace[Leanses.impl] "{defn}"
      trace[Leanses.impl] "{view_set_lemma}"
      trace[Leanses.impl] "{set_set_lemma}"
      trace[Leanses.impl] "{set_view_lemma}"
      trace[Leanses.impl] "{lawful_lens_instance}"
      trace[Leanses.impl] "{comp_view_lemma}"
      trace[Leanses.impl] "{comp_set_lemma}"
      trace[Leanses.impl] "{view_set_comp_lemma}"
      trace[Leanses.impl] "{view_set_comp3_lemma}"
      trace[Leanses.impl] "{view_constr_lemma}"
      elabCommand <| defn
      elabCommand <| ← `(addlensunfoldrule $fieldNameIdent:ident)
      elabCommand <| view_set_lemma
      elabCommand <| ← `(addlensrule $(freshName "_view_set"):ident)
      elabCommand <| set_set_lemma
      elabCommand <| ← `(addlensrule $(freshName "_set_set"):ident)
      elabCommand <| set_view_lemma
      elabCommand <| ← `(addlensrule $(freshName "_set_view"):ident)
      elabCommand <| lawful_lens_instance
      elabCommand <| view_constr_lemma
      elabCommand <| ← `(addlensrule $(freshName "_view_constr"):ident)
      elabCommand <| comp_view_lemma
      elabCommand <| ← `(addlensrule $(freshName "_comp_view"):ident)
      -- trace[debug] "{set_set_comp_lemma}"
      -- elabCommand <| set_set_comp_lemma
      -- elabCommand <| ← `(addlensrule $(freshName "_comp_set_set"):ident)
      --elabCommand <| comp_set_lemma
      --elabCommand <| view_set_comp_lemma
      elabCommand <| view_set_comp2_lemma
      elabCommand <| ← `(addlensrule $(freshName "_view_set_comp2"):ident)
      --elabCommand <| view_set_comp3_lemma
    for main_field in info.fieldInfo do
      let main_ident := mkIdent $ Name.mkSimple name' ++ Name.mkSimple "l" ++ main_field.fieldName
      let main_lens ← `((@$main_ident $names:ident*))
      let freshName r y := mkIdent <| Name.mkSimple name' ++ Name.mkSimple "l" ++ (Name.mkSimple (toString main_field.fieldName ++ r ++ y))
      for other_field in info.fieldInfo do
        if main_field.fieldName == other_field.fieldName then
          pure ()
        else do
          let other_ident := mkIdent $ Name.mkSimple name' ++ Name.mkSimple "l" ++ other_field.fieldName
          let other_lens ← `((@$other_ident $names:ident*))
          let freshName' := freshName ("_" ++ toString other_field.fieldName)
          trace[Leanses.traceNames] "{freshName' "_set_view"}"
          let contr_set_view_lemma ←
            `(theorem $(freshName' "_set_view"):ident $names:ident* :
                ∀ v s,
                  @view _ _ $main_lens
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ $main_lens s := by intros; rfl)
          trace[Leanses.traceNames] "{freshName' "_set_view_comp"}"
          let contr_set_view_comp_lemma ←
            `(theorem $(freshName' "_set_view_comp"):ident $names:ident* :
                ∀ x v s (f: Lens' _ x),
                  @view _ _ $main_lens
                    (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ x x $other_lens f) v s)
                  = @view _ _ $main_lens s := by intros; rfl)
          let _contr_set_view_comp_lemma2 ←
            `(theorem $(freshName' "_set_view_comp2"):ident $names:ident* :
                ∀ x y v s (g: Lens' _ y) (f: Lens' _ x),
                  @view _ _ ($main_lens ∘∘ g)
                    (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ x x $other_lens f) v s)
                  = @view _ _ ($main_lens ∘∘ g) s := by intros; rfl)
          let _contr_set_view_comp_lemma3 ←
            `(theorem $(freshName' "_set_view_comp3"):ident $names:ident* :
                ∀ y v s (g: Lens' _ y),
                  @view _ _ ($main_lens ∘∘ g)
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ ($main_lens ∘∘ g) s := by intros; rfl)
          trace[Leanses.impl] "{contr_set_view_lemma}"
          trace[Leanses.impl] "{contr_set_view_comp_lemma}"
          elabCommand <| contr_set_view_lemma
          elabCommand <| ← `(addlensrule $(freshName' "_set_view"):ident)
          elabCommand <| contr_set_view_comp_lemma
          elabCommand <| ← `(addlensrule $(freshName' "_set_view_comp"):ident)
          --elabCommand <| contr_set_view_comp_lemma2
          --elabCommand <| contr_set_view_comp_lemma3
  | _ => throwUnsupportedSyntax

def update_Fin {a} {n} (i' : Fin n)  (e : a) (f : Fin n → a) : Fin n → a :=
  fun i =>
    if i == i' then
      e
    else
      f i

theorem fview_view x y a b:
  @fview x y b a = @view x y a b := by
  simp [fview, flip]
addlensrule fview_view

@[simp]
theorem update_Fin_gso {a: Type} {n} (i i' : Fin n) (e : a) (f : Fin n → a) :
  ¬(i = i') → update_Fin i' e f i = f i := by intro h1; simp [update_Fin, h1]

@[simp]
theorem update_Fin_gso2 {a: Type} {n} (i i' : Fin n) (e : a) (f : Fin n → a) :
  ¬(i' = i) → update_Fin i' e f i = f i := by
    intro h1
    have h1 := Ne.symm h1
    simp [h1]

@[simp]
theorem update_Fin_gss {n} {a: Type} (i  : Fin n)  (e : a) (f : Fin n → a) :
  update_Fin i e f i  = e := by simp [update_Fin]

def fin_at {a n} (i : Fin n) : Lens' (Fin n → a) a :=
  lens' (fun a => a i) (fun a b => update_Fin i b a)
addlensunfoldrule fin_at

theorem fin_at_gss {n : Nat} {m : Fin n} {α : Type _} {x : α} {y : Fin n → α} :
  view (fin_at m) (set (fin_at m) x y) = x := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,pure]
addlensrule fin_at_gss

theorem fin_at_gss_comp {n : Nat} {m : Fin n} {s a b : Type _} {g : Lens s s a b} {x : b} {y : Fin n → s} :
  view (fin_at m) (set (fin_at m∘∘g) x y) = set g x (view (fin_at m) y) := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,Composable2.comp,Composable4.comp4]
addlensrule fin_at_gss_comp

theorem fin_at_gso {n : Nat} {n' m : Fin n} {α : Type _} {x : α} {y : Fin n → α} :
  ¬ n' = m → view (fin_at n') (set (fin_at m) x y) = view (fin_at n') y := by
  intros h1; simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,h1]
addlensrule fin_at_gso

theorem fin_at_gso2 {n' : Nat} {m n : Fin n'} {α : Type _} {x : α} {y : Fin n' → α} :
  ¬ m = n → view (fin_at n) (set (fin_at m) x y) = view (fin_at n) y := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,this]
addlensrule fin_at_gso2

theorem fin_at_gso2_comp {n' : Nat} {m n : Fin n'} {s a b : Type _} {g : Lens s s a b} {x : b} {y : Fin n' → s} :
  ¬ m = n → view (fin_at n) (set (fin_at m∘∘g) x y) = view (fin_at n) y := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,this,Composable4.comp4,Composable2.comp]
addlensrule fin_at_gso2_comp

theorem fin_at_gso_comp {n' : Nat} {n m : Fin n'} {s a b : Type _} {g : Lens s s a b} {x : b} {y : Fin n' → s} :
  ¬ n = m → view (fin_at n) (set (fin_at m∘∘g) x y) = view (fin_at n) y := by
  intros h1; simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,h1,Composable4.comp4,Composable2.comp]
addlensrule fin_at_gso_comp

theorem fin_at_gso_app {n' : Nat} {n m : Fin n'} {α : Type _} {x : α} {y : Fin n' → α} :
  ¬ n = m → (set (fin_at m) x y) n = y n := by
  intros h1; simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,h1]
--addlensrule fin_at_gso_app

theorem fin_at_gso2_app {n' : Nat} {m n : Fin n'} {α : Type _} {x : α} {y : Fin n' → α} :
  ¬ m = n → (set (fin_at m) x y) n = y n := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,this]
--addlensrule fin_at_gso2_app

theorem fin_at_gso2_comp_app {n' : Nat} {m n : Fin n'} {s a b : Type _} {g : Lens s s a b} {x : b} {y : Fin n' → s} :
  ¬ m = n → (set (fin_at m∘∘g) x y) n = y n := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,this,Composable4.comp4,Composable2.comp]
--addlensrule fin_at_gso2_comp_app

theorem fin_at_gso_comp_app {n' : Nat} {n m : Fin n'} {s a b : Type _} {g : Lens s s a b} {x : b} {y : Fin n' → s} :
  ¬ n = m → (set (fin_at m∘∘g) x y) n = y n := by
  intros h1; simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,h1,Composable4.comp4,Composable2.comp]
--addlensrule fin_at_gso_comp_app

theorem fin_at_apply {n' : Nat} {n : Fin n'} {α : Type _} {y : Fin n' → α} :
  view (fin_at n) y = y n := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,Composable4.comp4,Composable2.comp]
--addlensrule fin_at_apply

theorem fin_at_gss2 {n' : Nat} {n : Fin n'} {α : Type _} {x : α} {y : Fin n' → α} :
  (set (fin_at n) x y) n = x := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,pure]
--addlensrule fin_at_gss2

theorem fin_at_gss2_comp {n' : Nat} {n : Fin n'} {s a b : Type _} {g : Lens s s a b} {x : b} {y : Fin n' → s} :
  (set (fin_at n∘∘g) x y) n = set g x (y n) := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,Composable4.comp4,Composable2.comp]
--addlensrule fin_at_gss2_comp

theorem fin_at_view_comp {n' : Nat} {n : Fin n'} {s a : Type _} {g : Lens s s a a} {x : Fin n' → s} :
  view (fin_at n∘∘g) x = view g (view (fin_at n) x) := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,Composable4.comp4,Composable2.comp]
addlensrule fin_at_view_comp

def liftA2 {F a b c} [Applicative F] (f: a → b → c) (x: F a) (y: F b) :=
  (f <$> x) <*> y

def traverse_list' {F a b} [Applicative F] (f: a → F b) : List a → F (List b) :=
  List.foldr cons_f (pure [])
  where cons_f x ys := liftA2 List.cons (f x) ys

def traverse_list {a} : Traversal' (List a) a :=
  fun F _ inst2 => @traverse_list' F _ _ inst2

def range (n : Nat) : List (Fin n) :=
  loop n (Nat.le_of_eq (Eq.refl n)) []
where
  loop : (y:Nat) → y <= n → List (Fin n) → List (Fin n)
  | 0,   _,  ns => ns
  | n+1, lt, ns => let ltn := Nat.lt_of_succ_le lt; loop n (Nat.le_of_lt ltn) ({val := n, isLt := ltn}::ns)

def traverse_Fin' {F a b n} [Inhabited b] [Applicative F] (f: a → F b) (l: Fin n → a): F (Fin n → b) :=
  List.foldr cons_r (pure (fun _ => default)) (range n)
  where cons_r x ys := liftA2 (update_Fin x) (f (l x)) ys

def traverse_Fin'' {F a b n} [Inhabited b] [Applicative F] (f: Nat → a → F b) (l: Fin n → a): F (Fin n → b) :=
  List.foldr cons_r (pure (fun _ => default)) (range n)
  where cons_r x ys := liftA2 (update_Fin x) (f x (l x)) ys

def traverse_Fin {n} {a} [Inhabited a] : Traversal' (Fin n → a) a :=
  fun _ => traverse_Fin'

@[simp]
def set_Fin {n} {a} [Inhabited a] : ASetter' (Fin n → a) a := @traverse_Fin n a _

end Leanses

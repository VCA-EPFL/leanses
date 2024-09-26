/-
Copyright (c) 2024 Yann Herklotz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Init.Meta
import Lean.Data.Options
import Leanses.Options

namespace Leanses.UniverseLens

structure Lens (s : Sort _) (t : Sort _) (a : Sort _) (b : Sort _) where
  get : s → a
  set : s → b → t

abbrev Lens' s a := Lens s s a a

def lens' {s : Sort _} {a : Sort _} (get : s → a) (set : s → a → s) : Lens' s a := Lens.mk get set

def over {s t a b} (lens: Lens s t a b) (upd: a → b): s → t :=
  fun s => lens.set s (upd (lens.get s))

def set {s t a b} (lens: Lens s t a b) (v: b): s → t :=
  fun s => lens.set s v

def view {s a} (lens: Lens' s a): s → a := lens.get

def fview {s a} := flip (@view s a)

class LawfulLens {s a} (l : Lens' s a) : Prop where
  view_set : ∀ s v, view l (set l v s) = v
  set_view : ∀ s, set l (view l s) s = s
  set_set : ∀ s v v', set l v' (set l v s) = set l v' s

class Composable4 (T: Type _ → Type _ → Type _ → Type _ → Type _) where
  comp4 {s t a b x y : Type _} (f : T s t a b) (g : T a b x y) : T s t x y

instance : Composable4 Lens where
  comp4 f g := Lens.mk (g.get ∘ f.get) (fun s b => f.set s (g.set (f.get s) b))

infixr:90 "∘∘" => Composable4.comp4

syntax (priority := high) "<{ " term " with " (term " := " term),+ " }>" : term
syntax (priority := high) "<{ " term " ... }>" : term

syntax (priority := high) "<{ " term " | " term ("." term)* " }>" : term

macro_rules
  | `(<{$y with $x := $z}>) => `(set $x $z $y)
  | `(<{$y with $x := $z, $[$xs:term := $zs:term],*}>) =>
    `(set $x $z (<{ $y with $[$xs:term := $zs:term],* }>))

macro_rules
  | `(<{ $y | $x }>) => `(view $x $y)
  | `(<{ $y | $x . $z $[. $w]* }>) => `(view $x <{ $y | $z $[. $w]* }> )

@[app_unexpander Leanses.UniverseLens.set]
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
      let defn ← `(@[ulens_unfold] def $fieldNameIdent $names:ident* := @lens' _ _ $accessor $setter)
      trace[debug] "{defn}"
      trace[Leanses.traceNames] "{freshName "_view_set"}"
      let view_set_lemma ←
        `(@[ulens_set] theorem $(freshName "_view_set") $names:ident* :
            ∀ s v,
              @view _ _
                $appliedLens (@set _ _ _ _ $appliedLens v s) = v := by intros; rfl)
      trace[debug] "{view_set_lemma}"
      trace[Leanses.traceNames] "{freshName "_set_set"}"
      let set_set_lemma ←
        `(@[ulens_set] theorem $(freshName "_set_set") $names:ident* :
            ∀ s v v', @set _ _ _ _ $appliedLens v' (@set _ _ _ _ $appliedLens v s)
                      = @set _ _ _ _ $appliedLens v' s := by intros; rfl)
      trace[Leanses.traceNames] "{freshName "_set_view"}"
      let set_view_lemma ←
        `(@[ulens_set] theorem $(freshName "_set_view") $names:ident* :
            ∀ s, @set _ _ _ _ $appliedLens (@view _ _ $appliedLens s) s = s := by intros; rfl)
      let lawful_lens_instance ←
        `(instance ($names:ident*) : LawfulLens ($fieldNameIdent $names:ident*) where
            view_set := $(freshName "_view_set") $names:ident*
            set_set := $(freshName "_set_set") $names:ident*
            set_view := $(freshName "_set_view") $names:ident*)
      let view_constr_lemma ←
        `(@[ulens_set] theorem $(freshName "_view_constr") $names:ident* :
            ∀ $freshFieldNameVars:ident*, @view _ _ $appliedLens (@$(mkIdent ctorname):ident $(names ++ freshFieldNameVars):ident*) = $field_fresh_var:ident := by intros; rfl)
      trace[Leanses.traceNames] "{freshName "_comp_view"}"
      let comp_view_lemma ←
        `(@[ulens_set] theorem $(freshName "_comp_view") $names:ident* :
            ∀ α s (g : Lens' _ α), @view _ _ ($appliedLens ∘∘ g) s = @view _ _ g (@view _ _ $appliedLens s) := by intros; rfl)
      let comp_set_lemma ←
        `(@[ulens_set] theorem $(freshName "_comp_set") $names:ident* :
            ∀ α v s (g : Lens' _ α),
              @set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ α α $appliedLens g) v s
              = @set _ _ _ _ $appliedLens (@set _ _ _ _ g v (@view _ _ $appliedLens s)) s := by intros; rfl)
      --let _set_set_comp_lemma ←
      --  `(theorem $(freshName "_comp_set_set") $names:ident* :
      --      ∀ α s (v v': α) (g : Lens' _ α), @set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ α α $appliedLens g) v' (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ α α $appliedLens g) v s)
      --                = @set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ α α $appliedLens g) v' s := by
      --      simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4, $fieldNameIdent:ident])
      let view_set_comp_lemma ←
        `(@[ulens_set] theorem $(freshName "_view_set_comp") $names:ident* :
            ∀ x y v s (f: Lens' _ x) (g: Lens' _ y),
              @view _ _ ($appliedLens ∘∘ f)
                (@set _ _ _ _ (Composable4.comp4 Lens _ _ _ _ _ y y $appliedLens g) v s)
              = @view _ _ f (@set _ _ y y g v (@view _ _ $appliedLens s)) := by intros; rfl)
      trace[Leanses.traceNames] "{freshName "_view_set_comp2"}"
      let view_set_comp2_lemma ←
        `(@[ulens_set] theorem $(freshName "_view_set_comp2") $names:ident* :
            ∀ y v s (g: Lens' _ y),
              @view _ _ $appliedLens (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ y y $appliedLens g) v s)
              = @set _ _ y y g v (@view _ _ $appliedLens s) := by intros; rfl)
      let view_set_comp3_lemma ←
        `(@[ulens_set] theorem $(freshName "_view_set_comp3") $names:ident* :
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
      elabCommand <| view_set_lemma
      elabCommand <| set_set_lemma
      elabCommand <| set_view_lemma
      elabCommand <| lawful_lens_instance
      elabCommand <| view_constr_lemma
      elabCommand <| comp_view_lemma
      -- trace[debug] "{set_set_comp_lemma}"
      -- elabCommand <| set_set_comp_lemma
      -- elabCommand <| ← `(addlensrule $(freshName "_comp_set_set"):ident)
      --elabCommand <| comp_set_lemma
      --elabCommand <| view_set_comp_lemma
      elabCommand <| view_set_comp2_lemma
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
            `(@[ulens_set] theorem $(freshName' "_set_view"):ident $names:ident* :
                ∀ v s,
                  @view _ _ $main_lens
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ $main_lens s := by intros; rfl)
          trace[Leanses.traceNames] "{freshName' "_set_view_comp"}"
          let contr_set_view_comp_lemma ←
            `(@[ulens_set] theorem $(freshName' "_set_view_comp"):ident $names:ident* :
                ∀ x v s (f: Lens' _ x),
                  @view _ _ $main_lens
                    (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ x x $other_lens f) v s)
                  = @view _ _ $main_lens s := by intros; rfl)
          let _contr_set_view_comp_lemma2 ←
            `(@[ulens_set] theorem $(freshName' "_set_view_comp2"):ident $names:ident* :
                ∀ x y v s (g: Lens' _ y) (f: Lens' _ x),
                  @view _ _ ($main_lens ∘∘ g)
                    (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ x x $other_lens f) v s)
                  = @view _ _ ($main_lens ∘∘ g) s := by intros; rfl)
          let _contr_set_view_comp_lemma3 ←
            `(@[ulens_set] theorem $(freshName' "_set_view_comp3"):ident $names:ident* :
                ∀ y v s (g: Lens' _ y),
                  @view _ _ ($main_lens ∘∘ g)
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ ($main_lens ∘∘ g) s := by intros; rfl)
          trace[Leanses.impl] "{contr_set_view_lemma}"
          trace[Leanses.impl] "{contr_set_view_comp_lemma}"
          elabCommand <| contr_set_view_lemma
          elabCommand <| contr_set_view_comp_lemma
  | _ => throwUnsupportedSyntax

def update_Fin {a n} (i' : Fin n)  (e : a) (f : Fin n → a) : Fin n → a :=
  fun i =>
    if i == i' then
      e
    else
      f i

@[ulens_set] theorem fview_view x y a b:
  @fview x y b a = @view x y a b := by
  simp [fview, flip]

@[simp, ulens_set]
theorem update_Fin_gso {a: Type} {n} (i i' : Fin n)  (e : a) (f : Fin n → a) :
  ¬(i = i') → update_Fin i' e f i = f i := by intro h1; simp [update_Fin, h1]

@[simp, ulens_set]
theorem update_Fin_gso2 {a: Type} {n} (i i' : Fin n)  (e : a) (f : Fin n → a) :
  ¬(i' = i) → update_Fin i' e f i = f i := by
    intro h1
    have h1 := Ne.symm h1
    simp [h1]

@[simp, ulens_set]
theorem update_Fin_gss {a: Type _} {n} (i  : Fin n)  (e : a) (f : Fin n → a) :
  update_Fin i e f i  = e := by simp [update_Fin]

@[ulens_unfold] def fin_at {a: Type _} {n} (i : Fin n) : Lens' (Fin n → a) a :=
  Lens.mk (fun a => a i) (fun a b => update_Fin i b a)

theorem fin_at_gss {α : Type _} {m : Nat} {n : Fin m} (x : α) y :
  view (fin_at n) (set (fin_at n) x y) = x := by
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin,Composable4.comp4]

set_option autoImplicit true

@[ulens_set] theorem fin_at_gss_comp :
  view (fin_at n) (set (fin_at n∘∘g) x y) = set g x (view (fin_at n) y) := by
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin,Composable4.comp4]

@[ulens_set] theorem fin_at_gso :
  ¬ n = m → view (fin_at n) (set (fin_at m) x y) = view (fin_at n) y := by
  intros h1; simp [fin_at,view,set,Functor.map,Id.run,update_Fin,h1]

@[ulens_set] theorem fin_at_gso2 :
  ¬ m = n → view (fin_at n) (set (fin_at m) x y) = view (fin_at n) y := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin,this]

@[ulens_set] theorem fin_at_gso2_comp :
  ¬ m = n → view (fin_at n) (set (fin_at m∘∘g) x y) = view (fin_at n) y := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin,this,Composable4.comp4]

@[ulens_set] theorem fin_at_gso_comp :
  ¬ n = m → view (fin_at n) (set (fin_at m∘∘g) x y) = view (fin_at n) y := by
  intros h1; simp [fin_at,view,set,Functor.map,Id.run,update_Fin,h1,Composable4.comp4]

theorem fin_at_gso_app :
  ¬ n = m → (set (fin_at m) x y) n = y n := by
  intros h1; simp [fin_at,view,set,Functor.map,Id.run,update_Fin,h1]

theorem fin_at_gso2_app :
  ¬ m = n → (set (fin_at m) x y) n = y n := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin,this]

theorem fin_at_gso2_comp_app :
  ¬ m = n → (set (fin_at m∘∘g) x y) n = y n := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin,this,Composable4.comp4]

theorem fin_at_gso_comp_app :
  ¬ n = m → (set (fin_at m∘∘g) x y) n = y n := by
  intros h1; simp [fin_at,view,set,Functor.map,Id.run,update_Fin,h1,Composable4.comp4]

theorem fin_at_apply :
  view (fin_at n) y = y n := by
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin,Composable4.comp4]

theorem fin_at_gss2 :
  (set (fin_at n) x y) n = x := by
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin]

theorem fin_at_gss2_comp :
  (set (fin_at n∘∘g) x y) n = set g x (y n) := by
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin,Composable4.comp4]

@[ulens_set] theorem fin_at_view_comp :
  view (fin_at n∘∘g) x = view g (view (fin_at n) x) := by
  simp [fin_at,view,set,Functor.map,Id.run,update_Fin,Composable4.comp4]

set_option autoImplicit false

end Leanses.UniverseLens

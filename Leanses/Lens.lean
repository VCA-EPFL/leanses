import Lean
import Init.Meta
import Lean.Data.Options
import Leanses.Options
import Aesop

namespace Leanses

syntax "aesop_lens" : tactic
macro_rules
  | `(tactic| aesop_lens) => `(tactic| aesop (rule_sets := [lens]) )

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

class IndexedFunctor (f : Type _ → Type _ → Type _) where
    -- | imap is similar to fmap
    imap : (x → y) -- ^ function to apply to first parameter
           → (a → b) -- ^ function to apply to second parameter
           → f x a    -- ^ indexed functor
           → f y b

structure Endo (α: Type _) where
  app : α → α

instance : Append (Endo α) where
  append a b := Endo.mk (a.app ∘ b.app)

instance : Inhabited (Endo α) where
  default := Endo.mk id

def Lens s t a b := ∀ f [Functor f], (a → f b) → s → f t
abbrev Lens' a b := Lens a a b b

def Traversal s t a b := ∀ f [Functor f] [Applicative f], (a → f b) → s → f t
abbrev Traversal' a b := Traversal a a b b

def ITraversal s t a b := ∀ f [Functor f] [Applicative f], (a → f b) → s → f t
abbrev ITraversal' a b := Traversal a a b b

instance : Coe (Lens s t a b) (Traversal s t a b) where
  coe a := fun F => a F

instance : Coe (Lens' s a) (Traversal' s a) where
  coe a := fun F => a F

def Getting r s a := (a → Const r a) → s → Const r s

instance : Coe (Lens' a b) (∀ r, Getting r a b) where
  coe a := fun r => a (Const r)

instance [Inhabited r] [Append r] : Coe (Traversal' a b) (Getting r a b) where
  coe a := a (Const r)

def ASetter s t a b := (a → Id b) → s → Id t
abbrev ASetter' s a := ASetter s s a a

instance : Coe (Lens s t a b) (ASetter s t a b) where
  coe a := a Id

instance : Coe (Traversal s t a b) (ASetter s t a b) where
  coe a := a Id

def lens (get: s → a) (set: s → b → t): Lens s t a b :=
  fun F [Functor F] afb s => Functor.map (set s) (afb (get s))

def lens' (get: s → a) (set: s → a → s): Lens' s a :=
  lens get set

def over (setter: Lens s t a b) (upd: a → b): s → t :=
  Id.run ∘ setter Id (pure ∘ upd)

def set (setter: Lens s t a b) (v: b): s → t :=
  Id.run ∘ setter Id (fun _ => pure v)

def gset (setter: ASetter s t a b) (v: b): s → t :=
  Id.run ∘ setter (fun _ => pure v)

def view (getting: Lens' s a): s → a := Const.get ∘ getting (Const a) Const.mk

def fview {s a} := flip (@view s a)

def fold_map_of [Append r] [Inhabited r] (l: Traversal' s a) (f: a → r) :=
  Const.get ∘ l _ (Const.mk ∘ f)

def foldr_of (l: Traversal' s a) (f: a → r → r) (z: r) :=
  flip Endo.app z ∘ fold_map_of l (Endo.mk ∘ f)

def to_list_of (l: Traversal' s a) :=
  foldr_of l List.cons []

def fto_list_of {a s} := flip (@to_list_of a s)

class LawfulLens (l : Lens' s a) : Prop where
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

instance [Composable4 T] : Composable2 (fun a b => T a a b b) where
  comp := Composable4.comp4

instance : Composable2 (Getting r) where
  comp f g := f ∘ g

def comp {t a b} [tinst : Composable2 t] := @Composable2.comp t tinst a b

infixr:90 "⊚" => Composable2.comp
infixr:90 "∘∘" => Composable4.comp4

infix:60 "^." => fview
infix:60 "^.." => fto_list_of

--------------------------------------------------------------------------------

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

@[app_unexpander Leanses.set]
def unexpanderSet : Lean.PrettyPrinter.Unexpander
  | `($(_) $lens:term $item:term <{ $rest:term with $[$xs:term := $zs:term],* }>) =>
    `(<{ $rest:term with $lens:term := $item:term, $[$xs:term := $zs:term],* }>)
  | `($(_) $lens:term $item:term $rest:term) =>
    `(<{ $rest:term with $lens:term := $item:term }>)
  | _ => throw ()

@[app_unexpander Leanses.view]
def unexpanderView : Lean.PrettyPrinter.Unexpander
  | `($(_) $lens:term <{ $rest:term | $a:term $[. $z:term]* }>) =>
    `(<{ $rest:term | $lens:term . $a:term $[. $z:term]* }>)
  | `($(_) $lens:term $rest:term) =>
    `(<{ $rest:term | $lens:term }>)
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
      trace[Leanses.traceNames] "{freshName "_view_set"}"
      let view_set_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_view_set") $names:ident* :
            ∀ s v,
              @view _ _
                $appliedLens (@set _ _ _ _ $appliedLens v s) = v := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      trace[debug] "{view_set_lemma}"
      trace[Leanses.traceNames] "{freshName "_set_set"}"
      let set_set_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_set_set") $names:ident* :
            ∀ s v v', @set _ _ _ _ $appliedLens v' (@set _ _ _ _ $appliedLens v s)
                      = @set _ _ _ _ $appliedLens v' s := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      trace[Leanses.traceNames] "{freshName "_set_view"}"
      let set_view_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_set_view") $names:ident* :
            ∀ s, @set _ _ _ _ $appliedLens (@view _ _ $appliedLens s) s = s := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $fieldNameIdent:ident])
      let lawful_lens_instance ←
        `(instance ($names:ident*) : LawfulLens ($fieldNameIdent $names:ident*) where
            view_set := $(freshName "_view_set") $names:ident*
            set_set := $(freshName "_set_set") $names:ident*
            set_view := $(freshName "_set_view") $names:ident*)
      trace[Leanses.traceNames] "{freshName "_comp_view"}"
      let comp_view_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_comp_view") $names:ident* :
            ∀ α s (g : Lens' _ α), @view _ _ ($appliedLens ∘∘ g) s = @view _ _ g (@view _ _ $appliedLens s) := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4
                 , $fieldNameIdent:ident])
      let comp_set_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_comp_set") $names:ident* :
            ∀ α v s (g : Lens' _ α),
              @set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ α α $appliedLens g) v s
              = @set _ _ _ _ $appliedLens (@set _ _ _ _ g v (@view _ _ $appliedLens s)) s := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4
                 , $fieldNameIdent:ident])
      let view_set_comp_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_view_set_comp") $names:ident* :
            ∀ x y v s (f: Lens' _ x) (g: Lens' _ y),
              @view _ _ ($appliedLens ∘∘ f)
                (@set _ _ _ _ (Composable4.comp4 Lens _ _ _ _ _ y y $appliedLens g) v s)
              = @view _ _ f (@set _ _ y y g v (@view _ _ $appliedLens s)) := by
            simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4
                 , $fieldNameIdent:ident])
      trace[Leanses.traceNames] "{freshName "_view_set_comp2"}"
      let view_set_comp2_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_view_set_comp2") $names:ident* :
            ∀ y v s (g: Lens' _ y),
              @view _ _ $appliedLens (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ y y $appliedLens g) v s)
              = @set _ _ y y g v (@view _ _ $appliedLens s) := by
              simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4
                   , $fieldNameIdent:ident])
      let view_set_comp3_lemma ←
        `(@[aesop norm (rule_sets := [lens])] theorem $(freshName "_view_set_comp3") $names:ident* :
            ∀ y v s (g: Lens' _ y),
              @view _ _ ($appliedLens ∘∘ g) (@set _ _ _ _ $appliedLens v s)
              = @view _ _ g v := by
              simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4
                   , $fieldNameIdent:ident])
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
      elabCommand <| ← `(addlensunfoldrule $fieldNameIdent:ident)
      elabCommand <| view_set_lemma
      elabCommand <| ← `(addlensrule $(freshName "_view_set"):ident)
      elabCommand <| set_set_lemma
      elabCommand <| ← `(addlensrule $(freshName "_set_set"):ident)
      elabCommand <| set_view_lemma
      elabCommand <| ← `(addlensrule $(freshName "_set_view"):ident)
      elabCommand <| lawful_lens_instance
      elabCommand <| comp_view_lemma
      elabCommand <| ← `(addlensrule $(freshName "_comp_view"):ident)
      --elabCommand <| comp_set_lemma
      --elabCommand <| view_set_comp_lemma
      elabCommand <| view_set_comp2_lemma
      elabCommand <| ← `(addlensrule $(freshName "_view_set_comp2"):ident)
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
          trace[Leanses.traceNames] "{freshName' "_set_view"}"
          let contr_set_view_lemma ←
            `(@[aesop norm (rule_sets := [lens])] theorem $(freshName' "_set_view"):ident $names:ident* :
                ∀ v s,
                  @view _ _ $main_lens
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ $main_lens s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, $main_ident:ident, $other_ident:ident])
          trace[Leanses.traceNames] "{freshName' "_set_view_comp"}"
          let contr_set_view_comp_lemma ←
            `(@[aesop norm (rule_sets := [lens])] theorem $(freshName' "_set_view_comp"):ident $names:ident* :
                ∀ x v s (f: Lens' _ x),
                  @view _ _ $main_lens
                    (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ x x $other_lens f) v s)
                  = @view _ _ $main_lens s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4
                       , $main_ident:ident, $other_ident:ident])
          let contr_set_view_comp_lemma2 ←
            `(@[aesop norm (rule_sets := [lens])] theorem $(freshName' "_set_view_comp2"):ident $names:ident* :
                ∀ x y v s (g: Lens' _ y) (f: Lens' _ x),
                  @view _ _ ($main_lens ∘∘ g)
                    (@set _ _ _ _ (@Composable4.comp4 Lens _ _ _ _ _ x x $other_lens f) v s)
                  = @view _ _ ($main_lens ∘∘ g) s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4
                       , $main_ident:ident, $other_ident:ident])
          let contr_set_view_comp_lemma3 ←
            `(@[aesop norm (rule_sets := [lens])] theorem $(freshName' "_set_view_comp3"):ident $names:ident* :
                ∀ y v s (g: Lens' _ y),
                  @view _ _ ($main_lens ∘∘ g)
                    (@set _ _ _ _ $other_lens v s)
                  = @view _ _ ($main_lens ∘∘ g) s := by
                  simp [view, set, Functor.map, lens', lens, Id.run, Const.get, Composable2.comp, Composable4.comp4
                       , $main_ident:ident, $other_ident:ident])
          trace[debug] "{contr_set_view_lemma}"
          trace[debug] "{contr_set_view_comp_lemma2}"
          trace[debug] "{contr_set_view_comp_lemma3}"
          elabCommand <| contr_set_view_lemma
          elabCommand <| ← `(addlensrule $(freshName' "_set_view"):ident)
          elabCommand <| contr_set_view_comp_lemma
          elabCommand <| ← `(addlensrule $(freshName' "_set_view_comp"):ident)
          --elabCommand <| contr_set_view_comp_lemma2
          --elabCommand <| contr_set_view_comp_lemma3
  | _ => throwUnsupportedSyntax

def update_Fin {a} (i' : Fin n)  (e : a) (f : Fin n → a) : Fin n → a :=
  fun i =>
    if i == i' then
      e
    else
      f i

@[aesop norm (rule_sets := [lens])]
theorem fview_view a b:
  @fview x y b a = @view x y a b := by
  simp [fview, flip]
addlensrule fview_view

@[aesop norm (rule_sets := [lens])]
theorem update_Fin_gso {a: Type} (i i' : Fin n)  (e : a) (f : Fin n → a) :
  ¬(i = i') → update_Fin i' e f i = f i := by intro h1; simp [update_Fin, h1]

@[aesop norm (rule_sets := [lens])]
theorem update_Fin_gso2 {a: Type} (i i' : Fin n)  (e : a) (f : Fin n → a) :
  ¬(i' = i) → update_Fin i' e f i = f i := by
    intro h1
    have h1 := Ne.symm h1
    aesop_lens

@[aesop norm (rule_sets := [lens])]
theorem update_Fin_gss {a: Type} (i  : Fin n)  (e : a) (f : Fin n → a) :
  update_Fin i e f i  = e := by simp [update_Fin]

def fin_at {n} (i : Fin n) : Lens' (Fin n → a) a :=
  lens' (fun a => a i) (fun a b => update_Fin i b a)
addlensunfoldrule fin_at

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gss :
  view (fin_at n) (set (fin_at n) x y) = x := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin]
addlensrule fin_at_gss

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gss_comp :
  view (fin_at n) (set (fin_at n∘∘g) x y) = set g x (view (fin_at n) y) := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,Composable2.comp,Composable4.comp4]
addlensrule fin_at_gss_comp

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gso :
  ¬ n = m → view (fin_at n) (set (fin_at m) x y) = y n := by
  intros h1; simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,h1]
addlensrule fin_at_gso

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gso2 :
  ¬ m = n → view (fin_at n) (set (fin_at m) x y) = y n := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,this]
addlensrule fin_at_gso2

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gso2_comp :
  ¬ m = n → view (fin_at n) (set (fin_at m∘∘g) x y) = y n := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,this,Composable4.comp4,Composable2.comp]
addlensrule fin_at_gso2_comp

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gso_comp :
  ¬ n = m → view (fin_at n) (set (fin_at m∘∘g) x y) = y n := by
  intros h1; simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,h1,Composable4.comp4,Composable2.comp]
addlensrule fin_at_gso_comp

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gso_app :
  ¬ n = m → (set (fin_at m) x y) n = y n := by
  intros h1; simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,h1]
addlensrule fin_at_gso_app

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gso2_app :
  ¬ m = n → (set (fin_at m) x y) n = y n := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,this]
addlensrule fin_at_gso2_app

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gso2_comp_app :
  ¬ m = n → (set (fin_at m∘∘g) x y) n = y n := by
  intros h1
  have := Ne.symm h1
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,this,Composable4.comp4,Composable2.comp]
addlensrule fin_at_gso2_comp_app

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gso_comp_app :
  ¬ n = m → (set (fin_at m∘∘g) x y) n = y n := by
  intros h1; simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,h1,Composable4.comp4,Composable2.comp]
addlensrule fin_at_gso_comp_app

@[aesop norm (rule_sets := [lens])]
theorem fin_at_apply :
  view (fin_at n) y = y n := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,Composable4.comp4,Composable2.comp]
addlensrule fin_at_apply

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gss2 :
  (set (fin_at n) x y) n = x := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin]
addlensrule fin_at_gss2

@[aesop norm (rule_sets := [lens])]
theorem fin_at_gss2_comp :
  (set (fin_at n∘∘g) x y) n = set g x (y n) := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,Composable4.comp4,Composable2.comp]
addlensrule fin_at_gss2_comp

@[aesop norm (rule_sets := [lens])]
theorem fin_at_view_comp :
  view (fin_at n∘∘g) x = view g (view (fin_at n) x) := by
  simp [fin_at,lens,lens',view,set,Functor.map,Id.run,update_Fin,Composable4.comp4,Composable2.comp]
addlensrule fin_at_view_comp

def liftA2 [Applicative F] (f: a → b → c) (x: F a) (y: F b) :=
  (f <$> x) <*> y

def traverse_list' [Applicative F] (f: a → F b) : List a → F (List b) :=
  List.foldr cons_f (pure [])
  where cons_f x ys := liftA2 List.cons (f x) ys

def traverse_list : Traversal' (List a) a :=
  fun F _ inst2 => @traverse_list' F _ _ inst2

def range (n : Nat) : List (Fin n) :=
  loop n (Nat.le_of_eq (Eq.refl n)) []
where
  loop : (y:Nat) → y <= n → List (Fin n) → List (Fin n)
  | 0,   _,  ns => ns
  | n+1, lt, ns => let ltn := Nat.lt_of_succ_le lt; loop n (Nat.le_of_lt ltn) ({val := n, isLt := ltn}::ns)

def traverse_Fin' [Inhabited b] [Applicative F] (f: a → F b) (l: Fin n → a): F (Fin n → b) :=
  List.foldr cons_r (pure (fun _ => default)) (range n)
  where cons_r x ys := liftA2 (update_Fin x) (f (l x)) ys

def traverse_Fin'' [Inhabited b] [Applicative F] (f: Nat → a → F b) (l: Fin n → a): F (Fin n → b) :=
  List.foldr cons_r (pure (fun _ => default)) (range n)
  where cons_r x ys := liftA2 (update_Fin x) (f x (l x)) ys

def traverse_Fin {n} {a} [Inhabited a] : Traversal' (Fin n → a) a :=
  fun _ => traverse_Fin'

@[simp]
def set_Fin {n} {a} [Inhabited a] : ASetter' (Fin n → a) a := @traverse_Fin n a _

end Leanses

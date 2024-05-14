import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Simp
import Lean.Meta.Tactic.Simp.SimpTheorems

import Leanses.Options

namespace Leanses

open Lean.Parser.Tactic in
syntax (name := simpLens) "simp_lens" (config)? (discharger)? 
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

open Lean.Parser.Tactic in
syntax (name := unfoldLens) "unfold_lens" (config)? (discharger)? 
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

set_option trace.debug true

open Lean Meta Simp Core in
def SimpTheoremsArray.addConst (thmsArray : SimpTheoremsArray) (id : Name) : MetaM SimpTheoremsArray :=
  if thmsArray.isEmpty then
    let thms : SimpTheorems := {}
    return #[ (← thms.addConst id) ]
  else
    thmsArray.modifyM 0 fun thms => thms.addConst id

open Lean Meta Simp Core in
def getSimpTheorems : MetaM SimpTheorems := do
  let rlist := lens_ext.getState (← getEnv)
  let mut s : SimpTheorems := {}
  for name in rlist do
    s ← s.addConst name
  return s

open Lean Meta Simp Core in
def getUnfoldTheorems : MetaM SimpTheorems := do
  let rlist := lens_ext_unfold.getState (← getEnv)
  let mut s : SimpTheorems := {}
  for name in rlist do
    s ← s.addConst name
  return s

open Lean.Elab.Tactic in
@[tactic Leanses.simpLens] 
def evalSimpLens : Tactic := fun stx => withMainContext do
  match stx with 
  | Lean.Syntax.node si st _ =>
    let nstx_arr := Array.mkArray6 stx[0] stx[1] stx[2] Lean.Syntax.missing stx[3] stx[4]
    let nstx := Lean.Syntax.node si st nstx_arr
    let { ctx, simprocs, dischargeWrapper } ← mkSimpContext nstx (simpTheorems := pure (← getSimpTheorems)) (eraseLocal := false)
    let usedSimps ← dischargeWrapper.with fun discharge? =>
      simpLocation ctx simprocs discharge? (expandOptLocation stx[4])
    if tactic.simp.trace.get (← Lean.getOptions) then
        traceSimpCall stx usedSimps
  | _ => panic! "Wrong simp_lens syntax"

open Lean.Elab.Tactic in
@[tactic Leanses.unfoldLens] 
def evalUnfoldLens : Tactic := fun stx => withMainContext do
  match stx with 
  | Lean.Syntax.node si st _ =>
    let nstx_arr := Array.mkArray6 stx[0] stx[1] stx[2] Lean.Syntax.missing stx[3] stx[4]
    let nstx := Lean.Syntax.node si st nstx_arr
    let { ctx, simprocs, dischargeWrapper } ← mkSimpContext nstx (simpTheorems := pure (← getUnfoldTheorems)) (eraseLocal := false)
    let usedSimps ← dischargeWrapper.with fun discharge? =>
      simpLocation ctx simprocs discharge? (expandOptLocation stx[4])
    if tactic.simp.trace.get (← Lean.getOptions) then
        traceSimpCall stx usedSimps
  | _ => panic! "Wrong simp_lens syntax"

example : ∀ A (x y:A) (P: A → Prop), x = y -> P x -> P y := by
  intros; unfold_lens [*] at *; assumption

end Leanses

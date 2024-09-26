/-
Copyright (c) 2024 Yann Herklotz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

open Lean Meta Elab Command

register_option pp.hideLensUpdates : Bool := {
  defValue := False
  descr := "Hide the lense updates"
}

register_option pp.zeroLensUpdates : Bool := {
  defValue := False
  descr := "Hide the lense updates"
}

initialize Lean.registerTraceClass `Leanses.traceNames
initialize Lean.registerTraceClass `Leanses.debug
initialize Lean.registerTraceClass `Leanses.impl

abbrev RuleSet := Array Name

abbrev RuleName := Name

def extensionDescr (n:Name) :
    SimpleScopedEnvExtension.Descr RuleName RuleSet where
  name := n
  addEntry rs r := rs.push r
  initial := ∅

initialize lens_ext : SimpleScopedEnvExtension RuleName RuleSet 
  ← registerSimpleScopedEnvExtension (extensionDescr (Name.mkSimple "local_lens"))

initialize lens_ext_unfold : SimpleScopedEnvExtension RuleName RuleSet 
  ← registerSimpleScopedEnvExtension (extensionDescr (Name.mkSimple "local_lens_unfold"))

syntax (name := addLensRule) "addlensrule" ident : command
syntax (name := addLensUnfoldRule) "addlensunfoldrule" ident : command

@[command_elab addLensRule] 
def addLensRuleHandler : CommandElab
  | `(addlensrule $i) => do 
    let name ← resolveGlobalConstNoOverload i
    lens_ext.add name AttributeKind.global
  | _ => throwUnsupportedSyntax

@[command_elab addLensUnfoldRule] 
def addLensUnfoldRuleHandler : CommandElab
  | `(addlensunfoldrule $i) => do 
    let name ← resolveGlobalConstNoOverload i
    lens_ext_unfold.add name AttributeKind.global
  | _ => throwUnsupportedSyntax

register_simp_attr lens_set
register_simp_attr ulens_set
register_simp_attr ulens_unfold

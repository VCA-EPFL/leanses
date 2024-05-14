import Lean
import Aesop

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

declare_aesop_rule_sets [lens]

abbrev RuleSet := Array Name

abbrev RuleName := Name

def extensionDescr (n:String) :
    SimpleScopedEnvExtension.Descr RuleName RuleSet where
  name := n
  addEntry rs r := rs.push r
  initial := ∅

initialize lens_ext : SimpleScopedEnvExtension RuleName RuleSet 
  ← registerSimpleScopedEnvExtension (extensionDescr "local_lens")

initialize lens_ext_unfold : SimpleScopedEnvExtension RuleName RuleSet 
  ← registerSimpleScopedEnvExtension (extensionDescr "local_lens_unfold")

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

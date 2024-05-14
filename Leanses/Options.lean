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

def extensionDescr :
    SimpleScopedEnvExtension.Descr RuleName RuleSet where
  name := "local_lens"
  addEntry rs r := rs.push r
  initial := ∅

initialize lens_ext : SimpleScopedEnvExtension RuleName RuleSet 
  ← registerSimpleScopedEnvExtension extensionDescr

syntax (name := addLensRule) "addlensrule" ident : command

@[command_elab addLensRule] 
def addLensRuleHandler : CommandElab
  | `(addlensrule $i) => do 
    let name ← resolveGlobalConstNoOverload i
    lens_ext.add name AttributeKind.global
  | _ => throwUnsupportedSyntax

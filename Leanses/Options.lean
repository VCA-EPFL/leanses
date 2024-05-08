import Lean
import Aesop

register_option pp.hideLensUpdates : Bool := {
  defValue := False
  descr := "Hide the lense updates"
}

register_option pp.zeroLensUpdates : Bool := {
  defValue := False
  descr := "Hide the lense updates"
}

initialize Lean.registerTraceClass `Leanses.traceNames

declare_aesop_rule_sets [lens]

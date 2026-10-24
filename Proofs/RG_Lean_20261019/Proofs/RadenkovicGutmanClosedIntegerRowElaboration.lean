/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanClosedIntegerDataElaboration

syntax (name := rgClosedIntegerRowLiteral) "rg_closed_integer_row% " term : term

/-- Only closed integer rows are computed; identities and signs need kernel proofs. -/
@[term_elab rgClosedIntegerRowLiteral]
unsafe def elabRGClosedIntegerRowLiteral : Lean.Elab.Term.TermElab := fun stx _ => do
  let `(rg_closed_integer_row% $t) := stx | Lean.Elab.throwUnsupportedSyntax
  let ty ← Lean.Elab.Term.elabType (← `(List (List Int)))
  let e ← Lean.Elab.Term.elabTermEnsuringType t ty
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  if e.hasMVar then throwError "Integer row data must be closed"
  let env ← Lean.getEnv
  let e ← Lean.Meta.deltaExpand e (Lean.isNoncomputable env ·)
  let value ← Lean.Meta.evalExpr (List (List Int)) ty e
  return Lean.toExpr value

namespace Gebendorfer.RadenkovicGutman.ClosedIntegerRowElaboration
noncomputable def input : List (List Int) := [[1,2],[3,4]]
noncomputable def output : List (List Int) := rg_closed_integer_row% (input++input)
theorem checked : output=input++input := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.ClosedIntegerRowElaboration

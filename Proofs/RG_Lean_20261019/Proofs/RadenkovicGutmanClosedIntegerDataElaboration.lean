/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerDataElaboration
import Lean.Meta.Tactic.Delta
import Lean.Compiler.NoncomputableAttr

syntax (name := rgClosedIntegerDataLiteral) "rg_closed_integer_data% " term : term

/-- Untrusted closed integer data only; all identities and signs require kernel proofs. -/
@[term_elab rgClosedIntegerDataLiteral]
unsafe def elabRGClosedIntegerDataLiteral : Lean.Elab.Term.TermElab := fun stx _ => do
  let `(rg_closed_integer_data% $t) := stx | Lean.Elab.throwUnsupportedSyntax
  let ty ← Lean.Elab.Term.elabType (← `(List (List (List Int))))
  let e ← Lean.Elab.Term.elabTermEnsuringType t ty
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  if e.hasMVar then throwError "Integer certificate data must be closed"
  let env ← Lean.getEnv
  let e ← Lean.Meta.deltaExpand e (Lean.isNoncomputable env ·)
  let value ← Lean.Meta.evalExpr (List (List (List Int))) ty e
  return Lean.toExpr value

namespace Gebendorfer.RadenkovicGutman.ClosedIntegerDataElaboration
noncomputable def input : NestedInteger.Poly 3 := [[[1,2],[3]],[[4],[5]]]
noncomputable def output : NestedInteger.Poly 3 :=
  rg_closed_integer_data% (NestedInteger.add input input)
theorem checked : output=NestedInteger.add input input := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.ClosedIntegerDataElaboration

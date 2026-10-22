/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerLiteral
import Lean.Meta.Eval

syntax (name := rgIntegerDataLiteral) "rg_integer_data% " term : term

/-- This untrusted computation returns integer data only. Every use below still
requires a kernel-checked equality to the defining arithmetic expression and
kernel-checked Bernstein signs. No proposition is evaluated to produce a proof. -/
@[term_elab rgIntegerDataLiteral]
unsafe def elabRGIntegerDataLiteral : Lean.Elab.Term.TermElab := fun stx _ => do
  let `(rg_integer_data% $t) := stx | Lean.Elab.throwUnsupportedSyntax
  let ty ← Lean.Elab.Term.elabType (← `(List (List (List Int))))
  let e ← Lean.Elab.Term.elabTermEnsuringType t ty
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  if e.hasMVar then
    throwError "Integer certificate data must be closed"
  let value ← Lean.Meta.evalExpr (List (List (List Int))) ty e
  return Lean.toExpr value

namespace Gebendorfer.RadenkovicGutman.IntegerDataElaboration

/-- A prepared literal has no mathematical force without this exact equality. -/
theorem checked_identity (computed literal : NestedInteger.Poly 3)
    (h : computed=literal) : literal=computed := h.symm

#print axioms checked_identity
#print axioms IntegerLiteral.accepts_materialized
end Gebendorfer.RadenkovicGutman.IntegerDataElaboration

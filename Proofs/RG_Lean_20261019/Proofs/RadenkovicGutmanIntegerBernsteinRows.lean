/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerDataElaboration

syntax (name := rgIntegerRowLiteral) "rg_integer_row% " term : term

/-- Only integer data is evaluated. A row still needs a kernel checked identity
and a kernel checked sign certificate before it can be used below. -/
@[term_elab rgIntegerRowLiteral]
unsafe def elabRGIntegerRowLiteral : Lean.Elab.Term.TermElab := fun stx _ => do
  let `(rg_integer_row% $t) := stx | Lean.Elab.throwUnsupportedSyntax
  let ty ← Lean.Elab.Term.elabType (← `(List (List Int)))
  let e ← Lean.Elab.Term.elabTermEnsuringType t ty
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  if e.hasMVar then
    throwError "Integer row data must be closed"
  let value ← Lean.Meta.evalExpr (List (List Int)) ty e
  return Lean.toExpr value

namespace Gebendorfer.RadenkovicGutman.IntegerBernsteinRows
set_option maxHeartbeats 0

/-- Check each outer coefficient once, then reuse its checked lower-dimensional
Bernstein certificate. The conclusion is the original exact boolean checker. -/
theorem checked {n : ℕ} (d : Fin (n+1) → ℕ) (p : NestedInteger.Poly (n+1))
    (rows : Fin (d 0+1) → NestedInteger.Poly n)
    (hp : p.length ≤ d 0+1)
    (hr : ∀ j, rows j=NestedInteger.coefficientFrom (d 0) j.val 0 p)
    (hs : ∀ j, NestedInteger.bernsteinCheck n (fun i => d i.succ) (rows j)=true) :
    NestedInteger.bernsteinCheck (n+1) d p=true := by
  apply decide_eq_true
  refine ⟨hp,?_⟩
  intro j
  rw [← hr j]
  exact hs j

#print axioms checked
end Gebendorfer.RadenkovicGutman.IntegerBernsteinRows

import FormalConjectures.OEIS.«381054»
import FormalConjectures.WrittenOnTheWallII.GraphConjecture367
import Lean.Util.CollectAxioms

/-! Axiom audits for exactly the two completed conjecture refutations. -/

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``OeisA381054.a_family_3_11, ``OeisA381054.not_family_conjecture,
      ``WrittenOnTheWallII.GraphConjecture367.not_tied_mode_statement] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {target}: {ax}"
    Lean.logInfo m!"Checked {target}: {axioms}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "Placeholder negative control was not rejected"
  Lean.logInfo "INTAKE_EXACT_CERTIFICATE_PASS"

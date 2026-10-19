import Proofs.WOWII340Proof
import Lean.Util.CollectAxioms

example : ¬ WrittenOnTheWallII.GraphConjecture340.conjecture340Statement :=
  WOWII340Proof.conjecture340

run_cmd do
  let target := ``WOWII340Proof.conjecture340
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms target
  for ax in axioms do
    unless allowed.contains ax do
      Lean.throwError m!"Unexpected axiom in WOWII 340 refutation: {ax}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "The placeholder negative control was not rejected"
  Lean.logInfo m!"WOWII340_EXACT_CERTIFICATE_PASS: {axioms}"

#print axioms WOWII340Proof.conjecture340

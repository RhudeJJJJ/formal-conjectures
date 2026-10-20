import Proofs.WOWII405407Proof
import Lean.Util.CollectAxioms

/-! Exact target checks and a transitive axiom whitelist for both certificates. -/

open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture404To407

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    (horder : 2 < Fintype.card V) :
    privateExternalNeighborCount G (criticalUnion G) ≤
      2 * (G.induce ((univ \ leaves G : Finset V) : Set V)).indepNum :=
  WOWII405407Proof.conjecture405 G hT horder

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    (horder : 2 < Fintype.card V) :
    privateExternalNeighborCount G (criticalUnion G) ≤ 2 * G.pathCoverNumber :=
  WOWII405407Proof.conjecture407 G hT horder

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``WOWII405407Proof.conjecture405, ``WOWII405407Proof.conjecture407] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {target}: {ax}"
    Lean.logInfo m!"EXACT_CERTIFICATE_PASS {target}: {axioms}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "Placeholder negative control must fail the whitelist"
  Lean.logInfo "PLACEHOLDER_NEGATIVE_CONTROL_PASS"

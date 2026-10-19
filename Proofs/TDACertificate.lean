import Proofs.TDAFull
import Lean.Util.CollectAxioms

/-! Fail-closed check of the exact target and its full transitive axiom closure. -/

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 ≤ Fintype.card V) :
    G.totalDominationNumber ≤ G.annihilationNumber + 1 :=
  TotalDominationAnnihilationProof.total_domination_annihilation G hG horder

run_cmd do
  let target := ``TotalDominationAnnihilationProof.total_domination_annihilation
  let env ← Lean.getEnv
  unless (env.find? target).isSome do
    Lean.throwError "Exact universal theorem is missing"
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms target
  for ax in axioms do
    unless allowed.contains ax do
      Lean.throwError m!"Unexpected axiom in exact universal theorem: {ax}"
  -- This existing open equivalence is a negative control, never a proof input.
  let negative ← Lean.collectAxioms ``SimpleGraph.annihilationNumberEq
  unless negative.contains ``sorryAx do
    Lean.throwError "Negative-control assumption changed; review the axiom guard"
  Lean.logInfo m!"TDA_EXACT_CERTIFICATE_PASS: {axioms}"

#print axioms TotalDominationAnnihilationProof.total_domination_annihilation

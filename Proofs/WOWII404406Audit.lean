import Proofs.WOWII404406Proof
import Lean.Util.CollectAxioms

/-! Exact statement checks for the remaining two tree inequalities. -/
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture404To407

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    (horder : 2 < Fintype.card V) :
    (privateExternalNeighborCount G (criticalUnion G) : ℤ) ≤
      2 * ((supports G).card - (1 : ℤ)) :=
  WOWII404406Proof.conjecture404 G hT horder

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    (horder : 2 < Fintype.card V) :
    (privateExternalNeighborCount G (criticalUnion G) : ℤ) ≤
      (privateExternalNeighborCount G (univ \ leaves G) : ℤ) - 2 :=
  WOWII404406Proof.conjecture406 G hT horder

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``WOWII404406Proof.conjecture404, ``WOWII404406Proof.conjecture406,
      ``WOWII405407Proof.conjecture405, ``WOWII405407Proof.conjecture407] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {target}: {ax}"
    Lean.logInfo m!"EXACT_CERTIFICATE_PASS {target}: {axioms}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "Placeholder negative control must fail the whitelist"
  Lean.logInfo "PLACEHOLDER_NEGATIVE_CONTROL_PASS"

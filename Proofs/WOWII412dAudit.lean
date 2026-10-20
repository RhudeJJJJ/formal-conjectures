import Proofs.WOWII412dProof
import Proofs.WOWII412dForest
import Lean.Util.CollectAxioms

/-! Exact submitted targets and the transitive axiom whitelist. -/
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture412d

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hni : ∀ v, ∃ w, G.Adj v w) :
    G.totalDominationNumber ≤ (corona G).card ∧ corona G = criticalUnion G :=
  WOWII412dProof.conjecture412d_isolate_free G hb hni

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (hb : G.IsBipartite)
    (horder : 2 < Fintype.card V) :
    G.totalDominationNumber ≤ (criticalUnion G).card :=
  WOWII412dProof.conjecture412d G hG hb horder

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``StrictHallForest.exists_forest_selection,
      ``StrictHallForest.exists_covers_on, ``StrictHallForest.exists_incidence_cover,
      ``WOWII412dCore.exists_core_forest, ``WOWII412dCore.exists_core_cover,
      ``WOWII412dProof.conjecture412d_isolate_free, ``WOWII412dProof.conjecture412d] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {target}: {ax}"
    Lean.logInfo m!"EXACT_CERTIFICATE_PASS {target}: {axioms}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "Placeholder negative control must fail the whitelist"
  Lean.logInfo "PLACEHOLDER_NEGATIVE_CONTROL_PASS"

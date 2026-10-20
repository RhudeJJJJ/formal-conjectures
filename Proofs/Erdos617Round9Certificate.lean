import Proofs.Erdos617AffineProof
import Proofs.Erdos617ThreeProof
import Lean.Util.CollectAxioms

/-! Exact-target bridges and fail-closed axiom audits for two classical Erdős 617 results. -/

example (r : ℕ) (hr : r ≥ 3) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 3^2 + 1) (coloring : Sym2 V → Fin 3) :
    ∃ (S : Finset V) (k : Fin 3), S.card = 3 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u,v) ≠ k :=
  Erdos617ThreeProof.r_eq_3 r hr hV coloring

example :
    {r : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V), Fintype.card V = r^2 ∧
      ∃ (coloring : Sym2 V → Fin r), ∀ S : Finset V, S.card = r + 1 →
        ∀ k : Fin r, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u,v) = k}.Infinite :=
  Erdos617AffineProof.r2

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``Erdos617ThreeProof.r_eq_3, ``Erdos617AffineProof.r2] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {target}: {ax}"
    Lean.logInfo m!"Checked {target}: {axioms}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "Placeholder negative control was not rejected"
  Lean.logInfo "ERDOS617_R3_R2_EXACT_CERTIFICATE_PASS"

#print axioms Erdos617ThreeProof.r_eq_3
#print axioms Erdos617AffineProof.r2

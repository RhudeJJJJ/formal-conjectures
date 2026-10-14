/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
A negative model control: the corresponding r=2 shape is false.
The witness is a five-cycle and its complement, with kernel-only finite decision.
-/
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic

namespace Gebendorfer.Erdos617Boundary

def twoColour (e : Sym2 (Fin 5)) : Fin 2 :=
  if e ∈ (SimpleGraph.cycleGraph 5).edgeFinset then 0 else 1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem every_three_sees_both :
    ∀ S : Finset (Fin 5), S.card = 3 → ∀ k : Fin 2,
      ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ twoColour s(u, v) = k := by decide

theorem r_two_shape_false :
    ¬(∀ c : Sym2 (Fin 5) → Fin 2,
      ∃ (S : Finset (Fin 5)) (k : Fin 2), S.card = 3 ∧
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k) := by
  intro h
  obtain ⟨S, k, hS, hmiss⟩ := h twoColour
  obtain ⟨u, hu, v, hv, huv, hc⟩ := every_three_sees_both S hS k
  exact hmiss u hu v hv huv hc

#print axioms every_three_sees_both
#print axioms r_two_shape_false

end Gebendorfer.Erdos617Boundary

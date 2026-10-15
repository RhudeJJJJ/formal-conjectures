import Proofs.WOWII252Proof
import Mathlib.Combinatorics.SimpleGraph.Girth

/-! Definition audit: least modal degree over all natural degrees, and
exclusion of arbitrary four-cycle walks, including cycles with chords. -/
namespace WOWII252Audit
open WOWII252Proof SimpleGraph Finset WOWIIModal
lemma witness_frequencies : ∀ d : Fin 30, frequency witness d =
    if d.val = 1 then 4 else if d.val ∈ ({2,3,4,5} : Finset ℕ) then 5
    else if d.val = 7 then 6 else 0 := by
  unfold frequency
  simp_rw [degree_eq]
  decide

lemma damaged_selection : ¬ witness.IsTotalDominating ({0,1,2,3,4} : Set (Fin 30)) := by
  intro h
  obtain ⟨w, hw, ha⟩ := h 28
  have he : ¬ ∃ w : Fin 30, w ∈ ({0,1,2,3,4} : Finset (Fin 30)) ∧ witness.Adj 28 w := by decide
  exact he ⟨w, by simpa using hw, ha⟩

#print axioms modeMin_spec
#print axioms no_four_cycle
#print axioms witness_frequencies
#print axioms damaged_selection
end WOWII252Audit

import Proofs.WOWII253Proof

/-! Degree-frequency and negative-control audit for WOWII 253.
The common definitions also prove the global least-mode specification. -/
namespace WOWII253Audit
open WOWII253Proof SimpleGraph Finset WOWIIModal
lemma witness_frequencies : ∀ d : Fin 30, frequency witness d =
    if d.val ∈ ({1,2,3,4} : Finset ℕ) then 5 else if d.val = 5 then 4
    else if d.val = 6 then 6 else 0 := by
  unfold frequency
  simp_rw [degree_eq]
  decide

lemma damaged_selection : ¬ witness.IsTotalDominating ({0,1,2,3,4} : Set (Fin 30)) := by
  intro h
  obtain ⟨w, hw, ha⟩ := h 28
  have he : ¬ ∃ w : Fin 30, w ∈ ({0,1,2,3,4} : Finset (Fin 30)) ∧ witness.Adj 28 w := by decide
  exact he ⟨w, by simpa using hw, ha⟩

#print axioms witness_frequencies
#print axioms WOWII253Proof.witness_egirth_eq
#print axioms damaged_selection
end WOWII253Audit

import Proofs.BurghartAlgebra
import Proofs.BurghartCompute

/-! # BurghartFull
Exact-definition certificate for Burghart Conjecture 20.
All finite computations are checked by the Lean kernel. -/

namespace BurghartCertificate

theorem polynomial_eq : Burghart.MPolynomial.mPolynomial T1 0 = Burghart.MPolynomial.mPolynomial T2 0 := by
  rw [m_eq_rep T1 route1 route1_ok T1_tree admissiblesFast1 admissiblesFast1_eq,
    m_eq_rep T2 route2 route2_ok T2_tree admissiblesFast2 admissiblesFast2_eq,
    distances1_eq, distances2_eq, equal_reps_fast]

theorem full_conjecture20 : ¬ ∀ (n m : ℕ) (T : SimpleGraph (Fin n))
    (U : SimpleGraph (Fin m)) (r : Fin n) (s : Fin m), T.IsTree → U.IsTree →
      Burghart.MPolynomial.mPolynomial T r = Burghart.MPolynomial.mPolynomial U s →
        ∃ e : T ≃g U, e r = s := by
  intro h
  obtain ⟨e,he⟩ := h 28 28 T1 T2 0 0 T1_tree T2_tree polynomial_eq
  exact no_rooted_iso e he

#print axioms polynomial_eq
#print axioms full_conjecture20
end BurghartCertificate

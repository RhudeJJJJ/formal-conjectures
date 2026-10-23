import Proofs.BurghartVectors
/-! # Full finite polynomial equality for the two order-28 witnesses -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem normalized_equal : norm3 (polyVec T1 distances1 admissiblesFast1) =
    norm3 (polyVec T2 distances2 admissiblesFast2) := by
  decide +kernel
#print axioms normalized_equal

theorem polynomial_eq : Burghart.MPolynomial.mPolynomial T1 0 = Burghart.MPolynomial.mPolynomial T2 0 := by
  have h1 := m_eq_vec T1 route1 route1_ok T1_tree admissiblesFast1 admissiblesFast1_eq
  have h2 := m_eq_vec T2 route2 route2_ok T2_tree admissiblesFast2 admissiblesFast2_eq
  rw [distances1_eq] at h1
  rw [distances2_eq] at h2
  calc
    Burghart.MPolynomial.mPolynomial T1 0 = eval3 (norm3 (polyVec T1 distances1 admissiblesFast1)) :=
      h1.trans (eval_norm3 _).symm
    _ = eval3 (norm3 (polyVec T2 distances2 admissiblesFast2)) := congrArg eval3 normalized_equal
    _ = Burghart.MPolynomial.mPolynomial T2 0 := (eval_norm3 _).trans h2.symm
#print axioms polynomial_eq
end BurghartLists

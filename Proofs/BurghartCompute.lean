import Proofs.BurghartFringe1
import Proofs.BurghartFringe2
/-! # Full trivariate polynomial equality from complete fringe certificates -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem table_normalized_equal : norm3 (polyOf T1 admissiblesFast1 fringeTable1) =
    norm3 (polyOf T2 admissiblesFast2 fringeTable2) := by decide +kernel
#print axioms table_normalized_equal

theorem polynomial_eq : Burghart.MPolynomial.mPolynomial T1 0 = Burghart.MPolynomial.mPolynomial T2 0 := by
  have h1 := m_eq_table T1 route1 route1_ok T1_tree admissiblesFast1 admissiblesFast1_eq distances1 distances1_eq fringeTable1 fringeTable1_correct
  have h2 := m_eq_table T2 route2 route2_ok T2_tree admissiblesFast2 admissiblesFast2_eq distances2 distances2_eq fringeTable2 fringeTable2_correct
  exact h1.trans ((eval_norm3 _).symm.trans ((congrArg eval3 table_normalized_equal).trans ((eval_norm3 _).trans h2.symm)))
#print axioms polynomial_eq
end BurghartLists

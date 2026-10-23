import Proofs.BurghartRep
import Proofs.BurghartIdeals

/-! # BurghartCompute
Exact-definition certificate for Burghart Conjecture 20.
All finite computations are checked by the Lean kernel. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BurghartCertificate
theorem admissibles1_card : admissibles1.card = 325 := by decide +kernel
theorem admissibles2_card : admissibles2.card = 325 := by decide +kernel

theorem equal_reps : repOf T1 distances1 admissibles1 = repOf T2 distances2 admissibles2 := by
  decide +kernel
#print axioms equal_reps
end BurghartCertificate

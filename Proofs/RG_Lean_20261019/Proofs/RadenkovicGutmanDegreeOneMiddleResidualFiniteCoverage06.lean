/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage06Block000
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage06Block001
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered6 : decide (∀ i : Fin (RootedCatalogueData.catalogue 6).length,
    ∀ p q : Fin 5, eligible 6 i.val p.val q.val=true →
      (⟨6,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 48 at hi
  by_cases h0 : i.val < 32
  · exact CoreCoverage.range_sound 6 0 32 CoreCoverage.checked6b000 i.val p q (by omega) (by omega) he
  exact CoreCoverage.range_sound 6 32 16 CoreCoverage.checked6b001 i.val p q (by omega) (by omega) he
#print axioms covered6
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys

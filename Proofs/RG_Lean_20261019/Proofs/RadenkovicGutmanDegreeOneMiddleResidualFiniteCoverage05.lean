/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage05Block000
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered5 : decide (∀ i : Fin (RootedCatalogueData.catalogue 5).length,
    ∀ p q : Fin 5, eligible 5 i.val p.val q.val=true →
      (⟨5,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 20 at hi
  exact CoreCoverage.range_sound 5 0 20 CoreCoverage.checked5b000 i.val p q (by omega) (by omega) he
#print axioms covered5
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys

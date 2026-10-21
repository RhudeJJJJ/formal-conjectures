/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage03Block000
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered3 : decide (∀ i : Fin (RootedCatalogueData.catalogue 3).length,
    ∀ p q : Fin 5, eligible 3 i.val p.val q.val=true →
      (⟨3,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 4 at hi
  exact CoreCoverage.range_sound 3 0 4 CoreCoverage.checked3b000 i.val p q (by omega) (by omega) he
#print axioms covered3
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys

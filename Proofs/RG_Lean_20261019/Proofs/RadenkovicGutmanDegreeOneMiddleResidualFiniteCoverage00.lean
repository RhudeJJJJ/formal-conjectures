/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage00Block000
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered0 : decide (∀ i : Fin (RootedCatalogueData.catalogue 0).length,
    ∀ p q : Fin 5, eligible 0 i.val p.val q.val=true →
      (⟨0,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 1 at hi
  exact CoreCoverage.range_sound 0 0 1 CoreCoverage.checked0b000 i.val p q (by omega) (by omega) he
#print axioms covered0
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys

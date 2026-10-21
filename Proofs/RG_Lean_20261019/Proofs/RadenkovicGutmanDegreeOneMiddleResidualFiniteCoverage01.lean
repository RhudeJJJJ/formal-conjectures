/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage01Block000
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered1 : decide (∀ i : Fin (RootedCatalogueData.catalogue 1).length,
    ∀ p q : Fin 5, eligible 1 i.val p.val q.val=true →
      (⟨1,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 1 at hi
  exact CoreCoverage.range_sound 1 0 1 CoreCoverage.checked1b000 i.val p q (by omega) (by omega) he
#print axioms covered1
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys

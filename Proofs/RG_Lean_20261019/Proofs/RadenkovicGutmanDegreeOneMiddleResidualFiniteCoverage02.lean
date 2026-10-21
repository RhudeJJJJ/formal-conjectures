/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage02Block000
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered2 : decide (∀ i : Fin (RootedCatalogueData.catalogue 2).length,
    ∀ p q : Fin 5, eligible 2 i.val p.val q.val=true →
      (⟨2,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 2 at hi
  exact CoreCoverage.range_sound 2 0 2 CoreCoverage.checked2b000 i.val p q (by omega) (by omega) he
#print axioms covered2
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys

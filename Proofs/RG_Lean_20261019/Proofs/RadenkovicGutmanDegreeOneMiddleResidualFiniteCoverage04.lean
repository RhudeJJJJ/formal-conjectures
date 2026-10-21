/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage04Block000
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered4 : decide (∀ i : Fin (RootedCatalogueData.catalogue 4).length,
    ∀ p q : Fin 5, eligible 4 i.val p.val q.val=true →
      (⟨4,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 9 at hi
  exact CoreCoverage.range_sound 4 0 9 CoreCoverage.checked4b000 i.val p q (by omega) (by omega) he
#print axioms covered4
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys

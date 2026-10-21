/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage07Block000
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage07Block001
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage07Block002
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage07Block003
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered7 : decide (∀ i : Fin (RootedCatalogueData.catalogue 7).length,
    ∀ p q : Fin 5, eligible 7 i.val p.val q.val=true →
      (⟨7,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 115 at hi
  by_cases h0 : i.val < 32
  · exact CoreCoverage.range_sound 7 0 32 CoreCoverage.checked7b000 i.val p q (by omega) (by omega) he
  by_cases h1 : i.val < 64
  · exact CoreCoverage.range_sound 7 32 32 CoreCoverage.checked7b001 i.val p q (by omega) (by omega) he
  by_cases h2 : i.val < 96
  · exact CoreCoverage.range_sound 7 64 32 CoreCoverage.checked7b002 i.val p q (by omega) (by omega) he
  exact CoreCoverage.range_sound 7 96 19 CoreCoverage.checked7b003 i.val p q (by omega) (by omega) he
#print axioms covered7
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys

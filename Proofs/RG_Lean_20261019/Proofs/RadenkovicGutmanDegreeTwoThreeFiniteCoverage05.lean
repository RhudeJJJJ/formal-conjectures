/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage05Block000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage05Block001
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage05Block002
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered5 : decide (∀ i : Fin (RootedCatalogueData.catalogue 5).length,
    ∀ p q : Fin 13, eligible 5 i.val p.val q.val=true →
      (⟨5,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 20 at hi
  by_cases h0 : i.val < 8
  · exact CoreCoverage.range_sound 5 0 8 CoreCoverage.checked5b000 i.val p q (by omega) (by omega) he
  ·
    by_cases h1 : i.val < 16
    · exact CoreCoverage.range_sound 5 8 8 CoreCoverage.checked5b001 i.val p q (by omega) (by omega) he
    ·
      exact CoreCoverage.range_sound 5 16 4 CoreCoverage.checked5b002 i.val p q (by omega) (by omega) he
#print axioms covered5
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys

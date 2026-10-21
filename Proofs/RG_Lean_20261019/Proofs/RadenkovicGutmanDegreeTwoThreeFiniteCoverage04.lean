/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage04Block000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage04Block001
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered4 : decide (∀ i : Fin (RootedCatalogueData.catalogue 4).length,
    ∀ p q : Fin 13, eligible 4 i.val p.val q.val=true →
      (⟨4,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 9 at hi
  by_cases h0 : i.val < 8
  · exact CoreCoverage.range_sound 4 0 8 CoreCoverage.checked4b000 i.val p q (by omega) (by omega) he
  ·
    exact CoreCoverage.range_sound 4 8 1 CoreCoverage.checked4b001 i.val p q (by omega) (by omega) he
#print axioms covered4
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys

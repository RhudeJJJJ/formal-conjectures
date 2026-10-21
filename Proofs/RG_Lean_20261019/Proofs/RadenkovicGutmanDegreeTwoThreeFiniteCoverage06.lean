/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage06Block000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage06Block001
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage06Block002
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage06Block003
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage06Block004
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage06Block005
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered6 : decide (∀ i : Fin (RootedCatalogueData.catalogue 6).length,
    ∀ p q : Fin 13, eligible 6 i.val p.val q.val=true →
      (⟨6,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 48 at hi
  by_cases h0 : i.val < 8
  · exact CoreCoverage.range_sound 6 0 8 CoreCoverage.checked6b000 i.val p q (by omega) (by omega) he
  ·
    by_cases h1 : i.val < 16
    · exact CoreCoverage.range_sound 6 8 8 CoreCoverage.checked6b001 i.val p q (by omega) (by omega) he
    ·
      by_cases h2 : i.val < 24
      · exact CoreCoverage.range_sound 6 16 8 CoreCoverage.checked6b002 i.val p q (by omega) (by omega) he
      ·
        by_cases h3 : i.val < 32
        · exact CoreCoverage.range_sound 6 24 8 CoreCoverage.checked6b003 i.val p q (by omega) (by omega) he
        ·
          by_cases h4 : i.val < 40
          · exact CoreCoverage.range_sound 6 32 8 CoreCoverage.checked6b004 i.val p q (by omega) (by omega) he
          ·
            exact CoreCoverage.range_sound 6 40 8 CoreCoverage.checked6b005 i.val p q (by omega) (by omega) he
#print axioms covered6
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys

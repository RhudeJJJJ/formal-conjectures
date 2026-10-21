/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeyLookup
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem indexedChecked7 : coveredIndexed 7 0 (RootedCatalogueData.catalogue 7).length=true := by decide +kernel
theorem covered7 : decide (∀ i : Fin (RootedCatalogueData.catalogue 7).length,
    ∀ p q : Fin 13, eligible 7 i.val p.val q.val=true →
      (⟨7,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  exact indexed_range_sound 7 0 _ indexedChecked7 i.val p q (by omega) i.isLt he
#print axioms indexedChecked7
#print axioms covered7
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys

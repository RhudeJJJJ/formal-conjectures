/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeyLookup
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem indexedChecked2 : coveredIndexed 2 0 (RootedCatalogueData.catalogue 2).length=true := by decide +kernel
theorem covered2 : decide (∀ i : Fin (RootedCatalogueData.catalogue 2).length,
    ∀ p q : Fin 13, eligible 2 i.val p.val q.val=true →
      (⟨2,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  exact indexed_range_sound 2 0 _ indexedChecked2 i.val p q (by omega) i.isLt he
#print axioms indexedChecked2
#print axioms covered2
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys

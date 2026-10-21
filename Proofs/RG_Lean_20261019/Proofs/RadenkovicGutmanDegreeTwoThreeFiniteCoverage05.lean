/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered5 : decide (∀ i : Fin (RootedCatalogueData.catalogue 5).length,
    ∀ p q : Fin 13, eligible 5 i.val p.val q.val=true →
      (⟨5,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by decide +kernel
#print axioms covered5
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered8 : decide (∀ i : Fin (RootedCatalogueData.catalogue 8).length,
    ∀ p q : Fin 10, eligible 8 i.val p.val q.val=true →
      (⟨8,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by decide +kernel
#print axioms covered8
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys

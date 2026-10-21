/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered4 : decide (∀ i : Fin (RootedCatalogueData.catalogue 4).length,
    ∀ p q : Fin 10, eligible 4 i.val p.val q.val=true →
      (⟨4,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by decide +kernel
#print axioms covered4
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys

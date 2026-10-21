/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered6 : decide (∀ i : Fin (RootedCatalogueData.catalogue 6).length,
    ∀ p q : Fin 11, eligible 6 i.val p.val q.val=true →
      (⟨6,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by decide +kernel
#print axioms covered6
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys

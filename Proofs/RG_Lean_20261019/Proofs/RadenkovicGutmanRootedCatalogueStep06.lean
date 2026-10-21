/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedCatalogueStep06Block000
import Proofs.RadenkovicGutmanRootedCatalogueStep06Block001
import Proofs.RadenkovicGutmanRootedCatalogueStep06Block002
namespace Gebendorfer.RadenkovicGutman.RootedCatalogueData
open RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem step6 : ∀ i : Fin level6.length, ∀ v : Vertices 6,
    ∃ j : Fin level7.length,
      ∃ e : graph (n := 7) (level6.get i,v) ≃g graph (level7.get j),
        e (root 7)=root 7 := by
  intro i v
  have hi := i.isLt
  change i.val < 48 at hi
  by_cases h0 : i.val < 16
  · exact range_sound 6 level6 level7 0 16 (by decide) witnesses6b000 checked6b000
      ⟨i.val-0,by omega⟩ v i (by change 0+(i.val-0)=i.val; omega)
  ·
    by_cases h1 : i.val < 32
    · exact range_sound 6 level6 level7 16 16 (by decide) witnesses6b001 checked6b001
        ⟨i.val-16,by omega⟩ v i (by change 16+(i.val-16)=i.val; omega)
    ·
      exact range_sound 6 level6 level7 32 16 (by decide) witnesses6b002 checked6b002
          ⟨i.val-32,by omega⟩ v i (by change 32+(i.val-32)=i.val; omega)
#print axioms step6
end Gebendorfer.RadenkovicGutman.RootedCatalogueData

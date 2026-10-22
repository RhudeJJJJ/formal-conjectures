/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5394 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap5394 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5394 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5394_checked : acceptsGraphIso
    (source (graph core5394) (root 6) 4 4) DegreeTwoThreeSpectrum7053.graph sourceMap5394=true := by decide +kernel
theorem fusedMap5394_checked : acceptsGraphIso
    (fused (graph core5394) (root 6) 4 4) DegreeTwoThreeSpectrum5049.graph fusedMap5394=true := by decide +kernel
theorem certified5394 : Certified (graph core5394) (root 6) 4 4 :=
  of_native_maps core5394 DegreeTwoThreeSpectrum7053.graph DegreeTwoThreeSpectrum5049.graph
    sourceMap5394 fusedMap5394 sourceMap5394_checked fusedMap5394_checked
    DegreeTwoThreeFiniteComparisons.comparison5394
#print axioms sourceMap5394_checked
#print axioms fusedMap5394_checked
#print axioms certified5394
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

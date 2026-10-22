/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5396 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap5396 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5396 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5396_checked : acceptsGraphIso
    (source (graph core5396) (root 6) 4 4) DegreeTwoThreeSpectrum7055.graph sourceMap5396=true := by decide +kernel
theorem fusedMap5396_checked : acceptsGraphIso
    (fused (graph core5396) (root 6) 4 4) DegreeTwoThreeSpectrum5164.graph fusedMap5396=true := by decide +kernel
theorem certified5396 : Certified (graph core5396) (root 6) 4 4 :=
  of_native_maps core5396 DegreeTwoThreeSpectrum7055.graph DegreeTwoThreeSpectrum5164.graph
    sourceMap5396 fusedMap5396 sourceMap5396_checked fusedMap5396_checked
    DegreeTwoThreeFiniteComparisons.comparison5396
#print axioms sourceMap5396_checked
#print axioms fusedMap5396_checked
#print axioms certified5396
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5392 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap5392 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5392 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5392_checked : acceptsGraphIso
    (source (graph core5392) (root 6) 4 4) DegreeTwoThreeSpectrum7051.graph sourceMap5392=true := by decide +kernel
theorem fusedMap5392_checked : acceptsGraphIso
    (fused (graph core5392) (root 6) 4 4) DegreeTwoThreeSpectrum5021.graph fusedMap5392=true := by decide +kernel
theorem certified5392 : Certified (graph core5392) (root 6) 4 4 :=
  of_native_maps core5392 DegreeTwoThreeSpectrum7051.graph DegreeTwoThreeSpectrum5021.graph
    sourceMap5392 fusedMap5392 sourceMap5392_checked fusedMap5392_checked
    DegreeTwoThreeFiniteComparisons.comparison5392
#print axioms sourceMap5392_checked
#print axioms fusedMap5392_checked
#print axioms certified5392
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

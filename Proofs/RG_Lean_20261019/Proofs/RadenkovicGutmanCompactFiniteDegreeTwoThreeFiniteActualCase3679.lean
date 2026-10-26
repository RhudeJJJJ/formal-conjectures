/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3679 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap3679 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3679 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3679_checked : acceptsGraphIso
    (source (graph core3679) (root 7) 0 7) DegreeTwoThreeSpectrum5833.graph sourceMap3679=true := by decide +kernel
theorem fusedMap3679_checked : acceptsGraphIso
    (fused (graph core3679) (root 7) 0 7) DegreeTwoThreeSpectrum5081.graph fusedMap3679=true := by decide +kernel
theorem certified3679 : Certified (graph core3679) (root 7) 0 7 :=
  of_native_maps core3679 DegreeTwoThreeSpectrum5833.graph DegreeTwoThreeSpectrum5081.graph
    sourceMap3679 fusedMap3679 sourceMap3679_checked fusedMap3679_checked
    DegreeTwoThreeFiniteComparisons.comparison3679
#print axioms sourceMap3679_checked
#print axioms fusedMap3679_checked
#print axioms certified3679
def sourceMap3679swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3679swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3679swap_checked : acceptsGraphIso
    (source (graph core3679) (root 7) 7 0) DegreeTwoThreeSpectrum5833.graph sourceMap3679swap=true := by decide +kernel
theorem fusedMap3679swap_checked : acceptsGraphIso
    (fused (graph core3679) (root 7) 7 0) DegreeTwoThreeSpectrum5081.graph fusedMap3679swap=true := by decide +kernel
theorem certified3679swap : Certified (graph core3679) (root 7) 7 0 :=
  of_native_maps core3679 DegreeTwoThreeSpectrum5833.graph DegreeTwoThreeSpectrum5081.graph
    sourceMap3679swap fusedMap3679swap sourceMap3679swap_checked fusedMap3679swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3679
#print axioms sourceMap3679swap_checked
#print axioms fusedMap3679swap_checked
#print axioms certified3679swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

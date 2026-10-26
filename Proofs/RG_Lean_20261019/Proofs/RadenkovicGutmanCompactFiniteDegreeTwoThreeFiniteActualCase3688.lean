/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3688 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap3688 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3688 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3688_checked : acceptsGraphIso
    (source (graph core3688) (root 7) 0 7) DegreeTwoThreeSpectrum5312.graph sourceMap3688=true := by decide +kernel
theorem fusedMap3688_checked : acceptsGraphIso
    (fused (graph core3688) (root 7) 0 7) DegreeTwoThreeSpectrum5315.graph fusedMap3688=true := by decide +kernel
theorem certified3688 : Certified (graph core3688) (root 7) 0 7 :=
  of_native_maps core3688 DegreeTwoThreeSpectrum5312.graph DegreeTwoThreeSpectrum5315.graph
    sourceMap3688 fusedMap3688 sourceMap3688_checked fusedMap3688_checked
    DegreeTwoThreeFiniteComparisons.comparison3688
#print axioms sourceMap3688_checked
#print axioms fusedMap3688_checked
#print axioms certified3688
def sourceMap3688swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3688swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3688swap_checked : acceptsGraphIso
    (source (graph core3688) (root 7) 7 0) DegreeTwoThreeSpectrum5312.graph sourceMap3688swap=true := by decide +kernel
theorem fusedMap3688swap_checked : acceptsGraphIso
    (fused (graph core3688) (root 7) 7 0) DegreeTwoThreeSpectrum5315.graph fusedMap3688swap=true := by decide +kernel
theorem certified3688swap : Certified (graph core3688) (root 7) 7 0 :=
  of_native_maps core3688 DegreeTwoThreeSpectrum5312.graph DegreeTwoThreeSpectrum5315.graph
    sourceMap3688swap fusedMap3688swap sourceMap3688swap_checked fusedMap3688swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3688
#print axioms sourceMap3688swap_checked
#print axioms fusedMap3688swap_checked
#print axioms certified3688swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

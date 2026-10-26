/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3690 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap3690 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3690 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3690_checked : acceptsGraphIso
    (source (graph core3690) (root 7) 0 7) DegreeTwoThreeSpectrum5443.graph sourceMap3690=true := by decide +kernel
theorem fusedMap3690_checked : acceptsGraphIso
    (fused (graph core3690) (root 7) 0 7) DegreeTwoThreeSpectrum5446.graph fusedMap3690=true := by decide +kernel
theorem certified3690 : Certified (graph core3690) (root 7) 0 7 :=
  of_native_maps core3690 DegreeTwoThreeSpectrum5443.graph DegreeTwoThreeSpectrum5446.graph
    sourceMap3690 fusedMap3690 sourceMap3690_checked fusedMap3690_checked
    DegreeTwoThreeFiniteComparisons.comparison3690
#print axioms sourceMap3690_checked
#print axioms fusedMap3690_checked
#print axioms certified3690
def sourceMap3690swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3690swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3690swap_checked : acceptsGraphIso
    (source (graph core3690) (root 7) 7 0) DegreeTwoThreeSpectrum5443.graph sourceMap3690swap=true := by decide +kernel
theorem fusedMap3690swap_checked : acceptsGraphIso
    (fused (graph core3690) (root 7) 7 0) DegreeTwoThreeSpectrum5446.graph fusedMap3690swap=true := by decide +kernel
theorem certified3690swap : Certified (graph core3690) (root 7) 7 0 :=
  of_native_maps core3690 DegreeTwoThreeSpectrum5443.graph DegreeTwoThreeSpectrum5446.graph
    sourceMap3690swap fusedMap3690swap sourceMap3690swap_checked fusedMap3690swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3690
#print axioms sourceMap3690swap_checked
#print axioms fusedMap3690swap_checked
#print axioms certified3690swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3689 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap3689 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3689 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3689_checked : acceptsGraphIso
    (source (graph core3689) (root 7) 0 7) DegreeTwoThreeSpectrum5428.graph sourceMap3689=true := by decide +kernel
theorem fusedMap3689_checked : acceptsGraphIso
    (fused (graph core3689) (root 7) 0 7) DegreeTwoThreeSpectrum5431.graph fusedMap3689=true := by decide +kernel
theorem certified3689 : Certified (graph core3689) (root 7) 0 7 :=
  of_native_maps core3689 DegreeTwoThreeSpectrum5428.graph DegreeTwoThreeSpectrum5431.graph
    sourceMap3689 fusedMap3689 sourceMap3689_checked fusedMap3689_checked
    DegreeTwoThreeFiniteComparisons.comparison3689
#print axioms sourceMap3689_checked
#print axioms fusedMap3689_checked
#print axioms certified3689
def sourceMap3689swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3689swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3689swap_checked : acceptsGraphIso
    (source (graph core3689) (root 7) 7 0) DegreeTwoThreeSpectrum5428.graph sourceMap3689swap=true := by decide +kernel
theorem fusedMap3689swap_checked : acceptsGraphIso
    (fused (graph core3689) (root 7) 7 0) DegreeTwoThreeSpectrum5431.graph fusedMap3689swap=true := by decide +kernel
theorem certified3689swap : Certified (graph core3689) (root 7) 7 0 :=
  of_native_maps core3689 DegreeTwoThreeSpectrum5428.graph DegreeTwoThreeSpectrum5431.graph
    sourceMap3689swap fusedMap3689swap sourceMap3689swap_checked fusedMap3689swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3689
#print axioms sourceMap3689swap_checked
#print axioms fusedMap3689swap_checked
#print axioms certified3689swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

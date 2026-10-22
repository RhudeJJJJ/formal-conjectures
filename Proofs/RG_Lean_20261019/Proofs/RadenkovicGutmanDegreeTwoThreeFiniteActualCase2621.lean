/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2621 : Family 10 := level10.get ⟨600,by decide⟩
def sourceMap2621 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2621 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2621_checked : acceptsGraphIso
    (source (graph core2621) (root 10) 0 4) DegreeTwoThreeSpectrum6312.graph sourceMap2621=true := by decide +kernel
theorem fusedMap2621_checked : acceptsGraphIso
    (fused (graph core2621) (root 10) 0 4) DegreeTwoThreeSpectrum5275.graph fusedMap2621=true := by decide +kernel
theorem certified2621 : Certified (graph core2621) (root 10) 0 4 :=
  of_native_maps core2621 DegreeTwoThreeSpectrum6312.graph DegreeTwoThreeSpectrum5275.graph
    sourceMap2621 fusedMap2621 sourceMap2621_checked fusedMap2621_checked
    DegreeTwoThreeFiniteComparisons.comparison2621
#print axioms sourceMap2621_checked
#print axioms fusedMap2621_checked
#print axioms certified2621
def sourceMap2621swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2621swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2621swap_checked : acceptsGraphIso
    (source (graph core2621) (root 10) 4 0) DegreeTwoThreeSpectrum6312.graph sourceMap2621swap=true := by decide +kernel
theorem fusedMap2621swap_checked : acceptsGraphIso
    (fused (graph core2621) (root 10) 4 0) DegreeTwoThreeSpectrum5275.graph fusedMap2621swap=true := by decide +kernel
theorem certified2621swap : Certified (graph core2621) (root 10) 4 0 :=
  of_native_maps core2621 DegreeTwoThreeSpectrum6312.graph DegreeTwoThreeSpectrum5275.graph
    sourceMap2621swap fusedMap2621swap sourceMap2621swap_checked fusedMap2621swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2621
#print axioms sourceMap2621swap_checked
#print axioms fusedMap2621swap_checked
#print axioms certified2621swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

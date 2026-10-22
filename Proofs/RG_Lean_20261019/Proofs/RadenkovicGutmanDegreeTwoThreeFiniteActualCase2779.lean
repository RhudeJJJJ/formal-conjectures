/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2779 : Family 10 := level10.get ⟨1023,by decide⟩
def sourceMap2779 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2779 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2779_checked : acceptsGraphIso
    (source (graph core2779) (root 10) 0 4) DegreeTwoThreeSpectrum6029.graph sourceMap2779=true := by decide +kernel
theorem fusedMap2779_checked : acceptsGraphIso
    (fused (graph core2779) (root 10) 0 4) DegreeTwoThreeSpectrum6030.graph fusedMap2779=true := by decide +kernel
theorem certified2779 : Certified (graph core2779) (root 10) 0 4 :=
  of_native_maps core2779 DegreeTwoThreeSpectrum6029.graph DegreeTwoThreeSpectrum6030.graph
    sourceMap2779 fusedMap2779 sourceMap2779_checked fusedMap2779_checked
    DegreeTwoThreeFiniteComparisons.comparison2779
#print axioms sourceMap2779_checked
#print axioms fusedMap2779_checked
#print axioms certified2779
def sourceMap2779swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2779swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2779swap_checked : acceptsGraphIso
    (source (graph core2779) (root 10) 4 0) DegreeTwoThreeSpectrum6029.graph sourceMap2779swap=true := by decide +kernel
theorem fusedMap2779swap_checked : acceptsGraphIso
    (fused (graph core2779) (root 10) 4 0) DegreeTwoThreeSpectrum6030.graph fusedMap2779swap=true := by decide +kernel
theorem certified2779swap : Certified (graph core2779) (root 10) 4 0 :=
  of_native_maps core2779 DegreeTwoThreeSpectrum6029.graph DegreeTwoThreeSpectrum6030.graph
    sourceMap2779swap fusedMap2779swap sourceMap2779swap_checked fusedMap2779swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2779
#print axioms sourceMap2779swap_checked
#print axioms fusedMap2779swap_checked
#print axioms certified2779swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1394 : Family 9 := level9.get ⟨587,by decide⟩
def sourceMap1394 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1394 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1394_checked : acceptsGraphIso
    (source (graph core1394) (root 9) 0 2) DegreeTwoThreeSpectrum2266.graph sourceMap1394=true := by decide +kernel
theorem fusedMap1394_checked : acceptsGraphIso
    (fused (graph core1394) (root 9) 0 2) DegreeTwoThreeSpectrum1988.graph fusedMap1394=true := by decide +kernel
theorem certified1394 : Certified (graph core1394) (root 9) 0 2 :=
  of_native_maps core1394 DegreeTwoThreeSpectrum2266.graph DegreeTwoThreeSpectrum1988.graph
    sourceMap1394 fusedMap1394 sourceMap1394_checked fusedMap1394_checked
    DegreeTwoThreeFiniteComparisons.comparison1394
#print axioms sourceMap1394_checked
#print axioms fusedMap1394_checked
#print axioms certified1394
def sourceMap1394swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1394swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1394swap_checked : acceptsGraphIso
    (source (graph core1394) (root 9) 2 0) DegreeTwoThreeSpectrum2266.graph sourceMap1394swap=true := by decide +kernel
theorem fusedMap1394swap_checked : acceptsGraphIso
    (fused (graph core1394) (root 9) 2 0) DegreeTwoThreeSpectrum1988.graph fusedMap1394swap=true := by decide +kernel
theorem certified1394swap : Certified (graph core1394) (root 9) 2 0 :=
  of_native_maps core1394 DegreeTwoThreeSpectrum2266.graph DegreeTwoThreeSpectrum1988.graph
    sourceMap1394swap fusedMap1394swap sourceMap1394swap_checked fusedMap1394swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1394
#print axioms sourceMap1394swap_checked
#print axioms fusedMap1394swap_checked
#print axioms certified1394swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

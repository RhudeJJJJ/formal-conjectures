/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1393 : Family 9 := level9.get ⟨580,by decide⟩
def sourceMap1393 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1393 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1393_checked : acceptsGraphIso
    (source (graph core1393) (root 9) 0 2) DegreeTwoThreeSpectrum2265.graph sourceMap1393=true := by decide +kernel
theorem fusedMap1393_checked : acceptsGraphIso
    (fused (graph core1393) (root 9) 0 2) DegreeTwoThreeSpectrum1972.graph fusedMap1393=true := by decide +kernel
theorem certified1393 : Certified (graph core1393) (root 9) 0 2 :=
  of_native_maps core1393 DegreeTwoThreeSpectrum2265.graph DegreeTwoThreeSpectrum1972.graph
    sourceMap1393 fusedMap1393 sourceMap1393_checked fusedMap1393_checked
    DegreeTwoThreeFiniteComparisons.comparison1393
#print axioms sourceMap1393_checked
#print axioms fusedMap1393_checked
#print axioms certified1393
def sourceMap1393swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8,13] (sourceLabel 9 2 0 v)
def fusedMap1393swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1393swap_checked : acceptsGraphIso
    (source (graph core1393) (root 9) 2 0) DegreeTwoThreeSpectrum2265.graph sourceMap1393swap=true := by decide +kernel
theorem fusedMap1393swap_checked : acceptsGraphIso
    (fused (graph core1393) (root 9) 2 0) DegreeTwoThreeSpectrum1972.graph fusedMap1393swap=true := by decide +kernel
theorem certified1393swap : Certified (graph core1393) (root 9) 2 0 :=
  of_native_maps core1393 DegreeTwoThreeSpectrum2265.graph DegreeTwoThreeSpectrum1972.graph
    sourceMap1393swap fusedMap1393swap sourceMap1393swap_checked fusedMap1393swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1393
#print axioms sourceMap1393swap_checked
#print axioms fusedMap1393swap_checked
#print axioms certified1393swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

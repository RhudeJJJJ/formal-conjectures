/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1435 : Family 10 := level10.get ⟨38,by decide⟩
def sourceMap1435 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1435 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,7,3,4,5,6] (fusedLabel 10 0 2 v)
theorem sourceMap1435_checked : acceptsGraphIso
    (source (graph core1435) (root 10) 0 2) DegreeTwoThreeSpectrum2391.graph sourceMap1435=true := by decide +kernel
theorem fusedMap1435_checked : acceptsGraphIso
    (fused (graph core1435) (root 10) 0 2) DegreeTwoThreeSpectrum2423.graph fusedMap1435=true := by decide +kernel
theorem certified1435 : Certified (graph core1435) (root 10) 0 2 :=
  of_native_maps core1435 DegreeTwoThreeSpectrum2391.graph DegreeTwoThreeSpectrum2423.graph
    sourceMap1435 fusedMap1435 sourceMap1435_checked fusedMap1435_checked
    DegreeTwoThreeFiniteComparisons.comparison1435
#print axioms sourceMap1435_checked
#print axioms fusedMap1435_checked
#print axioms certified1435
def sourceMap1435swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1435swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,7,3,4,5,6] (fusedLabel 10 2 0 v)
theorem sourceMap1435swap_checked : acceptsGraphIso
    (source (graph core1435) (root 10) 2 0) DegreeTwoThreeSpectrum2391.graph sourceMap1435swap=true := by decide +kernel
theorem fusedMap1435swap_checked : acceptsGraphIso
    (fused (graph core1435) (root 10) 2 0) DegreeTwoThreeSpectrum2423.graph fusedMap1435swap=true := by decide +kernel
theorem certified1435swap : Certified (graph core1435) (root 10) 2 0 :=
  of_native_maps core1435 DegreeTwoThreeSpectrum2391.graph DegreeTwoThreeSpectrum2423.graph
    sourceMap1435swap fusedMap1435swap sourceMap1435swap_checked fusedMap1435swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1435
#print axioms sourceMap1435swap_checked
#print axioms fusedMap1435swap_checked
#print axioms certified1435swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

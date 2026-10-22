/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1947 : Family 10 := level10.get ⟨1478,by decide⟩
def sourceMap1947 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1947 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1947_checked : acceptsGraphIso
    (source (graph core1947) (root 10) 0 2) DegreeTwoThreeSpectrum3240.graph sourceMap1947=true := by decide +kernel
theorem fusedMap1947_checked : acceptsGraphIso
    (fused (graph core1947) (root 10) 0 2) DegreeTwoThreeSpectrum3719.graph fusedMap1947=true := by decide +kernel
theorem certified1947 : Certified (graph core1947) (root 10) 0 2 :=
  of_native_maps core1947 DegreeTwoThreeSpectrum3240.graph DegreeTwoThreeSpectrum3719.graph
    sourceMap1947 fusedMap1947 sourceMap1947_checked fusedMap1947_checked
    DegreeTwoThreeFiniteComparisons.comparison1947
#print axioms sourceMap1947_checked
#print axioms fusedMap1947_checked
#print axioms certified1947
def sourceMap1947swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1947swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1947swap_checked : acceptsGraphIso
    (source (graph core1947) (root 10) 2 0) DegreeTwoThreeSpectrum3240.graph sourceMap1947swap=true := by decide +kernel
theorem fusedMap1947swap_checked : acceptsGraphIso
    (fused (graph core1947) (root 10) 2 0) DegreeTwoThreeSpectrum3719.graph fusedMap1947swap=true := by decide +kernel
theorem certified1947swap : Certified (graph core1947) (root 10) 2 0 :=
  of_native_maps core1947 DegreeTwoThreeSpectrum3240.graph DegreeTwoThreeSpectrum3719.graph
    sourceMap1947swap fusedMap1947swap sourceMap1947swap_checked fusedMap1947swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1947
#print axioms sourceMap1947swap_checked
#print axioms fusedMap1947swap_checked
#print axioms certified1947swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

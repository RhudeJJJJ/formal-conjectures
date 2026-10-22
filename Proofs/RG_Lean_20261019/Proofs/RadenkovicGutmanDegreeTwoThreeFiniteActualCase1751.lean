/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1751 : Family 10 := level10.get ⟨1006,by decide⟩
def sourceMap1751 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1751 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1751_checked : acceptsGraphIso
    (source (graph core1751) (root 10) 0 2) DegreeTwoThreeSpectrum3017.graph sourceMap1751=true := by decide +kernel
theorem fusedMap1751_checked : acceptsGraphIso
    (fused (graph core1751) (root 10) 0 2) DegreeTwoThreeSpectrum3019.graph fusedMap1751=true := by decide +kernel
theorem certified1751 : Certified (graph core1751) (root 10) 0 2 :=
  of_native_maps core1751 DegreeTwoThreeSpectrum3017.graph DegreeTwoThreeSpectrum3019.graph
    sourceMap1751 fusedMap1751 sourceMap1751_checked fusedMap1751_checked
    DegreeTwoThreeFiniteComparisons.comparison1751
#print axioms sourceMap1751_checked
#print axioms fusedMap1751_checked
#print axioms certified1751
def sourceMap1751swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1751swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1751swap_checked : acceptsGraphIso
    (source (graph core1751) (root 10) 2 0) DegreeTwoThreeSpectrum3017.graph sourceMap1751swap=true := by decide +kernel
theorem fusedMap1751swap_checked : acceptsGraphIso
    (fused (graph core1751) (root 10) 2 0) DegreeTwoThreeSpectrum3019.graph fusedMap1751swap=true := by decide +kernel
theorem certified1751swap : Certified (graph core1751) (root 10) 2 0 :=
  of_native_maps core1751 DegreeTwoThreeSpectrum3017.graph DegreeTwoThreeSpectrum3019.graph
    sourceMap1751swap fusedMap1751swap sourceMap1751swap_checked fusedMap1751swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1751
#print axioms sourceMap1751swap_checked
#print axioms fusedMap1751swap_checked
#print axioms certified1751swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1942 : Family 10 := level10.get ⟨1467,by decide⟩
def sourceMap1942 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1942 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1942_checked : acceptsGraphIso
    (source (graph core1942) (root 10) 0 2) DegreeTwoThreeSpectrum3296.graph sourceMap1942=true := by decide +kernel
theorem fusedMap1942_checked : acceptsGraphIso
    (fused (graph core1942) (root 10) 0 2) DegreeTwoThreeSpectrum3708.graph fusedMap1942=true := by decide +kernel
theorem certified1942 : Certified (graph core1942) (root 10) 0 2 :=
  of_native_maps core1942 DegreeTwoThreeSpectrum3296.graph DegreeTwoThreeSpectrum3708.graph
    sourceMap1942 fusedMap1942 sourceMap1942_checked fusedMap1942_checked
    DegreeTwoThreeFiniteComparisons.comparison1942
#print axioms sourceMap1942_checked
#print axioms fusedMap1942_checked
#print axioms certified1942
def sourceMap1942swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1942swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1942swap_checked : acceptsGraphIso
    (source (graph core1942) (root 10) 2 0) DegreeTwoThreeSpectrum3296.graph sourceMap1942swap=true := by decide +kernel
theorem fusedMap1942swap_checked : acceptsGraphIso
    (fused (graph core1942) (root 10) 2 0) DegreeTwoThreeSpectrum3708.graph fusedMap1942swap=true := by decide +kernel
theorem certified1942swap : Certified (graph core1942) (root 10) 2 0 :=
  of_native_maps core1942 DegreeTwoThreeSpectrum3296.graph DegreeTwoThreeSpectrum3708.graph
    sourceMap1942swap fusedMap1942swap sourceMap1942swap_checked fusedMap1942swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1942
#print axioms sourceMap1942swap_checked
#print axioms fusedMap1942swap_checked
#print axioms certified1942swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1768 : Family 10 := level10.get ⟨1056,by decide⟩
def sourceMap1768 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1768 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1768_checked : acceptsGraphIso
    (source (graph core1768) (root 10) 0 2) DegreeTwoThreeSpectrum3099.graph sourceMap1768=true := by decide +kernel
theorem fusedMap1768_checked : acceptsGraphIso
    (fused (graph core1768) (root 10) 0 2) DegreeTwoThreeSpectrum3100.graph fusedMap1768=true := by decide +kernel
theorem certified1768 : Certified (graph core1768) (root 10) 0 2 :=
  of_native_maps core1768 DegreeTwoThreeSpectrum3099.graph DegreeTwoThreeSpectrum3100.graph
    sourceMap1768 fusedMap1768 sourceMap1768_checked fusedMap1768_checked
    DegreeTwoThreeFiniteComparisons.comparison1768
#print axioms sourceMap1768_checked
#print axioms fusedMap1768_checked
#print axioms certified1768
def sourceMap1768swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1768swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1768swap_checked : acceptsGraphIso
    (source (graph core1768) (root 10) 2 0) DegreeTwoThreeSpectrum3099.graph sourceMap1768swap=true := by decide +kernel
theorem fusedMap1768swap_checked : acceptsGraphIso
    (fused (graph core1768) (root 10) 2 0) DegreeTwoThreeSpectrum3100.graph fusedMap1768swap=true := by decide +kernel
theorem certified1768swap : Certified (graph core1768) (root 10) 2 0 :=
  of_native_maps core1768 DegreeTwoThreeSpectrum3099.graph DegreeTwoThreeSpectrum3100.graph
    sourceMap1768swap fusedMap1768swap sourceMap1768swap_checked fusedMap1768swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1768
#print axioms sourceMap1768swap_checked
#print axioms fusedMap1768swap_checked
#print axioms certified1768swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1347 : Family 9 := level9.get ⟨473,by decide⟩
def sourceMap1347 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1347 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1347_checked : acceptsGraphIso
    (source (graph core1347) (root 9) 0 2) DegreeTwoThreeSpectrum2161.graph sourceMap1347=true := by decide +kernel
theorem fusedMap1347_checked : acceptsGraphIso
    (fused (graph core1347) (root 9) 0 2) DegreeTwoThreeSpectrum2165.graph fusedMap1347=true := by decide +kernel
theorem certified1347 : Certified (graph core1347) (root 9) 0 2 :=
  of_native_maps core1347 DegreeTwoThreeSpectrum2161.graph DegreeTwoThreeSpectrum2165.graph
    sourceMap1347 fusedMap1347 sourceMap1347_checked fusedMap1347_checked
    DegreeTwoThreeFiniteComparisons.comparison1347
#print axioms sourceMap1347_checked
#print axioms fusedMap1347_checked
#print axioms certified1347
def sourceMap1347swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1347swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1347swap_checked : acceptsGraphIso
    (source (graph core1347) (root 9) 2 0) DegreeTwoThreeSpectrum2161.graph sourceMap1347swap=true := by decide +kernel
theorem fusedMap1347swap_checked : acceptsGraphIso
    (fused (graph core1347) (root 9) 2 0) DegreeTwoThreeSpectrum2165.graph fusedMap1347swap=true := by decide +kernel
theorem certified1347swap : Certified (graph core1347) (root 9) 2 0 :=
  of_native_maps core1347 DegreeTwoThreeSpectrum2161.graph DegreeTwoThreeSpectrum2165.graph
    sourceMap1347swap fusedMap1347swap sourceMap1347swap_checked fusedMap1347swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1347
#print axioms sourceMap1347swap_checked
#print axioms fusedMap1347swap_checked
#print axioms certified1347swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

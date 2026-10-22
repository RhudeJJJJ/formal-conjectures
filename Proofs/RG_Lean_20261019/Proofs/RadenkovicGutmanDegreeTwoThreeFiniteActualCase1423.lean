/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1423 : Family 9 := level9.get ⟨657,by decide⟩
def sourceMap1423 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1423 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1423_checked : acceptsGraphIso
    (source (graph core1423) (root 9) 0 2) DegreeTwoThreeSpectrum2299.graph sourceMap1423=true := by decide +kernel
theorem fusedMap1423_checked : acceptsGraphIso
    (fused (graph core1423) (root 9) 0 2) DegreeTwoThreeSpectrum2124.graph fusedMap1423=true := by decide +kernel
theorem certified1423 : Certified (graph core1423) (root 9) 0 2 :=
  of_native_maps core1423 DegreeTwoThreeSpectrum2299.graph DegreeTwoThreeSpectrum2124.graph
    sourceMap1423 fusedMap1423 sourceMap1423_checked fusedMap1423_checked
    DegreeTwoThreeFiniteComparisons.comparison1423
#print axioms sourceMap1423_checked
#print axioms fusedMap1423_checked
#print axioms certified1423
def sourceMap1423swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1423swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1423swap_checked : acceptsGraphIso
    (source (graph core1423) (root 9) 2 0) DegreeTwoThreeSpectrum2299.graph sourceMap1423swap=true := by decide +kernel
theorem fusedMap1423swap_checked : acceptsGraphIso
    (fused (graph core1423) (root 9) 2 0) DegreeTwoThreeSpectrum2124.graph fusedMap1423swap=true := by decide +kernel
theorem certified1423swap : Certified (graph core1423) (root 9) 2 0 :=
  of_native_maps core1423 DegreeTwoThreeSpectrum2299.graph DegreeTwoThreeSpectrum2124.graph
    sourceMap1423swap fusedMap1423swap sourceMap1423swap_checked fusedMap1423swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1423
#print axioms sourceMap1423swap_checked
#print axioms fusedMap1423swap_checked
#print axioms certified1423swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

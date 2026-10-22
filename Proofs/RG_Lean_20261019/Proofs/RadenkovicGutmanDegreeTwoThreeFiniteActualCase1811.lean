/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1811 : Family 10 := level10.get ⟨1162,by decide⟩
def sourceMap1811 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1811 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1811_checked : acceptsGraphIso
    (source (graph core1811) (root 10) 0 2) DegreeTwoThreeSpectrum3259.graph sourceMap1811=true := by decide +kernel
theorem fusedMap1811_checked : acceptsGraphIso
    (fused (graph core1811) (root 10) 0 2) DegreeTwoThreeSpectrum3263.graph fusedMap1811=true := by decide +kernel
theorem certified1811 : Certified (graph core1811) (root 10) 0 2 :=
  of_native_maps core1811 DegreeTwoThreeSpectrum3259.graph DegreeTwoThreeSpectrum3263.graph
    sourceMap1811 fusedMap1811 sourceMap1811_checked fusedMap1811_checked
    DegreeTwoThreeFiniteComparisons.comparison1811
#print axioms sourceMap1811_checked
#print axioms fusedMap1811_checked
#print axioms certified1811
def sourceMap1811swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1811swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1811swap_checked : acceptsGraphIso
    (source (graph core1811) (root 10) 2 0) DegreeTwoThreeSpectrum3259.graph sourceMap1811swap=true := by decide +kernel
theorem fusedMap1811swap_checked : acceptsGraphIso
    (fused (graph core1811) (root 10) 2 0) DegreeTwoThreeSpectrum3263.graph fusedMap1811swap=true := by decide +kernel
theorem certified1811swap : Certified (graph core1811) (root 10) 2 0 :=
  of_native_maps core1811 DegreeTwoThreeSpectrum3259.graph DegreeTwoThreeSpectrum3263.graph
    sourceMap1811swap fusedMap1811swap sourceMap1811swap_checked fusedMap1811swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1811
#print axioms sourceMap1811swap_checked
#print axioms fusedMap1811swap_checked
#print axioms certified1811swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

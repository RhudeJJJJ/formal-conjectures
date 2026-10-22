/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1351 : Family 9 := level9.get ⟨479,by decide⟩
def sourceMap1351 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,8,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1351 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 0 2 v)
theorem sourceMap1351_checked : acceptsGraphIso
    (source (graph core1351) (root 9) 0 2) DegreeTwoThreeSpectrum2141.graph sourceMap1351=true := by decide +kernel
theorem fusedMap1351_checked : acceptsGraphIso
    (fused (graph core1351) (root 9) 0 2) DegreeTwoThreeSpectrum2176.graph fusedMap1351=true := by decide +kernel
theorem certified1351 : Certified (graph core1351) (root 9) 0 2 :=
  of_native_maps core1351 DegreeTwoThreeSpectrum2141.graph DegreeTwoThreeSpectrum2176.graph
    sourceMap1351 fusedMap1351 sourceMap1351_checked fusedMap1351_checked
    DegreeTwoThreeFiniteComparisons.comparison1351
#print axioms sourceMap1351_checked
#print axioms fusedMap1351_checked
#print axioms certified1351
def sourceMap1351swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,5,6,7,8] (sourceLabel 9 2 0 v)
def fusedMap1351swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 2 0 v)
theorem sourceMap1351swap_checked : acceptsGraphIso
    (source (graph core1351) (root 9) 2 0) DegreeTwoThreeSpectrum2141.graph sourceMap1351swap=true := by decide +kernel
theorem fusedMap1351swap_checked : acceptsGraphIso
    (fused (graph core1351) (root 9) 2 0) DegreeTwoThreeSpectrum2176.graph fusedMap1351swap=true := by decide +kernel
theorem certified1351swap : Certified (graph core1351) (root 9) 2 0 :=
  of_native_maps core1351 DegreeTwoThreeSpectrum2141.graph DegreeTwoThreeSpectrum2176.graph
    sourceMap1351swap fusedMap1351swap sourceMap1351swap_checked fusedMap1351swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1351
#print axioms sourceMap1351swap_checked
#print axioms fusedMap1351swap_checked
#print axioms certified1351swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

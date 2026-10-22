/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1366 : Family 9 := level9.get ⟨514,by decide⟩
def sourceMap1366 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,4,5,6,7,1,2,3] (sourceLabel 9 0 2 v)
def fusedMap1366 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1366_checked : acceptsGraphIso
    (source (graph core1366) (root 9) 0 2) DegreeTwoThreeSpectrum2198.graph sourceMap1366=true := by decide +kernel
theorem fusedMap1366_checked : acceptsGraphIso
    (fused (graph core1366) (root 9) 0 2) DegreeTwoThreeSpectrum2226.graph fusedMap1366=true := by decide +kernel
theorem certified1366 : Certified (graph core1366) (root 9) 0 2 :=
  of_native_maps core1366 DegreeTwoThreeSpectrum2198.graph DegreeTwoThreeSpectrum2226.graph
    sourceMap1366 fusedMap1366 sourceMap1366_checked fusedMap1366_checked
    DegreeTwoThreeFiniteComparisons.comparison1366
#print axioms sourceMap1366_checked
#print axioms fusedMap1366_checked
#print axioms certified1366
def sourceMap1366swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,4,5,6,1,2,3,7] (sourceLabel 9 2 0 v)
def fusedMap1366swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1366swap_checked : acceptsGraphIso
    (source (graph core1366) (root 9) 2 0) DegreeTwoThreeSpectrum2198.graph sourceMap1366swap=true := by decide +kernel
theorem fusedMap1366swap_checked : acceptsGraphIso
    (fused (graph core1366) (root 9) 2 0) DegreeTwoThreeSpectrum2226.graph fusedMap1366swap=true := by decide +kernel
theorem certified1366swap : Certified (graph core1366) (root 9) 2 0 :=
  of_native_maps core1366 DegreeTwoThreeSpectrum2198.graph DegreeTwoThreeSpectrum2226.graph
    sourceMap1366swap fusedMap1366swap sourceMap1366swap_checked fusedMap1366swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1366
#print axioms sourceMap1366swap_checked
#print axioms fusedMap1366swap_checked
#print axioms certified1366swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1356 : Family 9 := level9.get ⟨496,by decide⟩
def sourceMap1356 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1356 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1356_checked : acceptsGraphIso
    (source (graph core1356) (root 9) 0 2) DegreeTwoThreeSpectrum2198.graph sourceMap1356=true := by decide +kernel
theorem fusedMap1356_checked : acceptsGraphIso
    (fused (graph core1356) (root 9) 0 2) DegreeTwoThreeSpectrum2200.graph fusedMap1356=true := by decide +kernel
theorem certified1356 : Certified (graph core1356) (root 9) 0 2 :=
  of_native_maps core1356 DegreeTwoThreeSpectrum2198.graph DegreeTwoThreeSpectrum2200.graph
    sourceMap1356 fusedMap1356 sourceMap1356_checked fusedMap1356_checked
    DegreeTwoThreeFiniteComparisons.comparison1356
#print axioms sourceMap1356_checked
#print axioms fusedMap1356_checked
#print axioms certified1356
def sourceMap1356swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1356swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1356swap_checked : acceptsGraphIso
    (source (graph core1356) (root 9) 2 0) DegreeTwoThreeSpectrum2198.graph sourceMap1356swap=true := by decide +kernel
theorem fusedMap1356swap_checked : acceptsGraphIso
    (fused (graph core1356) (root 9) 2 0) DegreeTwoThreeSpectrum2200.graph fusedMap1356swap=true := by decide +kernel
theorem certified1356swap : Certified (graph core1356) (root 9) 2 0 :=
  of_native_maps core1356 DegreeTwoThreeSpectrum2198.graph DegreeTwoThreeSpectrum2200.graph
    sourceMap1356swap fusedMap1356swap sourceMap1356swap_checked fusedMap1356swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1356
#print axioms sourceMap1356swap_checked
#print axioms fusedMap1356swap_checked
#print axioms certified1356swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

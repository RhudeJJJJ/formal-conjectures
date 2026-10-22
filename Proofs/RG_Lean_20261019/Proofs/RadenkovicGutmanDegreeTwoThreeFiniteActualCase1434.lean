/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1434 : Family 10 := level10.get ⟨32,by decide⟩
def sourceMap1434 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1434 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1434_checked : acceptsGraphIso
    (source (graph core1434) (root 10) 0 2) DegreeTwoThreeSpectrum2390.graph sourceMap1434=true := by decide +kernel
theorem fusedMap1434_checked : acceptsGraphIso
    (fused (graph core1434) (root 10) 0 2) DegreeTwoThreeSpectrum2405.graph fusedMap1434=true := by decide +kernel
theorem certified1434 : Certified (graph core1434) (root 10) 0 2 :=
  of_native_maps core1434 DegreeTwoThreeSpectrum2390.graph DegreeTwoThreeSpectrum2405.graph
    sourceMap1434 fusedMap1434 sourceMap1434_checked fusedMap1434_checked
    DegreeTwoThreeFiniteComparisons.comparison1434
#print axioms sourceMap1434_checked
#print axioms fusedMap1434_checked
#print axioms certified1434
def sourceMap1434swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1434swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1434swap_checked : acceptsGraphIso
    (source (graph core1434) (root 10) 2 0) DegreeTwoThreeSpectrum2390.graph sourceMap1434swap=true := by decide +kernel
theorem fusedMap1434swap_checked : acceptsGraphIso
    (fused (graph core1434) (root 10) 2 0) DegreeTwoThreeSpectrum2405.graph fusedMap1434swap=true := by decide +kernel
theorem certified1434swap : Certified (graph core1434) (root 10) 2 0 :=
  of_native_maps core1434 DegreeTwoThreeSpectrum2390.graph DegreeTwoThreeSpectrum2405.graph
    sourceMap1434swap fusedMap1434swap sourceMap1434swap_checked fusedMap1434swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1434
#print axioms sourceMap1434swap_checked
#print axioms fusedMap1434swap_checked
#print axioms certified1434swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

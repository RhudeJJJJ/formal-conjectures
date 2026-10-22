/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1481 : Family 10 := level10.get ⟨225,by decide⟩
def sourceMap1481 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1481 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1481_checked : acceptsGraphIso
    (source (graph core1481) (root 10) 0 2) DegreeTwoThreeSpectrum2529.graph sourceMap1481=true := by decide +kernel
theorem fusedMap1481_checked : acceptsGraphIso
    (fused (graph core1481) (root 10) 0 2) DegreeTwoThreeSpectrum2531.graph fusedMap1481=true := by decide +kernel
theorem certified1481 : Certified (graph core1481) (root 10) 0 2 :=
  of_native_maps core1481 DegreeTwoThreeSpectrum2529.graph DegreeTwoThreeSpectrum2531.graph
    sourceMap1481 fusedMap1481 sourceMap1481_checked fusedMap1481_checked
    DegreeTwoThreeFiniteComparisons.comparison1481
#print axioms sourceMap1481_checked
#print axioms fusedMap1481_checked
#print axioms certified1481
def sourceMap1481swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1481swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1481swap_checked : acceptsGraphIso
    (source (graph core1481) (root 10) 2 0) DegreeTwoThreeSpectrum2529.graph sourceMap1481swap=true := by decide +kernel
theorem fusedMap1481swap_checked : acceptsGraphIso
    (fused (graph core1481) (root 10) 2 0) DegreeTwoThreeSpectrum2531.graph fusedMap1481swap=true := by decide +kernel
theorem certified1481swap : Certified (graph core1481) (root 10) 2 0 :=
  of_native_maps core1481 DegreeTwoThreeSpectrum2529.graph DegreeTwoThreeSpectrum2531.graph
    sourceMap1481swap fusedMap1481swap sourceMap1481swap_checked fusedMap1481swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1481
#print axioms sourceMap1481swap_checked
#print axioms fusedMap1481swap_checked
#print axioms certified1481swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

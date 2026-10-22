/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1709 : Family 10 := level10.get ⟨906,by decide⟩
def sourceMap1709 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1709 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1709_checked : acceptsGraphIso
    (source (graph core1709) (root 10) 0 2) DegreeTwoThreeSpectrum3681.graph sourceMap1709=true := by decide +kernel
theorem fusedMap1709_checked : acceptsGraphIso
    (fused (graph core1709) (root 10) 0 2) DegreeTwoThreeSpectrum2920.graph fusedMap1709=true := by decide +kernel
theorem certified1709 : Certified (graph core1709) (root 10) 0 2 :=
  of_native_maps core1709 DegreeTwoThreeSpectrum3681.graph DegreeTwoThreeSpectrum2920.graph
    sourceMap1709 fusedMap1709 sourceMap1709_checked fusedMap1709_checked
    DegreeTwoThreeFiniteComparisons.comparison1709
#print axioms sourceMap1709_checked
#print axioms fusedMap1709_checked
#print axioms certified1709
def sourceMap1709swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1709swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1709swap_checked : acceptsGraphIso
    (source (graph core1709) (root 10) 2 0) DegreeTwoThreeSpectrum3681.graph sourceMap1709swap=true := by decide +kernel
theorem fusedMap1709swap_checked : acceptsGraphIso
    (fused (graph core1709) (root 10) 2 0) DegreeTwoThreeSpectrum2920.graph fusedMap1709swap=true := by decide +kernel
theorem certified1709swap : Certified (graph core1709) (root 10) 2 0 :=
  of_native_maps core1709 DegreeTwoThreeSpectrum3681.graph DegreeTwoThreeSpectrum2920.graph
    sourceMap1709swap fusedMap1709swap sourceMap1709swap_checked fusedMap1709swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1709
#print axioms sourceMap1709swap_checked
#print axioms fusedMap1709swap_checked
#print axioms certified1709swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

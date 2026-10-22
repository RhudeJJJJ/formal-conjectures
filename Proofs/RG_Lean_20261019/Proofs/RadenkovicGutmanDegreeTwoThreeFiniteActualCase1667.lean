/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1667 : Family 10 := level10.get ⟨794,by decide⟩
def sourceMap1667 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,13,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1667 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1667_checked : acceptsGraphIso
    (source (graph core1667) (root 10) 0 2) DegreeTwoThreeSpectrum3580.graph sourceMap1667=true := by decide +kernel
theorem fusedMap1667_checked : acceptsGraphIso
    (fused (graph core1667) (root 10) 0 2) DegreeTwoThreeSpectrum2761.graph fusedMap1667=true := by decide +kernel
theorem certified1667 : Certified (graph core1667) (root 10) 0 2 :=
  of_native_maps core1667 DegreeTwoThreeSpectrum3580.graph DegreeTwoThreeSpectrum2761.graph
    sourceMap1667 fusedMap1667 sourceMap1667_checked fusedMap1667_checked
    DegreeTwoThreeFiniteComparisons.comparison1667
#print axioms sourceMap1667_checked
#print axioms fusedMap1667_checked
#print axioms certified1667
def sourceMap1667swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,8,9,10,13] (sourceLabel 10 2 0 v)
def fusedMap1667swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1667swap_checked : acceptsGraphIso
    (source (graph core1667) (root 10) 2 0) DegreeTwoThreeSpectrum3580.graph sourceMap1667swap=true := by decide +kernel
theorem fusedMap1667swap_checked : acceptsGraphIso
    (fused (graph core1667) (root 10) 2 0) DegreeTwoThreeSpectrum2761.graph fusedMap1667swap=true := by decide +kernel
theorem certified1667swap : Certified (graph core1667) (root 10) 2 0 :=
  of_native_maps core1667 DegreeTwoThreeSpectrum3580.graph DegreeTwoThreeSpectrum2761.graph
    sourceMap1667swap fusedMap1667swap sourceMap1667swap_checked fusedMap1667swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1667
#print axioms sourceMap1667swap_checked
#print axioms fusedMap1667swap_checked
#print axioms certified1667swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

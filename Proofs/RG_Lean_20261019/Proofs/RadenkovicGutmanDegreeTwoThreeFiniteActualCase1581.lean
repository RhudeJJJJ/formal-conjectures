/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1581 : Family 10 := level10.get ⟨545,by decide⟩
def sourceMap1581 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1581 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1581_checked : acceptsGraphIso
    (source (graph core1581) (root 10) 0 2) DegreeTwoThreeSpectrum3139.graph sourceMap1581=true := by decide +kernel
theorem fusedMap1581_checked : acceptsGraphIso
    (fused (graph core1581) (root 10) 0 2) DegreeTwoThreeSpectrum2484.graph fusedMap1581=true := by decide +kernel
theorem certified1581 : Certified (graph core1581) (root 10) 0 2 :=
  of_native_maps core1581 DegreeTwoThreeSpectrum3139.graph DegreeTwoThreeSpectrum2484.graph
    sourceMap1581 fusedMap1581 sourceMap1581_checked fusedMap1581_checked
    DegreeTwoThreeFiniteComparisons.comparison1581
#print axioms sourceMap1581_checked
#print axioms fusedMap1581_checked
#print axioms certified1581
def sourceMap1581swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1581swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1581swap_checked : acceptsGraphIso
    (source (graph core1581) (root 10) 2 0) DegreeTwoThreeSpectrum3139.graph sourceMap1581swap=true := by decide +kernel
theorem fusedMap1581swap_checked : acceptsGraphIso
    (fused (graph core1581) (root 10) 2 0) DegreeTwoThreeSpectrum2484.graph fusedMap1581swap=true := by decide +kernel
theorem certified1581swap : Certified (graph core1581) (root 10) 2 0 :=
  of_native_maps core1581 DegreeTwoThreeSpectrum3139.graph DegreeTwoThreeSpectrum2484.graph
    sourceMap1581swap fusedMap1581swap sourceMap1581swap_checked fusedMap1581swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1581
#print axioms sourceMap1581swap_checked
#print axioms fusedMap1581swap_checked
#print axioms certified1581swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

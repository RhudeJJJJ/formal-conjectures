/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1501 : Family 10 := level10.get ⟨294,by decide⟩
def sourceMap1501 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1501 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1501_checked : acceptsGraphIso
    (source (graph core1501) (root 10) 0 2) DegreeTwoThreeSpectrum2671.graph sourceMap1501=true := by decide +kernel
theorem fusedMap1501_checked : acceptsGraphIso
    (fused (graph core1501) (root 10) 0 2) DegreeTwoThreeSpectrum2673.graph fusedMap1501=true := by decide +kernel
theorem certified1501 : Certified (graph core1501) (root 10) 0 2 :=
  of_native_maps core1501 DegreeTwoThreeSpectrum2671.graph DegreeTwoThreeSpectrum2673.graph
    sourceMap1501 fusedMap1501 sourceMap1501_checked fusedMap1501_checked
    DegreeTwoThreeFiniteComparisons.comparison1501
#print axioms sourceMap1501_checked
#print axioms fusedMap1501_checked
#print axioms certified1501
def sourceMap1501swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1501swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1501swap_checked : acceptsGraphIso
    (source (graph core1501) (root 10) 2 0) DegreeTwoThreeSpectrum2671.graph sourceMap1501swap=true := by decide +kernel
theorem fusedMap1501swap_checked : acceptsGraphIso
    (fused (graph core1501) (root 10) 2 0) DegreeTwoThreeSpectrum2673.graph fusedMap1501swap=true := by decide +kernel
theorem certified1501swap : Certified (graph core1501) (root 10) 2 0 :=
  of_native_maps core1501 DegreeTwoThreeSpectrum2671.graph DegreeTwoThreeSpectrum2673.graph
    sourceMap1501swap fusedMap1501swap sourceMap1501swap_checked fusedMap1501swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1501
#print axioms sourceMap1501swap_checked
#print axioms fusedMap1501swap_checked
#print axioms certified1501swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

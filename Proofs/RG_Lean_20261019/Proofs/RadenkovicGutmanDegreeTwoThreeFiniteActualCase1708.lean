/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1708 : Family 10 := level10.get ⟨905,by decide⟩
def sourceMap1708 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1708 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1708_checked : acceptsGraphIso
    (source (graph core1708) (root 10) 0 2) DegreeTwoThreeSpectrum3705.graph sourceMap1708=true := by decide +kernel
theorem fusedMap1708_checked : acceptsGraphIso
    (fused (graph core1708) (root 10) 0 2) DegreeTwoThreeSpectrum2918.graph fusedMap1708=true := by decide +kernel
theorem certified1708 : Certified (graph core1708) (root 10) 0 2 :=
  of_native_maps core1708 DegreeTwoThreeSpectrum3705.graph DegreeTwoThreeSpectrum2918.graph
    sourceMap1708 fusedMap1708 sourceMap1708_checked fusedMap1708_checked
    DegreeTwoThreeFiniteComparisons.comparison1708
#print axioms sourceMap1708_checked
#print axioms fusedMap1708_checked
#print axioms certified1708
def sourceMap1708swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1708swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1708swap_checked : acceptsGraphIso
    (source (graph core1708) (root 10) 2 0) DegreeTwoThreeSpectrum3705.graph sourceMap1708swap=true := by decide +kernel
theorem fusedMap1708swap_checked : acceptsGraphIso
    (fused (graph core1708) (root 10) 2 0) DegreeTwoThreeSpectrum2918.graph fusedMap1708swap=true := by decide +kernel
theorem certified1708swap : Certified (graph core1708) (root 10) 2 0 :=
  of_native_maps core1708 DegreeTwoThreeSpectrum3705.graph DegreeTwoThreeSpectrum2918.graph
    sourceMap1708swap fusedMap1708swap sourceMap1708swap_checked fusedMap1708swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1708
#print axioms sourceMap1708swap_checked
#print axioms fusedMap1708swap_checked
#print axioms certified1708swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

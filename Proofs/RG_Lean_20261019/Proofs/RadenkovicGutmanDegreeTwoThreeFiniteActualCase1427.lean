/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1427 : Family 9 := level9.get ⟨690,by decide⟩
def sourceMap1427 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 0 2 v)
def fusedMap1427 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1427_checked : acceptsGraphIso
    (source (graph core1427) (root 9) 0 2) DegreeTwoThreeSpectrum2239.graph sourceMap1427=true := by decide +kernel
theorem fusedMap1427_checked : acceptsGraphIso
    (fused (graph core1427) (root 9) 0 2) DegreeTwoThreeSpectrum2240.graph fusedMap1427=true := by decide +kernel
theorem certified1427 : Certified (graph core1427) (root 9) 0 2 :=
  of_native_maps core1427 DegreeTwoThreeSpectrum2239.graph DegreeTwoThreeSpectrum2240.graph
    sourceMap1427 fusedMap1427 sourceMap1427_checked fusedMap1427_checked
    DegreeTwoThreeFiniteComparisons.comparison1427
#print axioms sourceMap1427_checked
#print axioms fusedMap1427_checked
#print axioms certified1427
def sourceMap1427swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,10] (sourceLabel 9 2 0 v)
def fusedMap1427swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1427swap_checked : acceptsGraphIso
    (source (graph core1427) (root 9) 2 0) DegreeTwoThreeSpectrum2239.graph sourceMap1427swap=true := by decide +kernel
theorem fusedMap1427swap_checked : acceptsGraphIso
    (fused (graph core1427) (root 9) 2 0) DegreeTwoThreeSpectrum2240.graph fusedMap1427swap=true := by decide +kernel
theorem certified1427swap : Certified (graph core1427) (root 9) 2 0 :=
  of_native_maps core1427 DegreeTwoThreeSpectrum2239.graph DegreeTwoThreeSpectrum2240.graph
    sourceMap1427swap fusedMap1427swap sourceMap1427swap_checked fusedMap1427swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1427
#print axioms sourceMap1427swap_checked
#print axioms fusedMap1427swap_checked
#print axioms certified1427swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

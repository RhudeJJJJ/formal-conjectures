/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1554 : Family 10 := level10.get ⟨463,by decide⟩
def sourceMap1554 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1554 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1554_checked : acceptsGraphIso
    (source (graph core1554) (root 10) 0 2) DegreeTwoThreeSpectrum2818.graph sourceMap1554=true := by decide +kernel
theorem fusedMap1554_checked : acceptsGraphIso
    (fused (graph core1554) (root 10) 0 2) DegreeTwoThreeSpectrum2959.graph fusedMap1554=true := by decide +kernel
theorem certified1554 : Certified (graph core1554) (root 10) 0 2 :=
  of_native_maps core1554 DegreeTwoThreeSpectrum2818.graph DegreeTwoThreeSpectrum2959.graph
    sourceMap1554 fusedMap1554 sourceMap1554_checked fusedMap1554_checked
    DegreeTwoThreeFiniteComparisons.comparison1554
#print axioms sourceMap1554_checked
#print axioms fusedMap1554_checked
#print axioms certified1554
def sourceMap1554swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1554swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1554swap_checked : acceptsGraphIso
    (source (graph core1554) (root 10) 2 0) DegreeTwoThreeSpectrum2818.graph sourceMap1554swap=true := by decide +kernel
theorem fusedMap1554swap_checked : acceptsGraphIso
    (fused (graph core1554) (root 10) 2 0) DegreeTwoThreeSpectrum2959.graph fusedMap1554swap=true := by decide +kernel
theorem certified1554swap : Certified (graph core1554) (root 10) 2 0 :=
  of_native_maps core1554 DegreeTwoThreeSpectrum2818.graph DegreeTwoThreeSpectrum2959.graph
    sourceMap1554swap fusedMap1554swap sourceMap1554swap_checked fusedMap1554swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1554
#print axioms sourceMap1554swap_checked
#print axioms fusedMap1554swap_checked
#print axioms certified1554swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

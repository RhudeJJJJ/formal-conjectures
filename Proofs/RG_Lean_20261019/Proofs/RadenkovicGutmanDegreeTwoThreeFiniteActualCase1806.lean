/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1806 : Family 10 := level10.get ⟨1152,by decide⟩
def sourceMap1806 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1806 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1806_checked : acceptsGraphIso
    (source (graph core1806) (root 10) 0 2) DegreeTwoThreeSpectrum3246.graph sourceMap1806=true := by decide +kernel
theorem fusedMap1806_checked : acceptsGraphIso
    (fused (graph core1806) (root 10) 0 2) DegreeTwoThreeSpectrum3247.graph fusedMap1806=true := by decide +kernel
theorem certified1806 : Certified (graph core1806) (root 10) 0 2 :=
  of_native_maps core1806 DegreeTwoThreeSpectrum3246.graph DegreeTwoThreeSpectrum3247.graph
    sourceMap1806 fusedMap1806 sourceMap1806_checked fusedMap1806_checked
    DegreeTwoThreeFiniteComparisons.comparison1806
#print axioms sourceMap1806_checked
#print axioms fusedMap1806_checked
#print axioms certified1806
def sourceMap1806swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1806swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1806swap_checked : acceptsGraphIso
    (source (graph core1806) (root 10) 2 0) DegreeTwoThreeSpectrum3246.graph sourceMap1806swap=true := by decide +kernel
theorem fusedMap1806swap_checked : acceptsGraphIso
    (fused (graph core1806) (root 10) 2 0) DegreeTwoThreeSpectrum3247.graph fusedMap1806swap=true := by decide +kernel
theorem certified1806swap : Certified (graph core1806) (root 10) 2 0 :=
  of_native_maps core1806 DegreeTwoThreeSpectrum3246.graph DegreeTwoThreeSpectrum3247.graph
    sourceMap1806swap fusedMap1806swap sourceMap1806swap_checked fusedMap1806swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1806
#print axioms sourceMap1806swap_checked
#print axioms fusedMap1806swap_checked
#print axioms certified1806swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1530 : Family 10 := level10.get ⟨393,by decide⟩
def sourceMap1530 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1530 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1530_checked : acceptsGraphIso
    (source (graph core1530) (root 10) 0 2) DegreeTwoThreeSpectrum2876.graph sourceMap1530=true := by decide +kernel
theorem fusedMap1530_checked : acceptsGraphIso
    (fused (graph core1530) (root 10) 0 2) DegreeTwoThreeSpectrum2878.graph fusedMap1530=true := by decide +kernel
theorem certified1530 : Certified (graph core1530) (root 10) 0 2 :=
  of_native_maps core1530 DegreeTwoThreeSpectrum2876.graph DegreeTwoThreeSpectrum2878.graph
    sourceMap1530 fusedMap1530 sourceMap1530_checked fusedMap1530_checked
    DegreeTwoThreeFiniteComparisons.comparison1530
#print axioms sourceMap1530_checked
#print axioms fusedMap1530_checked
#print axioms certified1530
def sourceMap1530swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1530swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1530swap_checked : acceptsGraphIso
    (source (graph core1530) (root 10) 2 0) DegreeTwoThreeSpectrum2876.graph sourceMap1530swap=true := by decide +kernel
theorem fusedMap1530swap_checked : acceptsGraphIso
    (fused (graph core1530) (root 10) 2 0) DegreeTwoThreeSpectrum2878.graph fusedMap1530swap=true := by decide +kernel
theorem certified1530swap : Certified (graph core1530) (root 10) 2 0 :=
  of_native_maps core1530 DegreeTwoThreeSpectrum2876.graph DegreeTwoThreeSpectrum2878.graph
    sourceMap1530swap fusedMap1530swap sourceMap1530swap_checked fusedMap1530swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1530
#print axioms sourceMap1530swap_checked
#print axioms fusedMap1530swap_checked
#print axioms certified1530swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

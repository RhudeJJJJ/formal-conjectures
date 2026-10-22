/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1473 : Family 10 := level10.get ⟨186,by decide⟩
def sourceMap1473 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,6,7,8,9,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1473 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1473_checked : acceptsGraphIso
    (source (graph core1473) (root 10) 0 2) DegreeTwoThreeSpectrum2834.graph sourceMap1473=true := by decide +kernel
theorem fusedMap1473_checked : acceptsGraphIso
    (fused (graph core1473) (root 10) 0 2) DegreeTwoThreeSpectrum2409.graph fusedMap1473=true := by decide +kernel
theorem certified1473 : Certified (graph core1473) (root 10) 0 2 :=
  of_native_maps core1473 DegreeTwoThreeSpectrum2834.graph DegreeTwoThreeSpectrum2409.graph
    sourceMap1473 fusedMap1473 sourceMap1473_checked fusedMap1473_checked
    DegreeTwoThreeFiniteComparisons.comparison1473
#print axioms sourceMap1473_checked
#print axioms fusedMap1473_checked
#print axioms certified1473
def sourceMap1473swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,6,7,8,3,4,5,9] (sourceLabel 10 2 0 v)
def fusedMap1473swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1473swap_checked : acceptsGraphIso
    (source (graph core1473) (root 10) 2 0) DegreeTwoThreeSpectrum2834.graph sourceMap1473swap=true := by decide +kernel
theorem fusedMap1473swap_checked : acceptsGraphIso
    (fused (graph core1473) (root 10) 2 0) DegreeTwoThreeSpectrum2409.graph fusedMap1473swap=true := by decide +kernel
theorem certified1473swap : Certified (graph core1473) (root 10) 2 0 :=
  of_native_maps core1473 DegreeTwoThreeSpectrum2834.graph DegreeTwoThreeSpectrum2409.graph
    sourceMap1473swap fusedMap1473swap sourceMap1473swap_checked fusedMap1473swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1473
#print axioms sourceMap1473swap_checked
#print axioms fusedMap1473swap_checked
#print axioms certified1473swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1738 : Family 10 := level10.get ⟨970,by decide⟩
def sourceMap1738 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,5,6,7,8,9,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1738 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,5,6,7,8,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1738_checked : acceptsGraphIso
    (source (graph core1738) (root 10) 0 2) DegreeTwoThreeSpectrum3645.graph sourceMap1738=true := by decide +kernel
theorem fusedMap1738_checked : acceptsGraphIso
    (fused (graph core1738) (root 10) 0 2) DegreeTwoThreeSpectrum2963.graph fusedMap1738=true := by decide +kernel
theorem certified1738 : Certified (graph core1738) (root 10) 0 2 :=
  of_native_maps core1738 DegreeTwoThreeSpectrum3645.graph DegreeTwoThreeSpectrum2963.graph
    sourceMap1738 fusedMap1738 sourceMap1738_checked fusedMap1738_checked
    DegreeTwoThreeFiniteComparisons.comparison1738
#print axioms sourceMap1738_checked
#print axioms fusedMap1738_checked
#print axioms certified1738
def sourceMap1738swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,5,6,7,8,2,3,4,9] (sourceLabel 10 2 0 v)
def fusedMap1738swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,5,6,7,8,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1738swap_checked : acceptsGraphIso
    (source (graph core1738) (root 10) 2 0) DegreeTwoThreeSpectrum3645.graph sourceMap1738swap=true := by decide +kernel
theorem fusedMap1738swap_checked : acceptsGraphIso
    (fused (graph core1738) (root 10) 2 0) DegreeTwoThreeSpectrum2963.graph fusedMap1738swap=true := by decide +kernel
theorem certified1738swap : Certified (graph core1738) (root 10) 2 0 :=
  of_native_maps core1738 DegreeTwoThreeSpectrum3645.graph DegreeTwoThreeSpectrum2963.graph
    sourceMap1738swap fusedMap1738swap sourceMap1738swap_checked fusedMap1738swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1738
#print axioms sourceMap1738swap_checked
#print axioms fusedMap1738swap_checked
#print axioms certified1738swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1546 : Family 10 := level10.get ⟨444,by decide⟩
def sourceMap1546 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1546 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1546_checked : acceptsGraphIso
    (source (graph core1546) (root 10) 0 2) DegreeTwoThreeSpectrum2892.graph sourceMap1546=true := by decide +kernel
theorem fusedMap1546_checked : acceptsGraphIso
    (fused (graph core1546) (root 10) 0 2) DegreeTwoThreeSpectrum2980.graph fusedMap1546=true := by decide +kernel
theorem certified1546 : Certified (graph core1546) (root 10) 0 2 :=
  of_native_maps core1546 DegreeTwoThreeSpectrum2892.graph DegreeTwoThreeSpectrum2980.graph
    sourceMap1546 fusedMap1546 sourceMap1546_checked fusedMap1546_checked
    DegreeTwoThreeFiniteComparisons.comparison1546
#print axioms sourceMap1546_checked
#print axioms fusedMap1546_checked
#print axioms certified1546
def sourceMap1546swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1546swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1546swap_checked : acceptsGraphIso
    (source (graph core1546) (root 10) 2 0) DegreeTwoThreeSpectrum2892.graph sourceMap1546swap=true := by decide +kernel
theorem fusedMap1546swap_checked : acceptsGraphIso
    (fused (graph core1546) (root 10) 2 0) DegreeTwoThreeSpectrum2980.graph fusedMap1546swap=true := by decide +kernel
theorem certified1546swap : Certified (graph core1546) (root 10) 2 0 :=
  of_native_maps core1546 DegreeTwoThreeSpectrum2892.graph DegreeTwoThreeSpectrum2980.graph
    sourceMap1546swap fusedMap1546swap sourceMap1546swap_checked fusedMap1546swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1546
#print axioms sourceMap1546swap_checked
#print axioms fusedMap1546swap_checked
#print axioms certified1546swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

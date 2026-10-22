/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1529 : Family 10 := level10.get ⟨388,by decide⟩
def sourceMap1529 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1529 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1529_checked : acceptsGraphIso
    (source (graph core1529) (root 10) 0 2) DegreeTwoThreeSpectrum2849.graph sourceMap1529=true := by decide +kernel
theorem fusedMap1529_checked : acceptsGraphIso
    (fused (graph core1529) (root 10) 0 2) DegreeTwoThreeSpectrum2869.graph fusedMap1529=true := by decide +kernel
theorem certified1529 : Certified (graph core1529) (root 10) 0 2 :=
  of_native_maps core1529 DegreeTwoThreeSpectrum2849.graph DegreeTwoThreeSpectrum2869.graph
    sourceMap1529 fusedMap1529 sourceMap1529_checked fusedMap1529_checked
    DegreeTwoThreeFiniteComparisons.comparison1529
#print axioms sourceMap1529_checked
#print axioms fusedMap1529_checked
#print axioms certified1529
def sourceMap1529swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1529swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1529swap_checked : acceptsGraphIso
    (source (graph core1529) (root 10) 2 0) DegreeTwoThreeSpectrum2849.graph sourceMap1529swap=true := by decide +kernel
theorem fusedMap1529swap_checked : acceptsGraphIso
    (fused (graph core1529) (root 10) 2 0) DegreeTwoThreeSpectrum2869.graph fusedMap1529swap=true := by decide +kernel
theorem certified1529swap : Certified (graph core1529) (root 10) 2 0 :=
  of_native_maps core1529 DegreeTwoThreeSpectrum2849.graph DegreeTwoThreeSpectrum2869.graph
    sourceMap1529swap fusedMap1529swap sourceMap1529swap_checked fusedMap1529swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1529
#print axioms sourceMap1529swap_checked
#print axioms fusedMap1529swap_checked
#print axioms certified1529swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

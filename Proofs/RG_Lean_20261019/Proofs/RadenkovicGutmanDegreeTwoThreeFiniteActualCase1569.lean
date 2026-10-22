/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1569 : Family 10 := level10.get ⟨506,by decide⟩
def sourceMap1569 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1569 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1569_checked : acceptsGraphIso
    (source (graph core1569) (root 10) 0 2) DegreeTwoThreeSpectrum3039.graph sourceMap1569=true := by decide +kernel
theorem fusedMap1569_checked : acceptsGraphIso
    (fused (graph core1569) (root 10) 0 2) DegreeTwoThreeSpectrum2443.graph fusedMap1569=true := by decide +kernel
theorem certified1569 : Certified (graph core1569) (root 10) 0 2 :=
  of_native_maps core1569 DegreeTwoThreeSpectrum3039.graph DegreeTwoThreeSpectrum2443.graph
    sourceMap1569 fusedMap1569 sourceMap1569_checked fusedMap1569_checked
    DegreeTwoThreeFiniteComparisons.comparison1569
#print axioms sourceMap1569_checked
#print axioms fusedMap1569_checked
#print axioms certified1569
def sourceMap1569swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1569swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1569swap_checked : acceptsGraphIso
    (source (graph core1569) (root 10) 2 0) DegreeTwoThreeSpectrum3039.graph sourceMap1569swap=true := by decide +kernel
theorem fusedMap1569swap_checked : acceptsGraphIso
    (fused (graph core1569) (root 10) 2 0) DegreeTwoThreeSpectrum2443.graph fusedMap1569swap=true := by decide +kernel
theorem certified1569swap : Certified (graph core1569) (root 10) 2 0 :=
  of_native_maps core1569 DegreeTwoThreeSpectrum3039.graph DegreeTwoThreeSpectrum2443.graph
    sourceMap1569swap fusedMap1569swap sourceMap1569swap_checked fusedMap1569swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1569
#print axioms sourceMap1569swap_checked
#print axioms fusedMap1569swap_checked
#print axioms certified1569swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1451 : Family 10 := level10.get ⟨113,by decide⟩
def sourceMap1451 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1451 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1451_checked : acceptsGraphIso
    (source (graph core1451) (root 10) 0 2) DegreeTwoThreeSpectrum2803.graph sourceMap1451=true := by decide +kernel
theorem fusedMap1451_checked : acceptsGraphIso
    (fused (graph core1451) (root 10) 0 2) DegreeTwoThreeSpectrum2373.graph fusedMap1451=true := by decide +kernel
theorem certified1451 : Certified (graph core1451) (root 10) 0 2 :=
  of_native_maps core1451 DegreeTwoThreeSpectrum2803.graph DegreeTwoThreeSpectrum2373.graph
    sourceMap1451 fusedMap1451 sourceMap1451_checked fusedMap1451_checked
    DegreeTwoThreeFiniteComparisons.comparison1451
#print axioms sourceMap1451_checked
#print axioms fusedMap1451_checked
#print axioms certified1451
def sourceMap1451swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1451swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1451swap_checked : acceptsGraphIso
    (source (graph core1451) (root 10) 2 0) DegreeTwoThreeSpectrum2803.graph sourceMap1451swap=true := by decide +kernel
theorem fusedMap1451swap_checked : acceptsGraphIso
    (fused (graph core1451) (root 10) 2 0) DegreeTwoThreeSpectrum2373.graph fusedMap1451swap=true := by decide +kernel
theorem certified1451swap : Certified (graph core1451) (root 10) 2 0 :=
  of_native_maps core1451 DegreeTwoThreeSpectrum2803.graph DegreeTwoThreeSpectrum2373.graph
    sourceMap1451swap fusedMap1451swap sourceMap1451swap_checked fusedMap1451swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1451
#print axioms sourceMap1451swap_checked
#print axioms fusedMap1451swap_checked
#print axioms certified1451swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

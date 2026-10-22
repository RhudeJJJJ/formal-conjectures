/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1532 : Family 10 := level10.get ⟨400,by decide⟩
def sourceMap1532 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1532 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1532_checked : acceptsGraphIso
    (source (graph core1532) (root 10) 0 2) DegreeTwoThreeSpectrum2889.graph sourceMap1532=true := by decide +kernel
theorem fusedMap1532_checked : acceptsGraphIso
    (fused (graph core1532) (root 10) 0 2) DegreeTwoThreeSpectrum2907.graph fusedMap1532=true := by decide +kernel
theorem certified1532 : Certified (graph core1532) (root 10) 0 2 :=
  of_native_maps core1532 DegreeTwoThreeSpectrum2889.graph DegreeTwoThreeSpectrum2907.graph
    sourceMap1532 fusedMap1532 sourceMap1532_checked fusedMap1532_checked
    DegreeTwoThreeFiniteComparisons.comparison1532
#print axioms sourceMap1532_checked
#print axioms fusedMap1532_checked
#print axioms certified1532
def sourceMap1532swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1532swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1532swap_checked : acceptsGraphIso
    (source (graph core1532) (root 10) 2 0) DegreeTwoThreeSpectrum2889.graph sourceMap1532swap=true := by decide +kernel
theorem fusedMap1532swap_checked : acceptsGraphIso
    (fused (graph core1532) (root 10) 2 0) DegreeTwoThreeSpectrum2907.graph fusedMap1532swap=true := by decide +kernel
theorem certified1532swap : Certified (graph core1532) (root 10) 2 0 :=
  of_native_maps core1532 DegreeTwoThreeSpectrum2889.graph DegreeTwoThreeSpectrum2907.graph
    sourceMap1532swap fusedMap1532swap sourceMap1532swap_checked fusedMap1532swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1532
#print axioms sourceMap1532swap_checked
#print axioms fusedMap1532swap_checked
#print axioms certified1532swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

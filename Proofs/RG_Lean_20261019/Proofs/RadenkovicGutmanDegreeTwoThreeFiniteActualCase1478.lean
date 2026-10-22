/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1478 : Family 10 := level10.get ⟨212,by decide⟩
def sourceMap1478 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1478 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1478_checked : acceptsGraphIso
    (source (graph core1478) (root 10) 0 2) DegreeTwoThreeSpectrum2495.graph sourceMap1478=true := by decide +kernel
theorem fusedMap1478_checked : acceptsGraphIso
    (fused (graph core1478) (root 10) 0 2) DegreeTwoThreeSpectrum2500.graph fusedMap1478=true := by decide +kernel
theorem certified1478 : Certified (graph core1478) (root 10) 0 2 :=
  of_native_maps core1478 DegreeTwoThreeSpectrum2495.graph DegreeTwoThreeSpectrum2500.graph
    sourceMap1478 fusedMap1478 sourceMap1478_checked fusedMap1478_checked
    DegreeTwoThreeFiniteComparisons.comparison1478
#print axioms sourceMap1478_checked
#print axioms fusedMap1478_checked
#print axioms certified1478
def sourceMap1478swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1478swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1478swap_checked : acceptsGraphIso
    (source (graph core1478) (root 10) 2 0) DegreeTwoThreeSpectrum2495.graph sourceMap1478swap=true := by decide +kernel
theorem fusedMap1478swap_checked : acceptsGraphIso
    (fused (graph core1478) (root 10) 2 0) DegreeTwoThreeSpectrum2500.graph fusedMap1478swap=true := by decide +kernel
theorem certified1478swap : Certified (graph core1478) (root 10) 2 0 :=
  of_native_maps core1478 DegreeTwoThreeSpectrum2495.graph DegreeTwoThreeSpectrum2500.graph
    sourceMap1478swap fusedMap1478swap sourceMap1478swap_checked fusedMap1478swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1478
#print axioms sourceMap1478swap_checked
#print axioms fusedMap1478swap_checked
#print axioms certified1478swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

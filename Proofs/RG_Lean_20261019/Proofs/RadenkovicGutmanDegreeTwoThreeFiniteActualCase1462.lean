/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1462 : Family 10 := level10.get ⟨158,by decide⟩
def sourceMap1462 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1462 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1462_checked : acceptsGraphIso
    (source (graph core1462) (root 10) 0 2) DegreeTwoThreeSpectrum2907.graph sourceMap1462=true := by decide +kernel
theorem fusedMap1462_checked : acceptsGraphIso
    (fused (graph core1462) (root 10) 0 2) DegreeTwoThreeSpectrum2420.graph fusedMap1462=true := by decide +kernel
theorem certified1462 : Certified (graph core1462) (root 10) 0 2 :=
  of_native_maps core1462 DegreeTwoThreeSpectrum2907.graph DegreeTwoThreeSpectrum2420.graph
    sourceMap1462 fusedMap1462 sourceMap1462_checked fusedMap1462_checked
    DegreeTwoThreeFiniteComparisons.comparison1462
#print axioms sourceMap1462_checked
#print axioms fusedMap1462_checked
#print axioms certified1462
def sourceMap1462swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1462swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1462swap_checked : acceptsGraphIso
    (source (graph core1462) (root 10) 2 0) DegreeTwoThreeSpectrum2907.graph sourceMap1462swap=true := by decide +kernel
theorem fusedMap1462swap_checked : acceptsGraphIso
    (fused (graph core1462) (root 10) 2 0) DegreeTwoThreeSpectrum2420.graph fusedMap1462swap=true := by decide +kernel
theorem certified1462swap : Certified (graph core1462) (root 10) 2 0 :=
  of_native_maps core1462 DegreeTwoThreeSpectrum2907.graph DegreeTwoThreeSpectrum2420.graph
    sourceMap1462swap fusedMap1462swap sourceMap1462swap_checked fusedMap1462swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1462
#print axioms sourceMap1462swap_checked
#print axioms fusedMap1462swap_checked
#print axioms certified1462swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

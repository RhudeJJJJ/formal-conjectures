/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1539 : Family 10 := level10.get ⟨421,by decide⟩
def sourceMap1539 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1539 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1539_checked : acceptsGraphIso
    (source (graph core1539) (root 10) 0 2) DegreeTwoThreeSpectrum2886.graph sourceMap1539=true := by decide +kernel
theorem fusedMap1539_checked : acceptsGraphIso
    (fused (graph core1539) (root 10) 0 2) DegreeTwoThreeSpectrum2939.graph fusedMap1539=true := by decide +kernel
theorem certified1539 : Certified (graph core1539) (root 10) 0 2 :=
  of_native_maps core1539 DegreeTwoThreeSpectrum2886.graph DegreeTwoThreeSpectrum2939.graph
    sourceMap1539 fusedMap1539 sourceMap1539_checked fusedMap1539_checked
    DegreeTwoThreeFiniteComparisons.comparison1539
#print axioms sourceMap1539_checked
#print axioms fusedMap1539_checked
#print axioms certified1539
def sourceMap1539swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1539swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1539swap_checked : acceptsGraphIso
    (source (graph core1539) (root 10) 2 0) DegreeTwoThreeSpectrum2886.graph sourceMap1539swap=true := by decide +kernel
theorem fusedMap1539swap_checked : acceptsGraphIso
    (fused (graph core1539) (root 10) 2 0) DegreeTwoThreeSpectrum2939.graph fusedMap1539swap=true := by decide +kernel
theorem certified1539swap : Certified (graph core1539) (root 10) 2 0 :=
  of_native_maps core1539 DegreeTwoThreeSpectrum2886.graph DegreeTwoThreeSpectrum2939.graph
    sourceMap1539swap fusedMap1539swap sourceMap1539swap_checked fusedMap1539swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1539
#print axioms sourceMap1539swap_checked
#print axioms fusedMap1539swap_checked
#print axioms certified1539swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

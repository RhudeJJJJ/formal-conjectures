/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1406 : Family 9 := level9.get ⟨609,by decide⟩
def sourceMap1406 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1406 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1406_checked : acceptsGraphIso
    (source (graph core1406) (root 9) 0 2) DegreeTwoThreeSpectrum2278.graph sourceMap1406=true := by decide +kernel
theorem fusedMap1406_checked : acceptsGraphIso
    (fused (graph core1406) (root 9) 0 2) DegreeTwoThreeSpectrum2020.graph fusedMap1406=true := by decide +kernel
theorem certified1406 : Certified (graph core1406) (root 9) 0 2 :=
  of_native_maps core1406 DegreeTwoThreeSpectrum2278.graph DegreeTwoThreeSpectrum2020.graph
    sourceMap1406 fusedMap1406 sourceMap1406_checked fusedMap1406_checked
    DegreeTwoThreeFiniteComparisons.comparison1406
#print axioms sourceMap1406_checked
#print axioms fusedMap1406_checked
#print axioms certified1406
def sourceMap1406swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1406swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1406swap_checked : acceptsGraphIso
    (source (graph core1406) (root 9) 2 0) DegreeTwoThreeSpectrum2278.graph sourceMap1406swap=true := by decide +kernel
theorem fusedMap1406swap_checked : acceptsGraphIso
    (fused (graph core1406) (root 9) 2 0) DegreeTwoThreeSpectrum2020.graph fusedMap1406swap=true := by decide +kernel
theorem certified1406swap : Certified (graph core1406) (root 9) 2 0 :=
  of_native_maps core1406 DegreeTwoThreeSpectrum2278.graph DegreeTwoThreeSpectrum2020.graph
    sourceMap1406swap fusedMap1406swap sourceMap1406swap_checked fusedMap1406swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1406
#print axioms sourceMap1406swap_checked
#print axioms fusedMap1406swap_checked
#print axioms certified1406swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

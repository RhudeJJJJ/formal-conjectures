/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1348 : Family 9 := level9.get ⟨474,by decide⟩
def sourceMap1348 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1348 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1348_checked : acceptsGraphIso
    (source (graph core1348) (root 9) 0 2) DegreeTwoThreeSpectrum2162.graph sourceMap1348=true := by decide +kernel
theorem fusedMap1348_checked : acceptsGraphIso
    (fused (graph core1348) (root 9) 0 2) DegreeTwoThreeSpectrum2166.graph fusedMap1348=true := by decide +kernel
theorem certified1348 : Certified (graph core1348) (root 9) 0 2 :=
  of_native_maps core1348 DegreeTwoThreeSpectrum2162.graph DegreeTwoThreeSpectrum2166.graph
    sourceMap1348 fusedMap1348 sourceMap1348_checked fusedMap1348_checked
    DegreeTwoThreeFiniteComparisons.comparison1348
#print axioms sourceMap1348_checked
#print axioms fusedMap1348_checked
#print axioms certified1348
def sourceMap1348swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1348swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1348swap_checked : acceptsGraphIso
    (source (graph core1348) (root 9) 2 0) DegreeTwoThreeSpectrum2162.graph sourceMap1348swap=true := by decide +kernel
theorem fusedMap1348swap_checked : acceptsGraphIso
    (fused (graph core1348) (root 9) 2 0) DegreeTwoThreeSpectrum2166.graph fusedMap1348swap=true := by decide +kernel
theorem certified1348swap : Certified (graph core1348) (root 9) 2 0 :=
  of_native_maps core1348 DegreeTwoThreeSpectrum2162.graph DegreeTwoThreeSpectrum2166.graph
    sourceMap1348swap fusedMap1348swap sourceMap1348swap_checked fusedMap1348swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1348
#print axioms sourceMap1348swap_checked
#print axioms fusedMap1348swap_checked
#print axioms certified1348swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

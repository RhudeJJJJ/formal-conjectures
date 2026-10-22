/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1410 : Family 9 := level9.get ⟨622,by decide⟩
def sourceMap1410 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1410 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1410_checked : acceptsGraphIso
    (source (graph core1410) (root 9) 0 2) DegreeTwoThreeSpectrum2285.graph sourceMap1410=true := by decide +kernel
theorem fusedMap1410_checked : acceptsGraphIso
    (fused (graph core1410) (root 9) 0 2) DegreeTwoThreeSpectrum2045.graph fusedMap1410=true := by decide +kernel
theorem certified1410 : Certified (graph core1410) (root 9) 0 2 :=
  of_native_maps core1410 DegreeTwoThreeSpectrum2285.graph DegreeTwoThreeSpectrum2045.graph
    sourceMap1410 fusedMap1410 sourceMap1410_checked fusedMap1410_checked
    DegreeTwoThreeFiniteComparisons.comparison1410
#print axioms sourceMap1410_checked
#print axioms fusedMap1410_checked
#print axioms certified1410
def sourceMap1410swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,5,6,7,13] (sourceLabel 9 2 0 v)
def fusedMap1410swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1410swap_checked : acceptsGraphIso
    (source (graph core1410) (root 9) 2 0) DegreeTwoThreeSpectrum2285.graph sourceMap1410swap=true := by decide +kernel
theorem fusedMap1410swap_checked : acceptsGraphIso
    (fused (graph core1410) (root 9) 2 0) DegreeTwoThreeSpectrum2045.graph fusedMap1410swap=true := by decide +kernel
theorem certified1410swap : Certified (graph core1410) (root 9) 2 0 :=
  of_native_maps core1410 DegreeTwoThreeSpectrum2285.graph DegreeTwoThreeSpectrum2045.graph
    sourceMap1410swap fusedMap1410swap sourceMap1410swap_checked fusedMap1410swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1410
#print axioms sourceMap1410swap_checked
#print axioms fusedMap1410swap_checked
#print axioms certified1410swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

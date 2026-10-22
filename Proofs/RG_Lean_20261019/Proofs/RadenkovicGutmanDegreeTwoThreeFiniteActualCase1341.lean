/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1341 : Family 9 := level9.get ⟨460,by decide⟩
def sourceMap1341 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1341 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1341_checked : acceptsGraphIso
    (source (graph core1341) (root 9) 0 2) DegreeTwoThreeSpectrum2144.graph sourceMap1341=true := by decide +kernel
theorem fusedMap1341_checked : acceptsGraphIso
    (fused (graph core1341) (root 9) 0 2) DegreeTwoThreeSpectrum2145.graph fusedMap1341=true := by decide +kernel
theorem certified1341 : Certified (graph core1341) (root 9) 0 2 :=
  of_native_maps core1341 DegreeTwoThreeSpectrum2144.graph DegreeTwoThreeSpectrum2145.graph
    sourceMap1341 fusedMap1341 sourceMap1341_checked fusedMap1341_checked
    DegreeTwoThreeFiniteComparisons.comparison1341
#print axioms sourceMap1341_checked
#print axioms fusedMap1341_checked
#print axioms certified1341
def sourceMap1341swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1341swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1341swap_checked : acceptsGraphIso
    (source (graph core1341) (root 9) 2 0) DegreeTwoThreeSpectrum2144.graph sourceMap1341swap=true := by decide +kernel
theorem fusedMap1341swap_checked : acceptsGraphIso
    (fused (graph core1341) (root 9) 2 0) DegreeTwoThreeSpectrum2145.graph fusedMap1341swap=true := by decide +kernel
theorem certified1341swap : Certified (graph core1341) (root 9) 2 0 :=
  of_native_maps core1341 DegreeTwoThreeSpectrum2144.graph DegreeTwoThreeSpectrum2145.graph
    sourceMap1341swap fusedMap1341swap sourceMap1341swap_checked fusedMap1341swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1341
#print axioms sourceMap1341swap_checked
#print axioms fusedMap1341swap_checked
#print axioms certified1341swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

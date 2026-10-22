/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1332 : Family 9 := level9.get ⟨435,by decide⟩
def sourceMap1332 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1332 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1332_checked : acceptsGraphIso
    (source (graph core1332) (root 9) 0 2) DegreeTwoThreeSpectrum2107.graph sourceMap1332=true := by decide +kernel
theorem fusedMap1332_checked : acceptsGraphIso
    (fused (graph core1332) (root 9) 0 2) DegreeTwoThreeSpectrum2111.graph fusedMap1332=true := by decide +kernel
theorem certified1332 : Certified (graph core1332) (root 9) 0 2 :=
  of_native_maps core1332 DegreeTwoThreeSpectrum2107.graph DegreeTwoThreeSpectrum2111.graph
    sourceMap1332 fusedMap1332 sourceMap1332_checked fusedMap1332_checked
    DegreeTwoThreeFiniteComparisons.comparison1332
#print axioms sourceMap1332_checked
#print axioms fusedMap1332_checked
#print axioms certified1332
def sourceMap1332swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1332swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1332swap_checked : acceptsGraphIso
    (source (graph core1332) (root 9) 2 0) DegreeTwoThreeSpectrum2107.graph sourceMap1332swap=true := by decide +kernel
theorem fusedMap1332swap_checked : acceptsGraphIso
    (fused (graph core1332) (root 9) 2 0) DegreeTwoThreeSpectrum2111.graph fusedMap1332swap=true := by decide +kernel
theorem certified1332swap : Certified (graph core1332) (root 9) 2 0 :=
  of_native_maps core1332 DegreeTwoThreeSpectrum2107.graph DegreeTwoThreeSpectrum2111.graph
    sourceMap1332swap fusedMap1332swap sourceMap1332swap_checked fusedMap1332swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1332
#print axioms sourceMap1332swap_checked
#print axioms fusedMap1332swap_checked
#print axioms certified1332swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

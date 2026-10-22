/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1325 : Family 9 := level9.get ⟨420,by decide⟩
def sourceMap1325 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1325 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1325_checked : acceptsGraphIso
    (source (graph core1325) (root 9) 0 2) DegreeTwoThreeSpectrum2085.graph sourceMap1325=true := by decide +kernel
theorem fusedMap1325_checked : acceptsGraphIso
    (fused (graph core1325) (root 9) 0 2) DegreeTwoThreeSpectrum2086.graph fusedMap1325=true := by decide +kernel
theorem certified1325 : Certified (graph core1325) (root 9) 0 2 :=
  of_native_maps core1325 DegreeTwoThreeSpectrum2085.graph DegreeTwoThreeSpectrum2086.graph
    sourceMap1325 fusedMap1325 sourceMap1325_checked fusedMap1325_checked
    DegreeTwoThreeFiniteComparisons.comparison1325
#print axioms sourceMap1325_checked
#print axioms fusedMap1325_checked
#print axioms certified1325
def sourceMap1325swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1325swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1325swap_checked : acceptsGraphIso
    (source (graph core1325) (root 9) 2 0) DegreeTwoThreeSpectrum2085.graph sourceMap1325swap=true := by decide +kernel
theorem fusedMap1325swap_checked : acceptsGraphIso
    (fused (graph core1325) (root 9) 2 0) DegreeTwoThreeSpectrum2086.graph fusedMap1325swap=true := by decide +kernel
theorem certified1325swap : Certified (graph core1325) (root 9) 2 0 :=
  of_native_maps core1325 DegreeTwoThreeSpectrum2085.graph DegreeTwoThreeSpectrum2086.graph
    sourceMap1325swap fusedMap1325swap sourceMap1325swap_checked fusedMap1325swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1325
#print axioms sourceMap1325swap_checked
#print axioms fusedMap1325swap_checked
#print axioms certified1325swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

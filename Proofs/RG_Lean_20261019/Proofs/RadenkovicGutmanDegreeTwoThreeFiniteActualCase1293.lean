/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1293 : Family 9 := level9.get ⟨339,by decide⟩
def sourceMap1293 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1293 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1293_checked : acceptsGraphIso
    (source (graph core1293) (root 9) 0 2) DegreeTwoThreeSpectrum1964.graph sourceMap1293=true := by decide +kernel
theorem fusedMap1293_checked : acceptsGraphIso
    (fused (graph core1293) (root 9) 0 2) DegreeTwoThreeSpectrum1965.graph fusedMap1293=true := by decide +kernel
theorem certified1293 : Certified (graph core1293) (root 9) 0 2 :=
  of_native_maps core1293 DegreeTwoThreeSpectrum1964.graph DegreeTwoThreeSpectrum1965.graph
    sourceMap1293 fusedMap1293 sourceMap1293_checked fusedMap1293_checked
    DegreeTwoThreeFiniteComparisons.comparison1293
#print axioms sourceMap1293_checked
#print axioms fusedMap1293_checked
#print axioms certified1293
def sourceMap1293swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1293swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1293swap_checked : acceptsGraphIso
    (source (graph core1293) (root 9) 2 0) DegreeTwoThreeSpectrum1964.graph sourceMap1293swap=true := by decide +kernel
theorem fusedMap1293swap_checked : acceptsGraphIso
    (fused (graph core1293) (root 9) 2 0) DegreeTwoThreeSpectrum1965.graph fusedMap1293swap=true := by decide +kernel
theorem certified1293swap : Certified (graph core1293) (root 9) 2 0 :=
  of_native_maps core1293 DegreeTwoThreeSpectrum1964.graph DegreeTwoThreeSpectrum1965.graph
    sourceMap1293swap fusedMap1293swap sourceMap1293swap_checked fusedMap1293swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1293
#print axioms sourceMap1293swap_checked
#print axioms fusedMap1293swap_checked
#print axioms certified1293swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

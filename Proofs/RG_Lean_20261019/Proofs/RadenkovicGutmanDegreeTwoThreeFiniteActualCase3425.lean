/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3425 : Family 9 := level9.get ⟨555,by decide⟩
def sourceMap3425 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3425 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3425_checked : acceptsGraphIso
    (source (graph core3425) (root 9) 0 5) DegreeTwoThreeSpectrum6012.graph sourceMap3425=true := by decide +kernel
theorem fusedMap3425_checked : acceptsGraphIso
    (fused (graph core3425) (root 9) 0 5) DegreeTwoThreeSpectrum6013.graph fusedMap3425=true := by decide +kernel
theorem certified3425 : Certified (graph core3425) (root 9) 0 5 :=
  of_native_maps core3425 DegreeTwoThreeSpectrum6012.graph DegreeTwoThreeSpectrum6013.graph
    sourceMap3425 fusedMap3425 sourceMap3425_checked fusedMap3425_checked
    DegreeTwoThreeFiniteComparisons.comparison3425
#print axioms sourceMap3425_checked
#print axioms fusedMap3425_checked
#print axioms certified3425
def sourceMap3425swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3425swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3425swap_checked : acceptsGraphIso
    (source (graph core3425) (root 9) 5 0) DegreeTwoThreeSpectrum6012.graph sourceMap3425swap=true := by decide +kernel
theorem fusedMap3425swap_checked : acceptsGraphIso
    (fused (graph core3425) (root 9) 5 0) DegreeTwoThreeSpectrum6013.graph fusedMap3425swap=true := by decide +kernel
theorem certified3425swap : Certified (graph core3425) (root 9) 5 0 :=
  of_native_maps core3425 DegreeTwoThreeSpectrum6012.graph DegreeTwoThreeSpectrum6013.graph
    sourceMap3425swap fusedMap3425swap sourceMap3425swap_checked fusedMap3425swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3425
#print axioms sourceMap3425swap_checked
#print axioms fusedMap3425swap_checked
#print axioms certified3425swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3414 : Family 9 := level9.get ⟨521,by decide⟩
def sourceMap3414 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3414 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3414_checked : acceptsGraphIso
    (source (graph core3414) (root 9) 0 5) DegreeTwoThreeSpectrum6979.graph sourceMap3414=true := by decide +kernel
theorem fusedMap3414_checked : acceptsGraphIso
    (fused (graph core3414) (root 9) 0 5) DegreeTwoThreeSpectrum5766.graph fusedMap3414=true := by decide +kernel
theorem certified3414 : Certified (graph core3414) (root 9) 0 5 :=
  of_native_maps core3414 DegreeTwoThreeSpectrum6979.graph DegreeTwoThreeSpectrum5766.graph
    sourceMap3414 fusedMap3414 sourceMap3414_checked fusedMap3414_checked
    DegreeTwoThreeFiniteComparisons.comparison3414
#print axioms sourceMap3414_checked
#print axioms fusedMap3414_checked
#print axioms certified3414
def sourceMap3414swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3414swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3414swap_checked : acceptsGraphIso
    (source (graph core3414) (root 9) 5 0) DegreeTwoThreeSpectrum6979.graph sourceMap3414swap=true := by decide +kernel
theorem fusedMap3414swap_checked : acceptsGraphIso
    (fused (graph core3414) (root 9) 5 0) DegreeTwoThreeSpectrum5766.graph fusedMap3414swap=true := by decide +kernel
theorem certified3414swap : Certified (graph core3414) (root 9) 5 0 :=
  of_native_maps core3414 DegreeTwoThreeSpectrum6979.graph DegreeTwoThreeSpectrum5766.graph
    sourceMap3414swap fusedMap3414swap sourceMap3414swap_checked fusedMap3414swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3414
#print axioms sourceMap3414swap_checked
#print axioms fusedMap3414swap_checked
#print axioms certified3414swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

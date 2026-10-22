/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3469 : Family 9 := level9.get ⟨667,by decide⟩
def sourceMap3469 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3469 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3469_checked : acceptsGraphIso
    (source (graph core3469) (root 9) 0 5) DegreeTwoThreeSpectrum6686.graph sourceMap3469=true := by decide +kernel
theorem fusedMap3469_checked : acceptsGraphIso
    (fused (graph core3469) (root 9) 0 5) DegreeTwoThreeSpectrum6687.graph fusedMap3469=true := by decide +kernel
theorem certified3469 : Certified (graph core3469) (root 9) 0 5 :=
  of_native_maps core3469 DegreeTwoThreeSpectrum6686.graph DegreeTwoThreeSpectrum6687.graph
    sourceMap3469 fusedMap3469 sourceMap3469_checked fusedMap3469_checked
    DegreeTwoThreeFiniteComparisons.comparison3469
#print axioms sourceMap3469_checked
#print axioms fusedMap3469_checked
#print axioms certified3469
def sourceMap3469swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3469swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3469swap_checked : acceptsGraphIso
    (source (graph core3469) (root 9) 5 0) DegreeTwoThreeSpectrum6686.graph sourceMap3469swap=true := by decide +kernel
theorem fusedMap3469swap_checked : acceptsGraphIso
    (fused (graph core3469) (root 9) 5 0) DegreeTwoThreeSpectrum6687.graph fusedMap3469swap=true := by decide +kernel
theorem certified3469swap : Certified (graph core3469) (root 9) 5 0 :=
  of_native_maps core3469 DegreeTwoThreeSpectrum6686.graph DegreeTwoThreeSpectrum6687.graph
    sourceMap3469swap fusedMap3469swap sourceMap3469swap_checked fusedMap3469swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3469
#print axioms sourceMap3469swap_checked
#print axioms fusedMap3469swap_checked
#print axioms certified3469swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

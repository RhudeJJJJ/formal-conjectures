/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3349 : Family 9 := level9.get ⟨371,by decide⟩
def sourceMap3349 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3349 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3349_checked : acceptsGraphIso
    (source (graph core3349) (root 9) 0 5) DegreeTwoThreeSpectrum6268.graph sourceMap3349=true := by decide +kernel
theorem fusedMap3349_checked : acceptsGraphIso
    (fused (graph core3349) (root 9) 0 5) DegreeTwoThreeSpectrum5252.graph fusedMap3349=true := by decide +kernel
theorem certified3349 : Certified (graph core3349) (root 9) 0 5 :=
  of_native_maps core3349 DegreeTwoThreeSpectrum6268.graph DegreeTwoThreeSpectrum5252.graph
    sourceMap3349 fusedMap3349 sourceMap3349_checked fusedMap3349_checked
    DegreeTwoThreeFiniteComparisons.comparison3349
#print axioms sourceMap3349_checked
#print axioms fusedMap3349_checked
#print axioms certified3349
def sourceMap3349swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3349swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3349swap_checked : acceptsGraphIso
    (source (graph core3349) (root 9) 5 0) DegreeTwoThreeSpectrum6268.graph sourceMap3349swap=true := by decide +kernel
theorem fusedMap3349swap_checked : acceptsGraphIso
    (fused (graph core3349) (root 9) 5 0) DegreeTwoThreeSpectrum5252.graph fusedMap3349swap=true := by decide +kernel
theorem certified3349swap : Certified (graph core3349) (root 9) 5 0 :=
  of_native_maps core3349 DegreeTwoThreeSpectrum6268.graph DegreeTwoThreeSpectrum5252.graph
    sourceMap3349swap fusedMap3349swap sourceMap3349swap_checked fusedMap3349swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3349
#print axioms sourceMap3349swap_checked
#print axioms fusedMap3349swap_checked
#print axioms certified3349swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

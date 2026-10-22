/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3367 : Family 9 := level9.get ⟨410,by decide⟩
def sourceMap3367 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3367 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3367_checked : acceptsGraphIso
    (source (graph core3367) (root 9) 0 5) DegreeTwoThreeSpectrum6441.graph sourceMap3367=true := by decide +kernel
theorem fusedMap3367_checked : acceptsGraphIso
    (fused (graph core3367) (root 9) 0 5) DegreeTwoThreeSpectrum5368.graph fusedMap3367=true := by decide +kernel
theorem certified3367 : Certified (graph core3367) (root 9) 0 5 :=
  of_native_maps core3367 DegreeTwoThreeSpectrum6441.graph DegreeTwoThreeSpectrum5368.graph
    sourceMap3367 fusedMap3367 sourceMap3367_checked fusedMap3367_checked
    DegreeTwoThreeFiniteComparisons.comparison3367
#print axioms sourceMap3367_checked
#print axioms fusedMap3367_checked
#print axioms certified3367
def sourceMap3367swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3367swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3367swap_checked : acceptsGraphIso
    (source (graph core3367) (root 9) 5 0) DegreeTwoThreeSpectrum6441.graph sourceMap3367swap=true := by decide +kernel
theorem fusedMap3367swap_checked : acceptsGraphIso
    (fused (graph core3367) (root 9) 5 0) DegreeTwoThreeSpectrum5368.graph fusedMap3367swap=true := by decide +kernel
theorem certified3367swap : Certified (graph core3367) (root 9) 5 0 :=
  of_native_maps core3367 DegreeTwoThreeSpectrum6441.graph DegreeTwoThreeSpectrum5368.graph
    sourceMap3367swap fusedMap3367swap sourceMap3367swap_checked fusedMap3367swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3367
#print axioms sourceMap3367swap_checked
#print axioms fusedMap3367swap_checked
#print axioms certified3367swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

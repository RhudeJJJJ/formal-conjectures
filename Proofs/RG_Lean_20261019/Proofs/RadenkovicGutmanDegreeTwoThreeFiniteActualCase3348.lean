/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3348 : Family 9 := level9.get ⟨368,by decide⟩
def sourceMap3348 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3348 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3348_checked : acceptsGraphIso
    (source (graph core3348) (root 9) 0 5) DegreeTwoThreeSpectrum6252.graph sourceMap3348=true := by decide +kernel
theorem fusedMap3348_checked : acceptsGraphIso
    (fused (graph core3348) (root 9) 0 5) DegreeTwoThreeSpectrum5248.graph fusedMap3348=true := by decide +kernel
theorem certified3348 : Certified (graph core3348) (root 9) 0 5 :=
  of_native_maps core3348 DegreeTwoThreeSpectrum6252.graph DegreeTwoThreeSpectrum5248.graph
    sourceMap3348 fusedMap3348 sourceMap3348_checked fusedMap3348_checked
    DegreeTwoThreeFiniteComparisons.comparison3348
#print axioms sourceMap3348_checked
#print axioms fusedMap3348_checked
#print axioms certified3348
def sourceMap3348swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3348swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3348swap_checked : acceptsGraphIso
    (source (graph core3348) (root 9) 5 0) DegreeTwoThreeSpectrum6252.graph sourceMap3348swap=true := by decide +kernel
theorem fusedMap3348swap_checked : acceptsGraphIso
    (fused (graph core3348) (root 9) 5 0) DegreeTwoThreeSpectrum5248.graph fusedMap3348swap=true := by decide +kernel
theorem certified3348swap : Certified (graph core3348) (root 9) 5 0 :=
  of_native_maps core3348 DegreeTwoThreeSpectrum6252.graph DegreeTwoThreeSpectrum5248.graph
    sourceMap3348swap fusedMap3348swap sourceMap3348swap_checked fusedMap3348swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3348
#print axioms sourceMap3348swap_checked
#print axioms fusedMap3348swap_checked
#print axioms certified3348swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3277 : Family 9 := level9.get ⟨168,by decide⟩
def sourceMap3277 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3277 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3277_checked : acceptsGraphIso
    (source (graph core3277) (root 9) 0 5) DegreeTwoThreeSpectrum5278.graph sourceMap3277=true := by decide +kernel
theorem fusedMap3277_checked : acceptsGraphIso
    (fused (graph core3277) (root 9) 0 5) DegreeTwoThreeSpectrum5279.graph fusedMap3277=true := by decide +kernel
theorem certified3277 : Certified (graph core3277) (root 9) 0 5 :=
  of_native_maps core3277 DegreeTwoThreeSpectrum5278.graph DegreeTwoThreeSpectrum5279.graph
    sourceMap3277 fusedMap3277 sourceMap3277_checked fusedMap3277_checked
    DegreeTwoThreeFiniteComparisons.comparison3277
#print axioms sourceMap3277_checked
#print axioms fusedMap3277_checked
#print axioms certified3277
def sourceMap3277swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3277swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3277swap_checked : acceptsGraphIso
    (source (graph core3277) (root 9) 5 0) DegreeTwoThreeSpectrum5278.graph sourceMap3277swap=true := by decide +kernel
theorem fusedMap3277swap_checked : acceptsGraphIso
    (fused (graph core3277) (root 9) 5 0) DegreeTwoThreeSpectrum5279.graph fusedMap3277swap=true := by decide +kernel
theorem certified3277swap : Certified (graph core3277) (root 9) 5 0 :=
  of_native_maps core3277 DegreeTwoThreeSpectrum5278.graph DegreeTwoThreeSpectrum5279.graph
    sourceMap3277swap fusedMap3277swap sourceMap3277swap_checked fusedMap3277swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3277
#print axioms sourceMap3277swap_checked
#print axioms fusedMap3277swap_checked
#print axioms certified3277swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

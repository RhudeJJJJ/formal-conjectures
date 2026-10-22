/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3310 : Family 9 := level9.get ⟨265,by decide⟩
def sourceMap3310 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3310 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3310_checked : acceptsGraphIso
    (source (graph core3310) (root 9) 0 5) DegreeTwoThreeSpectrum5717.graph sourceMap3310=true := by decide +kernel
theorem fusedMap3310_checked : acceptsGraphIso
    (fused (graph core3310) (root 9) 0 5) DegreeTwoThreeSpectrum5718.graph fusedMap3310=true := by decide +kernel
theorem certified3310 : Certified (graph core3310) (root 9) 0 5 :=
  of_native_maps core3310 DegreeTwoThreeSpectrum5717.graph DegreeTwoThreeSpectrum5718.graph
    sourceMap3310 fusedMap3310 sourceMap3310_checked fusedMap3310_checked
    DegreeTwoThreeFiniteComparisons.comparison3310
#print axioms sourceMap3310_checked
#print axioms fusedMap3310_checked
#print axioms certified3310
def sourceMap3310swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3310swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3310swap_checked : acceptsGraphIso
    (source (graph core3310) (root 9) 5 0) DegreeTwoThreeSpectrum5717.graph sourceMap3310swap=true := by decide +kernel
theorem fusedMap3310swap_checked : acceptsGraphIso
    (fused (graph core3310) (root 9) 5 0) DegreeTwoThreeSpectrum5718.graph fusedMap3310swap=true := by decide +kernel
theorem certified3310swap : Certified (graph core3310) (root 9) 5 0 :=
  of_native_maps core3310 DegreeTwoThreeSpectrum5717.graph DegreeTwoThreeSpectrum5718.graph
    sourceMap3310swap fusedMap3310swap sourceMap3310swap_checked fusedMap3310swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3310
#print axioms sourceMap3310swap_checked
#print axioms fusedMap3310swap_checked
#print axioms certified3310swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

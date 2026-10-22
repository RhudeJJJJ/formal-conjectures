/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3383 : Family 9 := level9.get ⟨454,by decide⟩
def sourceMap3383 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3383 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3383_checked : acceptsGraphIso
    (source (graph core3383) (root 9) 0 5) DegreeTwoThreeSpectrum6660.graph sourceMap3383=true := by decide +kernel
theorem fusedMap3383_checked : acceptsGraphIso
    (fused (graph core3383) (root 9) 0 5) DegreeTwoThreeSpectrum5517.graph fusedMap3383=true := by decide +kernel
theorem certified3383 : Certified (graph core3383) (root 9) 0 5 :=
  of_native_maps core3383 DegreeTwoThreeSpectrum6660.graph DegreeTwoThreeSpectrum5517.graph
    sourceMap3383 fusedMap3383 sourceMap3383_checked fusedMap3383_checked
    DegreeTwoThreeFiniteComparisons.comparison3383
#print axioms sourceMap3383_checked
#print axioms fusedMap3383_checked
#print axioms certified3383
def sourceMap3383swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3383swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3383swap_checked : acceptsGraphIso
    (source (graph core3383) (root 9) 5 0) DegreeTwoThreeSpectrum6660.graph sourceMap3383swap=true := by decide +kernel
theorem fusedMap3383swap_checked : acceptsGraphIso
    (fused (graph core3383) (root 9) 5 0) DegreeTwoThreeSpectrum5517.graph fusedMap3383swap=true := by decide +kernel
theorem certified3383swap : Certified (graph core3383) (root 9) 5 0 :=
  of_native_maps core3383 DegreeTwoThreeSpectrum6660.graph DegreeTwoThreeSpectrum5517.graph
    sourceMap3383swap fusedMap3383swap sourceMap3383swap_checked fusedMap3383swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3383
#print axioms sourceMap3383swap_checked
#print axioms fusedMap3383swap_checked
#print axioms certified3383swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3261 : Family 9 := level9.get ⟨116,by decide⟩
def sourceMap3261 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3261 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3261_checked : acceptsGraphIso
    (source (graph core3261) (root 9) 0 5) DegreeTwoThreeSpectrum5867.graph sourceMap3261=true := by decide +kernel
theorem fusedMap3261_checked : acceptsGraphIso
    (fused (graph core3261) (root 9) 0 5) DegreeTwoThreeSpectrum5085.graph fusedMap3261=true := by decide +kernel
theorem certified3261 : Certified (graph core3261) (root 9) 0 5 :=
  of_native_maps core3261 DegreeTwoThreeSpectrum5867.graph DegreeTwoThreeSpectrum5085.graph
    sourceMap3261 fusedMap3261 sourceMap3261_checked fusedMap3261_checked
    DegreeTwoThreeFiniteComparisons.comparison3261
#print axioms sourceMap3261_checked
#print axioms fusedMap3261_checked
#print axioms certified3261
def sourceMap3261swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3261swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3261swap_checked : acceptsGraphIso
    (source (graph core3261) (root 9) 5 0) DegreeTwoThreeSpectrum5867.graph sourceMap3261swap=true := by decide +kernel
theorem fusedMap3261swap_checked : acceptsGraphIso
    (fused (graph core3261) (root 9) 5 0) DegreeTwoThreeSpectrum5085.graph fusedMap3261swap=true := by decide +kernel
theorem certified3261swap : Certified (graph core3261) (root 9) 5 0 :=
  of_native_maps core3261 DegreeTwoThreeSpectrum5867.graph DegreeTwoThreeSpectrum5085.graph
    sourceMap3261swap fusedMap3261swap sourceMap3261swap_checked fusedMap3261swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3261
#print axioms sourceMap3261swap_checked
#print axioms fusedMap3261swap_checked
#print axioms certified3261swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

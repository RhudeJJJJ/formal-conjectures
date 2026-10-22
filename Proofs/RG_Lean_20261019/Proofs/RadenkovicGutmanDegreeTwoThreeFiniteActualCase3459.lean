/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3459 : Family 9 := level9.get ⟨638,by decide⟩
def sourceMap3459 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3459 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3459_checked : acceptsGraphIso
    (source (graph core3459) (root 9) 0 5) DegreeTwoThreeSpectrum6504.graph sourceMap3459=true := by decide +kernel
theorem fusedMap3459_checked : acceptsGraphIso
    (fused (graph core3459) (root 9) 0 5) DegreeTwoThreeSpectrum6505.graph fusedMap3459=true := by decide +kernel
theorem certified3459 : Certified (graph core3459) (root 9) 0 5 :=
  of_native_maps core3459 DegreeTwoThreeSpectrum6504.graph DegreeTwoThreeSpectrum6505.graph
    sourceMap3459 fusedMap3459 sourceMap3459_checked fusedMap3459_checked
    DegreeTwoThreeFiniteComparisons.comparison3459
#print axioms sourceMap3459_checked
#print axioms fusedMap3459_checked
#print axioms certified3459
def sourceMap3459swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3459swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3459swap_checked : acceptsGraphIso
    (source (graph core3459) (root 9) 5 0) DegreeTwoThreeSpectrum6504.graph sourceMap3459swap=true := by decide +kernel
theorem fusedMap3459swap_checked : acceptsGraphIso
    (fused (graph core3459) (root 9) 5 0) DegreeTwoThreeSpectrum6505.graph fusedMap3459swap=true := by decide +kernel
theorem certified3459swap : Certified (graph core3459) (root 9) 5 0 :=
  of_native_maps core3459 DegreeTwoThreeSpectrum6504.graph DegreeTwoThreeSpectrum6505.graph
    sourceMap3459swap fusedMap3459swap sourceMap3459swap_checked fusedMap3459swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3459
#print axioms sourceMap3459swap_checked
#print axioms fusedMap3459swap_checked
#print axioms certified3459swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

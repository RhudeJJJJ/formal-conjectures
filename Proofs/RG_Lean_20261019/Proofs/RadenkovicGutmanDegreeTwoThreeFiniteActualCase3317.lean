/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3317 : Family 9 := level9.get ⟨283,by decide⟩
def sourceMap3317 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3317 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3317_checked : acceptsGraphIso
    (source (graph core3317) (root 9) 0 5) DegreeTwoThreeSpectrum5797.graph sourceMap3317=true := by decide +kernel
theorem fusedMap3317_checked : acceptsGraphIso
    (fused (graph core3317) (root 9) 0 5) DegreeTwoThreeSpectrum5798.graph fusedMap3317=true := by decide +kernel
theorem certified3317 : Certified (graph core3317) (root 9) 0 5 :=
  of_native_maps core3317 DegreeTwoThreeSpectrum5797.graph DegreeTwoThreeSpectrum5798.graph
    sourceMap3317 fusedMap3317 sourceMap3317_checked fusedMap3317_checked
    DegreeTwoThreeFiniteComparisons.comparison3317
#print axioms sourceMap3317_checked
#print axioms fusedMap3317_checked
#print axioms certified3317
def sourceMap3317swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3317swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3317swap_checked : acceptsGraphIso
    (source (graph core3317) (root 9) 5 0) DegreeTwoThreeSpectrum5797.graph sourceMap3317swap=true := by decide +kernel
theorem fusedMap3317swap_checked : acceptsGraphIso
    (fused (graph core3317) (root 9) 5 0) DegreeTwoThreeSpectrum5798.graph fusedMap3317swap=true := by decide +kernel
theorem certified3317swap : Certified (graph core3317) (root 9) 5 0 :=
  of_native_maps core3317 DegreeTwoThreeSpectrum5797.graph DegreeTwoThreeSpectrum5798.graph
    sourceMap3317swap fusedMap3317swap sourceMap3317swap_checked fusedMap3317swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3317
#print axioms sourceMap3317swap_checked
#print axioms fusedMap3317swap_checked
#print axioms certified3317swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

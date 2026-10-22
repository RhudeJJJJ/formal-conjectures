/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3272 : Family 9 := level9.get ⟨150,by decide⟩
def sourceMap3272 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3272 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3272_checked : acceptsGraphIso
    (source (graph core3272) (root 9) 0 5) DegreeTwoThreeSpectrum5197.graph sourceMap3272=true := by decide +kernel
theorem fusedMap3272_checked : acceptsGraphIso
    (fused (graph core3272) (root 9) 0 5) DegreeTwoThreeSpectrum5198.graph fusedMap3272=true := by decide +kernel
theorem certified3272 : Certified (graph core3272) (root 9) 0 5 :=
  of_native_maps core3272 DegreeTwoThreeSpectrum5197.graph DegreeTwoThreeSpectrum5198.graph
    sourceMap3272 fusedMap3272 sourceMap3272_checked fusedMap3272_checked
    DegreeTwoThreeFiniteComparisons.comparison3272
#print axioms sourceMap3272_checked
#print axioms fusedMap3272_checked
#print axioms certified3272
def sourceMap3272swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3272swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3272swap_checked : acceptsGraphIso
    (source (graph core3272) (root 9) 5 0) DegreeTwoThreeSpectrum5197.graph sourceMap3272swap=true := by decide +kernel
theorem fusedMap3272swap_checked : acceptsGraphIso
    (fused (graph core3272) (root 9) 5 0) DegreeTwoThreeSpectrum5198.graph fusedMap3272swap=true := by decide +kernel
theorem certified3272swap : Certified (graph core3272) (root 9) 5 0 :=
  of_native_maps core3272 DegreeTwoThreeSpectrum5197.graph DegreeTwoThreeSpectrum5198.graph
    sourceMap3272swap fusedMap3272swap sourceMap3272swap_checked fusedMap3272swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3272
#print axioms sourceMap3272swap_checked
#print axioms fusedMap3272swap_checked
#print axioms certified3272swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

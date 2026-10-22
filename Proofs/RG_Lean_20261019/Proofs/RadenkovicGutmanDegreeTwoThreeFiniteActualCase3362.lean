/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3362 : Family 9 := level9.get ⟨402,by decide⟩
def sourceMap3362 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3362 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3362_checked : acceptsGraphIso
    (source (graph core3362) (root 9) 0 5) DegreeTwoThreeSpectrum6405.graph sourceMap3362=true := by decide +kernel
theorem fusedMap3362_checked : acceptsGraphIso
    (fused (graph core3362) (root 9) 0 5) DegreeTwoThreeSpectrum5339.graph fusedMap3362=true := by decide +kernel
theorem certified3362 : Certified (graph core3362) (root 9) 0 5 :=
  of_native_maps core3362 DegreeTwoThreeSpectrum6405.graph DegreeTwoThreeSpectrum5339.graph
    sourceMap3362 fusedMap3362 sourceMap3362_checked fusedMap3362_checked
    DegreeTwoThreeFiniteComparisons.comparison3362
#print axioms sourceMap3362_checked
#print axioms fusedMap3362_checked
#print axioms certified3362
def sourceMap3362swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3362swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3362swap_checked : acceptsGraphIso
    (source (graph core3362) (root 9) 5 0) DegreeTwoThreeSpectrum6405.graph sourceMap3362swap=true := by decide +kernel
theorem fusedMap3362swap_checked : acceptsGraphIso
    (fused (graph core3362) (root 9) 5 0) DegreeTwoThreeSpectrum5339.graph fusedMap3362swap=true := by decide +kernel
theorem certified3362swap : Certified (graph core3362) (root 9) 5 0 :=
  of_native_maps core3362 DegreeTwoThreeSpectrum6405.graph DegreeTwoThreeSpectrum5339.graph
    sourceMap3362swap fusedMap3362swap sourceMap3362swap_checked fusedMap3362swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3362
#print axioms sourceMap3362swap_checked
#print axioms fusedMap3362swap_checked
#print axioms certified3362swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

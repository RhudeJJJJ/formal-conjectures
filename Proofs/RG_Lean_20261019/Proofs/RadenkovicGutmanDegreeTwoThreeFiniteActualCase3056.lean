/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3056 : Family 10 := level10.get ⟨1717,by decide⟩
def sourceMap3056 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3056 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3056_checked : acceptsGraphIso
    (source (graph core3056) (root 10) 0 4) DegreeTwoThreeSpectrum7339.graph sourceMap3056=true := by decide +kernel
theorem fusedMap3056_checked : acceptsGraphIso
    (fused (graph core3056) (root 10) 0 4) DegreeTwoThreeSpectrum6503.graph fusedMap3056=true := by decide +kernel
theorem certified3056 : Certified (graph core3056) (root 10) 0 4 :=
  of_native_maps core3056 DegreeTwoThreeSpectrum7339.graph DegreeTwoThreeSpectrum6503.graph
    sourceMap3056 fusedMap3056 sourceMap3056_checked fusedMap3056_checked
    DegreeTwoThreeFiniteComparisons.comparison3056
#print axioms sourceMap3056_checked
#print axioms fusedMap3056_checked
#print axioms certified3056
def sourceMap3056swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3056swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3056swap_checked : acceptsGraphIso
    (source (graph core3056) (root 10) 4 0) DegreeTwoThreeSpectrum7339.graph sourceMap3056swap=true := by decide +kernel
theorem fusedMap3056swap_checked : acceptsGraphIso
    (fused (graph core3056) (root 10) 4 0) DegreeTwoThreeSpectrum6503.graph fusedMap3056swap=true := by decide +kernel
theorem certified3056swap : Certified (graph core3056) (root 10) 4 0 :=
  of_native_maps core3056 DegreeTwoThreeSpectrum7339.graph DegreeTwoThreeSpectrum6503.graph
    sourceMap3056swap fusedMap3056swap sourceMap3056swap_checked fusedMap3056swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3056
#print axioms sourceMap3056swap_checked
#print axioms fusedMap3056swap_checked
#print axioms certified3056swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

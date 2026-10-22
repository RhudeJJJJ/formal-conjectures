/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3406 : Family 9 := level9.get ⟨506,by decide⟩
def sourceMap3406 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3406 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3406_checked : acceptsGraphIso
    (source (graph core3406) (root 9) 0 5) DegreeTwoThreeSpectrum6925.graph sourceMap3406=true := by decide +kernel
theorem fusedMap3406_checked : acceptsGraphIso
    (fused (graph core3406) (root 9) 0 5) DegreeTwoThreeSpectrum5704.graph fusedMap3406=true := by decide +kernel
theorem certified3406 : Certified (graph core3406) (root 9) 0 5 :=
  of_native_maps core3406 DegreeTwoThreeSpectrum6925.graph DegreeTwoThreeSpectrum5704.graph
    sourceMap3406 fusedMap3406 sourceMap3406_checked fusedMap3406_checked
    DegreeTwoThreeFiniteComparisons.comparison3406
#print axioms sourceMap3406_checked
#print axioms fusedMap3406_checked
#print axioms certified3406
def sourceMap3406swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3406swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3406swap_checked : acceptsGraphIso
    (source (graph core3406) (root 9) 5 0) DegreeTwoThreeSpectrum6925.graph sourceMap3406swap=true := by decide +kernel
theorem fusedMap3406swap_checked : acceptsGraphIso
    (fused (graph core3406) (root 9) 5 0) DegreeTwoThreeSpectrum5704.graph fusedMap3406swap=true := by decide +kernel
theorem certified3406swap : Certified (graph core3406) (root 9) 5 0 :=
  of_native_maps core3406 DegreeTwoThreeSpectrum6925.graph DegreeTwoThreeSpectrum5704.graph
    sourceMap3406swap fusedMap3406swap sourceMap3406swap_checked fusedMap3406swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3406
#print axioms sourceMap3406swap_checked
#print axioms fusedMap3406swap_checked
#print axioms certified3406swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

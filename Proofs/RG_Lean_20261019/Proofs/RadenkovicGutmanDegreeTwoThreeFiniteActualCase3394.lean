/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3394 : Family 9 := level9.get ⟨478,by decide⟩
def sourceMap3394 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3394 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3394_checked : acceptsGraphIso
    (source (graph core3394) (root 9) 0 5) DegreeTwoThreeSpectrum6756.graph sourceMap3394=true := by decide +kernel
theorem fusedMap3394_checked : acceptsGraphIso
    (fused (graph core3394) (root 9) 0 5) DegreeTwoThreeSpectrum5597.graph fusedMap3394=true := by decide +kernel
theorem certified3394 : Certified (graph core3394) (root 9) 0 5 :=
  of_native_maps core3394 DegreeTwoThreeSpectrum6756.graph DegreeTwoThreeSpectrum5597.graph
    sourceMap3394 fusedMap3394 sourceMap3394_checked fusedMap3394_checked
    DegreeTwoThreeFiniteComparisons.comparison3394
#print axioms sourceMap3394_checked
#print axioms fusedMap3394_checked
#print axioms certified3394
def sourceMap3394swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3394swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3394swap_checked : acceptsGraphIso
    (source (graph core3394) (root 9) 5 0) DegreeTwoThreeSpectrum6756.graph sourceMap3394swap=true := by decide +kernel
theorem fusedMap3394swap_checked : acceptsGraphIso
    (fused (graph core3394) (root 9) 5 0) DegreeTwoThreeSpectrum5597.graph fusedMap3394swap=true := by decide +kernel
theorem certified3394swap : Certified (graph core3394) (root 9) 5 0 :=
  of_native_maps core3394 DegreeTwoThreeSpectrum6756.graph DegreeTwoThreeSpectrum5597.graph
    sourceMap3394swap fusedMap3394swap sourceMap3394swap_checked fusedMap3394swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3394
#print axioms sourceMap3394swap_checked
#print axioms fusedMap3394swap_checked
#print axioms certified3394swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

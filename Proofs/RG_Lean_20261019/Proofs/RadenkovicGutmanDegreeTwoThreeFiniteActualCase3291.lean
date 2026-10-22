/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3291 : Family 9 := level9.get ⟨210,by decide⟩
def sourceMap3291 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3291 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3291_checked : acceptsGraphIso
    (source (graph core3291) (root 9) 0 5) DegreeTwoThreeSpectrum5467.graph sourceMap3291=true := by decide +kernel
theorem fusedMap3291_checked : acceptsGraphIso
    (fused (graph core3291) (root 9) 0 5) DegreeTwoThreeSpectrum5468.graph fusedMap3291=true := by decide +kernel
theorem certified3291 : Certified (graph core3291) (root 9) 0 5 :=
  of_native_maps core3291 DegreeTwoThreeSpectrum5467.graph DegreeTwoThreeSpectrum5468.graph
    sourceMap3291 fusedMap3291 sourceMap3291_checked fusedMap3291_checked
    DegreeTwoThreeFiniteComparisons.comparison3291
#print axioms sourceMap3291_checked
#print axioms fusedMap3291_checked
#print axioms certified3291
def sourceMap3291swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3291swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3291swap_checked : acceptsGraphIso
    (source (graph core3291) (root 9) 5 0) DegreeTwoThreeSpectrum5467.graph sourceMap3291swap=true := by decide +kernel
theorem fusedMap3291swap_checked : acceptsGraphIso
    (fused (graph core3291) (root 9) 5 0) DegreeTwoThreeSpectrum5468.graph fusedMap3291swap=true := by decide +kernel
theorem certified3291swap : Certified (graph core3291) (root 9) 5 0 :=
  of_native_maps core3291 DegreeTwoThreeSpectrum5467.graph DegreeTwoThreeSpectrum5468.graph
    sourceMap3291swap fusedMap3291swap sourceMap3291swap_checked fusedMap3291swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3291
#print axioms sourceMap3291swap_checked
#print axioms fusedMap3291swap_checked
#print axioms certified3291swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3264 : Family 9 := level9.get ⟨123,by decide⟩
def sourceMap3264 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 9 0 5 v)
def fusedMap3264 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3264_checked : acceptsGraphIso
    (source (graph core3264) (root 9) 0 5) DegreeTwoThreeSpectrum5908.graph sourceMap3264=true := by decide +kernel
theorem fusedMap3264_checked : acceptsGraphIso
    (fused (graph core3264) (root 9) 0 5) DegreeTwoThreeSpectrum5097.graph fusedMap3264=true := by decide +kernel
theorem certified3264 : Certified (graph core3264) (root 9) 0 5 :=
  of_native_maps core3264 DegreeTwoThreeSpectrum5908.graph DegreeTwoThreeSpectrum5097.graph
    sourceMap3264 fusedMap3264 sourceMap3264_checked fusedMap3264_checked
    DegreeTwoThreeFiniteComparisons.comparison3264
#print axioms sourceMap3264_checked
#print axioms fusedMap3264_checked
#print axioms certified3264
def sourceMap3264swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13,16] (sourceLabel 9 5 0 v)
def fusedMap3264swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3264swap_checked : acceptsGraphIso
    (source (graph core3264) (root 9) 5 0) DegreeTwoThreeSpectrum5908.graph sourceMap3264swap=true := by decide +kernel
theorem fusedMap3264swap_checked : acceptsGraphIso
    (fused (graph core3264) (root 9) 5 0) DegreeTwoThreeSpectrum5097.graph fusedMap3264swap=true := by decide +kernel
theorem certified3264swap : Certified (graph core3264) (root 9) 5 0 :=
  of_native_maps core3264 DegreeTwoThreeSpectrum5908.graph DegreeTwoThreeSpectrum5097.graph
    sourceMap3264swap fusedMap3264swap sourceMap3264swap_checked fusedMap3264swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3264
#print axioms sourceMap3264swap_checked
#print axioms fusedMap3264swap_checked
#print axioms certified3264swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

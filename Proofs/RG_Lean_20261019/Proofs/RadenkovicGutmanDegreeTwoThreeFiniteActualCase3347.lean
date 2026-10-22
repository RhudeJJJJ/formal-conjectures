/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3347 : Family 9 := level9.get ⟨364,by decide⟩
def sourceMap3347 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3347 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3347_checked : acceptsGraphIso
    (source (graph core3347) (root 9) 0 5) DegreeTwoThreeSpectrum6233.graph sourceMap3347=true := by decide +kernel
theorem fusedMap3347_checked : acceptsGraphIso
    (fused (graph core3347) (root 9) 0 5) DegreeTwoThreeSpectrum5238.graph fusedMap3347=true := by decide +kernel
theorem certified3347 : Certified (graph core3347) (root 9) 0 5 :=
  of_native_maps core3347 DegreeTwoThreeSpectrum6233.graph DegreeTwoThreeSpectrum5238.graph
    sourceMap3347 fusedMap3347 sourceMap3347_checked fusedMap3347_checked
    DegreeTwoThreeFiniteComparisons.comparison3347
#print axioms sourceMap3347_checked
#print axioms fusedMap3347_checked
#print axioms certified3347
def sourceMap3347swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3347swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3347swap_checked : acceptsGraphIso
    (source (graph core3347) (root 9) 5 0) DegreeTwoThreeSpectrum6233.graph sourceMap3347swap=true := by decide +kernel
theorem fusedMap3347swap_checked : acceptsGraphIso
    (fused (graph core3347) (root 9) 5 0) DegreeTwoThreeSpectrum5238.graph fusedMap3347swap=true := by decide +kernel
theorem certified3347swap : Certified (graph core3347) (root 9) 5 0 :=
  of_native_maps core3347 DegreeTwoThreeSpectrum6233.graph DegreeTwoThreeSpectrum5238.graph
    sourceMap3347swap fusedMap3347swap sourceMap3347swap_checked fusedMap3347swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3347
#print axioms sourceMap3347swap_checked
#print axioms fusedMap3347swap_checked
#print axioms certified3347swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

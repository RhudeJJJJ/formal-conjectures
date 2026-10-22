/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3354 : Family 9 := level9.get ⟨382,by decide⟩
def sourceMap3354 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3354 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3354_checked : acceptsGraphIso
    (source (graph core3354) (root 9) 0 5) DegreeTwoThreeSpectrum6322.graph sourceMap3354=true := by decide +kernel
theorem fusedMap3354_checked : acceptsGraphIso
    (fused (graph core3354) (root 9) 0 5) DegreeTwoThreeSpectrum5282.graph fusedMap3354=true := by decide +kernel
theorem certified3354 : Certified (graph core3354) (root 9) 0 5 :=
  of_native_maps core3354 DegreeTwoThreeSpectrum6322.graph DegreeTwoThreeSpectrum5282.graph
    sourceMap3354 fusedMap3354 sourceMap3354_checked fusedMap3354_checked
    DegreeTwoThreeFiniteComparisons.comparison3354
#print axioms sourceMap3354_checked
#print axioms fusedMap3354_checked
#print axioms certified3354
def sourceMap3354swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3354swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3354swap_checked : acceptsGraphIso
    (source (graph core3354) (root 9) 5 0) DegreeTwoThreeSpectrum6322.graph sourceMap3354swap=true := by decide +kernel
theorem fusedMap3354swap_checked : acceptsGraphIso
    (fused (graph core3354) (root 9) 5 0) DegreeTwoThreeSpectrum5282.graph fusedMap3354swap=true := by decide +kernel
theorem certified3354swap : Certified (graph core3354) (root 9) 5 0 :=
  of_native_maps core3354 DegreeTwoThreeSpectrum6322.graph DegreeTwoThreeSpectrum5282.graph
    sourceMap3354swap fusedMap3354swap sourceMap3354swap_checked fusedMap3354swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3354
#print axioms sourceMap3354swap_checked
#print axioms fusedMap3354swap_checked
#print axioms certified3354swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

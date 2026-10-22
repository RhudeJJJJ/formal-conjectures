/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3334 : Family 9 := level9.get ⟨328,by decide⟩
def sourceMap3334 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3334 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3334_checked : acceptsGraphIso
    (source (graph core3334) (root 9) 0 5) DegreeTwoThreeSpectrum6041.graph sourceMap3334=true := by decide +kernel
theorem fusedMap3334_checked : acceptsGraphIso
    (fused (graph core3334) (root 9) 0 5) DegreeTwoThreeSpectrum5150.graph fusedMap3334=true := by decide +kernel
theorem certified3334 : Certified (graph core3334) (root 9) 0 5 :=
  of_native_maps core3334 DegreeTwoThreeSpectrum6041.graph DegreeTwoThreeSpectrum5150.graph
    sourceMap3334 fusedMap3334 sourceMap3334_checked fusedMap3334_checked
    DegreeTwoThreeFiniteComparisons.comparison3334
#print axioms sourceMap3334_checked
#print axioms fusedMap3334_checked
#print axioms certified3334
def sourceMap3334swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3334swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3334swap_checked : acceptsGraphIso
    (source (graph core3334) (root 9) 5 0) DegreeTwoThreeSpectrum6041.graph sourceMap3334swap=true := by decide +kernel
theorem fusedMap3334swap_checked : acceptsGraphIso
    (fused (graph core3334) (root 9) 5 0) DegreeTwoThreeSpectrum5150.graph fusedMap3334swap=true := by decide +kernel
theorem certified3334swap : Certified (graph core3334) (root 9) 5 0 :=
  of_native_maps core3334 DegreeTwoThreeSpectrum6041.graph DegreeTwoThreeSpectrum5150.graph
    sourceMap3334swap fusedMap3334swap sourceMap3334swap_checked fusedMap3334swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3334
#print axioms sourceMap3334swap_checked
#print axioms fusedMap3334swap_checked
#print axioms certified3334swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3467 : Family 9 := level9.get ⟨657,by decide⟩
def sourceMap3467 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3467 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3467_checked : acceptsGraphIso
    (source (graph core3467) (root 9) 0 5) DegreeTwoThreeSpectrum6621.graph sourceMap3467=true := by decide +kernel
theorem fusedMap3467_checked : acceptsGraphIso
    (fused (graph core3467) (root 9) 0 5) DegreeTwoThreeSpectrum6622.graph fusedMap3467=true := by decide +kernel
theorem certified3467 : Certified (graph core3467) (root 9) 0 5 :=
  of_native_maps core3467 DegreeTwoThreeSpectrum6621.graph DegreeTwoThreeSpectrum6622.graph
    sourceMap3467 fusedMap3467 sourceMap3467_checked fusedMap3467_checked
    DegreeTwoThreeFiniteComparisons.comparison3467
#print axioms sourceMap3467_checked
#print axioms fusedMap3467_checked
#print axioms certified3467
def sourceMap3467swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3467swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3467swap_checked : acceptsGraphIso
    (source (graph core3467) (root 9) 5 0) DegreeTwoThreeSpectrum6621.graph sourceMap3467swap=true := by decide +kernel
theorem fusedMap3467swap_checked : acceptsGraphIso
    (fused (graph core3467) (root 9) 5 0) DegreeTwoThreeSpectrum6622.graph fusedMap3467swap=true := by decide +kernel
theorem certified3467swap : Certified (graph core3467) (root 9) 5 0 :=
  of_native_maps core3467 DegreeTwoThreeSpectrum6621.graph DegreeTwoThreeSpectrum6622.graph
    sourceMap3467swap fusedMap3467swap sourceMap3467swap_checked fusedMap3467swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3467
#print axioms sourceMap3467swap_checked
#print axioms fusedMap3467swap_checked
#print axioms certified3467swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

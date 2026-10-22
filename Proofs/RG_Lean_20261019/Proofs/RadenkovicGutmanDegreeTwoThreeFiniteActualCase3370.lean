/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3370 : Family 9 := level9.get ⟨423,by decide⟩
def sourceMap3370 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3370 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3370_checked : acceptsGraphIso
    (source (graph core3370) (root 9) 0 5) DegreeTwoThreeSpectrum6516.graph sourceMap3370=true := by decide +kernel
theorem fusedMap3370_checked : acceptsGraphIso
    (fused (graph core3370) (root 9) 0 5) DegreeTwoThreeSpectrum5429.graph fusedMap3370=true := by decide +kernel
theorem certified3370 : Certified (graph core3370) (root 9) 0 5 :=
  of_native_maps core3370 DegreeTwoThreeSpectrum6516.graph DegreeTwoThreeSpectrum5429.graph
    sourceMap3370 fusedMap3370 sourceMap3370_checked fusedMap3370_checked
    DegreeTwoThreeFiniteComparisons.comparison3370
#print axioms sourceMap3370_checked
#print axioms fusedMap3370_checked
#print axioms certified3370
def sourceMap3370swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3370swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3370swap_checked : acceptsGraphIso
    (source (graph core3370) (root 9) 5 0) DegreeTwoThreeSpectrum6516.graph sourceMap3370swap=true := by decide +kernel
theorem fusedMap3370swap_checked : acceptsGraphIso
    (fused (graph core3370) (root 9) 5 0) DegreeTwoThreeSpectrum5429.graph fusedMap3370swap=true := by decide +kernel
theorem certified3370swap : Certified (graph core3370) (root 9) 5 0 :=
  of_native_maps core3370 DegreeTwoThreeSpectrum6516.graph DegreeTwoThreeSpectrum5429.graph
    sourceMap3370swap fusedMap3370swap sourceMap3370swap_checked fusedMap3370swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3370
#print axioms sourceMap3370swap_checked
#print axioms fusedMap3370swap_checked
#print axioms certified3370swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

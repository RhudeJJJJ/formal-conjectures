/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3332 : Family 9 := level9.get ⟨324,by decide⟩
def sourceMap3332 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3332 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3332_checked : acceptsGraphIso
    (source (graph core3332) (root 9) 0 5) DegreeTwoThreeSpectrum6019.graph sourceMap3332=true := by decide +kernel
theorem fusedMap3332_checked : acceptsGraphIso
    (fused (graph core3332) (root 9) 0 5) DegreeTwoThreeSpectrum5142.graph fusedMap3332=true := by decide +kernel
theorem certified3332 : Certified (graph core3332) (root 9) 0 5 :=
  of_native_maps core3332 DegreeTwoThreeSpectrum6019.graph DegreeTwoThreeSpectrum5142.graph
    sourceMap3332 fusedMap3332 sourceMap3332_checked fusedMap3332_checked
    DegreeTwoThreeFiniteComparisons.comparison3332
#print axioms sourceMap3332_checked
#print axioms fusedMap3332_checked
#print axioms certified3332
def sourceMap3332swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3332swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3332swap_checked : acceptsGraphIso
    (source (graph core3332) (root 9) 5 0) DegreeTwoThreeSpectrum6019.graph sourceMap3332swap=true := by decide +kernel
theorem fusedMap3332swap_checked : acceptsGraphIso
    (fused (graph core3332) (root 9) 5 0) DegreeTwoThreeSpectrum5142.graph fusedMap3332swap=true := by decide +kernel
theorem certified3332swap : Certified (graph core3332) (root 9) 5 0 :=
  of_native_maps core3332 DegreeTwoThreeSpectrum6019.graph DegreeTwoThreeSpectrum5142.graph
    sourceMap3332swap fusedMap3332swap sourceMap3332swap_checked fusedMap3332swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3332
#print axioms sourceMap3332swap_checked
#print axioms fusedMap3332swap_checked
#print axioms certified3332swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3460 : Family 9 := level9.get ⟨639,by decide⟩
def sourceMap3460 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3460 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3460_checked : acceptsGraphIso
    (source (graph core3460) (root 9) 0 5) DegreeTwoThreeSpectrum6507.graph sourceMap3460=true := by decide +kernel
theorem fusedMap3460_checked : acceptsGraphIso
    (fused (graph core3460) (root 9) 0 5) DegreeTwoThreeSpectrum6508.graph fusedMap3460=true := by decide +kernel
theorem certified3460 : Certified (graph core3460) (root 9) 0 5 :=
  of_native_maps core3460 DegreeTwoThreeSpectrum6507.graph DegreeTwoThreeSpectrum6508.graph
    sourceMap3460 fusedMap3460 sourceMap3460_checked fusedMap3460_checked
    DegreeTwoThreeFiniteComparisons.comparison3460
#print axioms sourceMap3460_checked
#print axioms fusedMap3460_checked
#print axioms certified3460
def sourceMap3460swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3460swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3460swap_checked : acceptsGraphIso
    (source (graph core3460) (root 9) 5 0) DegreeTwoThreeSpectrum6507.graph sourceMap3460swap=true := by decide +kernel
theorem fusedMap3460swap_checked : acceptsGraphIso
    (fused (graph core3460) (root 9) 5 0) DegreeTwoThreeSpectrum6508.graph fusedMap3460swap=true := by decide +kernel
theorem certified3460swap : Certified (graph core3460) (root 9) 5 0 :=
  of_native_maps core3460 DegreeTwoThreeSpectrum6507.graph DegreeTwoThreeSpectrum6508.graph
    sourceMap3460swap fusedMap3460swap sourceMap3460swap_checked fusedMap3460swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3460
#print axioms sourceMap3460swap_checked
#print axioms fusedMap3460swap_checked
#print axioms certified3460swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

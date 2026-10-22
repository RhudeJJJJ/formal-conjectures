/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3461 : Family 9 := level9.get ⟨642,by decide⟩
def sourceMap3461 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3461 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3461_checked : acceptsGraphIso
    (source (graph core3461) (root 9) 0 5) DegreeTwoThreeSpectrum6528.graph sourceMap3461=true := by decide +kernel
theorem fusedMap3461_checked : acceptsGraphIso
    (fused (graph core3461) (root 9) 0 5) DegreeTwoThreeSpectrum6529.graph fusedMap3461=true := by decide +kernel
theorem certified3461 : Certified (graph core3461) (root 9) 0 5 :=
  of_native_maps core3461 DegreeTwoThreeSpectrum6528.graph DegreeTwoThreeSpectrum6529.graph
    sourceMap3461 fusedMap3461 sourceMap3461_checked fusedMap3461_checked
    DegreeTwoThreeFiniteComparisons.comparison3461
#print axioms sourceMap3461_checked
#print axioms fusedMap3461_checked
#print axioms certified3461
def sourceMap3461swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3461swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3461swap_checked : acceptsGraphIso
    (source (graph core3461) (root 9) 5 0) DegreeTwoThreeSpectrum6528.graph sourceMap3461swap=true := by decide +kernel
theorem fusedMap3461swap_checked : acceptsGraphIso
    (fused (graph core3461) (root 9) 5 0) DegreeTwoThreeSpectrum6529.graph fusedMap3461swap=true := by decide +kernel
theorem certified3461swap : Certified (graph core3461) (root 9) 5 0 :=
  of_native_maps core3461 DegreeTwoThreeSpectrum6528.graph DegreeTwoThreeSpectrum6529.graph
    sourceMap3461swap fusedMap3461swap sourceMap3461swap_checked fusedMap3461swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3461
#print axioms sourceMap3461swap_checked
#print axioms fusedMap3461swap_checked
#print axioms certified3461swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

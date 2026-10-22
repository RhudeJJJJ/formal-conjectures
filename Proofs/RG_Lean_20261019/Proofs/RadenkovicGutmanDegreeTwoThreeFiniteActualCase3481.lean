/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3481 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap3481 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (sourceLabel 5 0 6 v)
def fusedMap3481 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 0 6 v)
theorem sourceMap3481_checked : acceptsGraphIso
    (source (graph core3481) (root 5) 0 6) DegreeTwoThreeSpectrum1781.graph sourceMap3481=true := by decide +kernel
theorem fusedMap3481_checked : acceptsGraphIso
    (fused (graph core3481) (root 5) 0 6) DegreeTwoThreeSpectrum1711.graph fusedMap3481=true := by decide +kernel
theorem certified3481 : Certified (graph core3481) (root 5) 0 6 :=
  of_native_maps core3481 DegreeTwoThreeSpectrum1781.graph DegreeTwoThreeSpectrum1711.graph
    sourceMap3481 fusedMap3481 sourceMap3481_checked fusedMap3481_checked
    DegreeTwoThreeFiniteComparisons.comparison3481
#print axioms sourceMap3481_checked
#print axioms fusedMap3481_checked
#print axioms certified3481
def sourceMap3481swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,8] (sourceLabel 5 6 0 v)
def fusedMap3481swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 6 0 v)
theorem sourceMap3481swap_checked : acceptsGraphIso
    (source (graph core3481) (root 5) 6 0) DegreeTwoThreeSpectrum1781.graph sourceMap3481swap=true := by decide +kernel
theorem fusedMap3481swap_checked : acceptsGraphIso
    (fused (graph core3481) (root 5) 6 0) DegreeTwoThreeSpectrum1711.graph fusedMap3481swap=true := by decide +kernel
theorem certified3481swap : Certified (graph core3481) (root 5) 6 0 :=
  of_native_maps core3481 DegreeTwoThreeSpectrum1781.graph DegreeTwoThreeSpectrum1711.graph
    sourceMap3481swap fusedMap3481swap sourceMap3481swap_checked fusedMap3481swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3481
#print axioms sourceMap3481swap_checked
#print axioms fusedMap3481swap_checked
#print axioms certified3481swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

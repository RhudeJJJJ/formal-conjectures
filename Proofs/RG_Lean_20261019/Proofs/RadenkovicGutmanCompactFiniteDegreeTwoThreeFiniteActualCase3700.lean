/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3700 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3700 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (sourceLabel 3 0 8 v)
def fusedMap3700 : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 0 8 v)
theorem sourceMap3700_checked : acceptsGraphIso
    (source (graph core3700) (root 3) 0 8) DegreeTwoThreeSpectrum1717.graph sourceMap3700=true := by decide +kernel
theorem fusedMap3700_checked : acceptsGraphIso
    (fused (graph core3700) (root 3) 0 8) DegreeTwoThreeSpectrum1722.graph fusedMap3700=true := by decide +kernel
theorem certified3700 : Certified (graph core3700) (root 3) 0 8 :=
  of_native_maps core3700 DegreeTwoThreeSpectrum1717.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap3700 fusedMap3700 sourceMap3700_checked fusedMap3700_checked
    DegreeTwoThreeFiniteComparisons.comparison3700
#print axioms sourceMap3700_checked
#print axioms fusedMap3700_checked
#print axioms certified3700
def sourceMap3700swap : (Vertices 3 ⊕ Fin 9 ⊕ Fin 1) → Fin 14 :=
  fun v => ![3,4,5,6,2,1,0,8,9,10,11,12,13,7] (sourceLabel 3 8 0 v)
def fusedMap3700swap : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 8 0 v)
theorem sourceMap3700swap_checked : acceptsGraphIso
    (source (graph core3700) (root 3) 8 0) DegreeTwoThreeSpectrum1717.graph sourceMap3700swap=true := by decide +kernel
theorem fusedMap3700swap_checked : acceptsGraphIso
    (fused (graph core3700) (root 3) 8 0) DegreeTwoThreeSpectrum1722.graph fusedMap3700swap=true := by decide +kernel
theorem certified3700swap : Certified (graph core3700) (root 3) 8 0 :=
  of_native_maps core3700 DegreeTwoThreeSpectrum1717.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap3700swap fusedMap3700swap sourceMap3700swap_checked fusedMap3700swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3700
#print axioms sourceMap3700swap_checked
#print axioms fusedMap3700swap_checked
#print axioms certified3700swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

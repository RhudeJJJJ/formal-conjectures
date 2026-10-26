/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3596 : Family 8 := level8.get ⟨176,by decide⟩
def sourceMap3596 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3596 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3596_checked : acceptsGraphIso
    (source (graph core3596) (root 8) 0 6) DegreeTwoThreeSpectrum5767.graph sourceMap3596=true := by decide +kernel
theorem fusedMap3596_checked : acceptsGraphIso
    (fused (graph core3596) (root 8) 0 6) DegreeTwoThreeSpectrum5769.graph fusedMap3596=true := by decide +kernel
theorem certified3596 : Certified (graph core3596) (root 8) 0 6 :=
  of_native_maps core3596 DegreeTwoThreeSpectrum5767.graph DegreeTwoThreeSpectrum5769.graph
    sourceMap3596 fusedMap3596 sourceMap3596_checked fusedMap3596_checked
    DegreeTwoThreeFiniteComparisons.comparison3596
#print axioms sourceMap3596_checked
#print axioms fusedMap3596_checked
#print axioms certified3596
def sourceMap3596swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3596swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3596swap_checked : acceptsGraphIso
    (source (graph core3596) (root 8) 6 0) DegreeTwoThreeSpectrum5767.graph sourceMap3596swap=true := by decide +kernel
theorem fusedMap3596swap_checked : acceptsGraphIso
    (fused (graph core3596) (root 8) 6 0) DegreeTwoThreeSpectrum5769.graph fusedMap3596swap=true := by decide +kernel
theorem certified3596swap : Certified (graph core3596) (root 8) 6 0 :=
  of_native_maps core3596 DegreeTwoThreeSpectrum5767.graph DegreeTwoThreeSpectrum5769.graph
    sourceMap3596swap fusedMap3596swap sourceMap3596swap_checked fusedMap3596swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3596
#print axioms sourceMap3596swap_checked
#print axioms fusedMap3596swap_checked
#print axioms certified3596swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

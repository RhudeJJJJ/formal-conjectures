/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3713 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap3713 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3713 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3713_checked : acceptsGraphIso
    (source (graph core3713) (root 6) 0 8) DegreeTwoThreeSpectrum5062.graph sourceMap3713=true := by decide +kernel
theorem fusedMap3713_checked : acceptsGraphIso
    (fused (graph core3713) (root 6) 0 8) DegreeTwoThreeSpectrum5066.graph fusedMap3713=true := by decide +kernel
theorem certified3713 : Certified (graph core3713) (root 6) 0 8 :=
  of_native_maps core3713 DegreeTwoThreeSpectrum5062.graph DegreeTwoThreeSpectrum5066.graph
    sourceMap3713 fusedMap3713 sourceMap3713_checked fusedMap3713_checked
    DegreeTwoThreeFiniteComparisons.comparison3713
#print axioms sourceMap3713_checked
#print axioms fusedMap3713_checked
#print axioms certified3713
def sourceMap3713swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,16,9] (sourceLabel 6 8 0 v)
def fusedMap3713swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3713swap_checked : acceptsGraphIso
    (source (graph core3713) (root 6) 8 0) DegreeTwoThreeSpectrum5062.graph sourceMap3713swap=true := by decide +kernel
theorem fusedMap3713swap_checked : acceptsGraphIso
    (fused (graph core3713) (root 6) 8 0) DegreeTwoThreeSpectrum5066.graph fusedMap3713swap=true := by decide +kernel
theorem certified3713swap : Certified (graph core3713) (root 6) 8 0 :=
  of_native_maps core3713 DegreeTwoThreeSpectrum5062.graph DegreeTwoThreeSpectrum5066.graph
    sourceMap3713swap fusedMap3713swap sourceMap3713swap_checked fusedMap3713swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3713
#print axioms sourceMap3713swap_checked
#print axioms fusedMap3713swap_checked
#print axioms certified3713swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

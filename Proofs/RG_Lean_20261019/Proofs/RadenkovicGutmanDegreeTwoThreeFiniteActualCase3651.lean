/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3651 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap3651 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3651 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3651_checked : acceptsGraphIso
    (source (graph core3651) (root 6) 0 7) DegreeTwoThreeSpectrum3904.graph sourceMap3651=true := by decide +kernel
theorem fusedMap3651_checked : acceptsGraphIso
    (fused (graph core3651) (root 6) 0 7) DegreeTwoThreeSpectrum3907.graph fusedMap3651=true := by decide +kernel
theorem certified3651 : Certified (graph core3651) (root 6) 0 7 :=
  of_native_maps core3651 DegreeTwoThreeSpectrum3904.graph DegreeTwoThreeSpectrum3907.graph
    sourceMap3651 fusedMap3651 sourceMap3651_checked fusedMap3651_checked
    DegreeTwoThreeFiniteComparisons.comparison3651
#print axioms sourceMap3651_checked
#print axioms fusedMap3651_checked
#print axioms certified3651
def sourceMap3651swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3651swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3651swap_checked : acceptsGraphIso
    (source (graph core3651) (root 6) 7 0) DegreeTwoThreeSpectrum3904.graph sourceMap3651swap=true := by decide +kernel
theorem fusedMap3651swap_checked : acceptsGraphIso
    (fused (graph core3651) (root 6) 7 0) DegreeTwoThreeSpectrum3907.graph fusedMap3651swap=true := by decide +kernel
theorem certified3651swap : Certified (graph core3651) (root 6) 7 0 :=
  of_native_maps core3651 DegreeTwoThreeSpectrum3904.graph DegreeTwoThreeSpectrum3907.graph
    sourceMap3651swap fusedMap3651swap sourceMap3651swap_checked fusedMap3651swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3651
#print axioms sourceMap3651swap_checked
#print axioms fusedMap3651swap_checked
#print axioms certified3651swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

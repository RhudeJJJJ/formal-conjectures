/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3324 : Family 9 := level9.get ⟨302,by decide⟩
def sourceMap3324 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3324 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3324_checked : acceptsGraphIso
    (source (graph core3324) (root 9) 0 5) DegreeTwoThreeSpectrum5876.graph sourceMap3324=true := by decide +kernel
theorem fusedMap3324_checked : acceptsGraphIso
    (fused (graph core3324) (root 9) 0 5) DegreeTwoThreeSpectrum5877.graph fusedMap3324=true := by decide +kernel
theorem certified3324 : Certified (graph core3324) (root 9) 0 5 :=
  of_native_maps core3324 DegreeTwoThreeSpectrum5876.graph DegreeTwoThreeSpectrum5877.graph
    sourceMap3324 fusedMap3324 sourceMap3324_checked fusedMap3324_checked
    DegreeTwoThreeFiniteComparisons.comparison3324
#print axioms sourceMap3324_checked
#print axioms fusedMap3324_checked
#print axioms certified3324
def sourceMap3324swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3324swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3324swap_checked : acceptsGraphIso
    (source (graph core3324) (root 9) 5 0) DegreeTwoThreeSpectrum5876.graph sourceMap3324swap=true := by decide +kernel
theorem fusedMap3324swap_checked : acceptsGraphIso
    (fused (graph core3324) (root 9) 5 0) DegreeTwoThreeSpectrum5877.graph fusedMap3324swap=true := by decide +kernel
theorem certified3324swap : Certified (graph core3324) (root 9) 5 0 :=
  of_native_maps core3324 DegreeTwoThreeSpectrum5876.graph DegreeTwoThreeSpectrum5877.graph
    sourceMap3324swap fusedMap3324swap sourceMap3324swap_checked fusedMap3324swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3324
#print axioms sourceMap3324swap_checked
#print axioms fusedMap3324swap_checked
#print axioms certified3324swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

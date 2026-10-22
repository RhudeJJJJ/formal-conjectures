/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3353 : Family 9 := level9.get ⟨380,by decide⟩
def sourceMap3353 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3353 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3353_checked : acceptsGraphIso
    (source (graph core3353) (root 9) 0 5) DegreeTwoThreeSpectrum6311.graph sourceMap3353=true := by decide +kernel
theorem fusedMap3353_checked : acceptsGraphIso
    (fused (graph core3353) (root 9) 0 5) DegreeTwoThreeSpectrum5273.graph fusedMap3353=true := by decide +kernel
theorem certified3353 : Certified (graph core3353) (root 9) 0 5 :=
  of_native_maps core3353 DegreeTwoThreeSpectrum6311.graph DegreeTwoThreeSpectrum5273.graph
    sourceMap3353 fusedMap3353 sourceMap3353_checked fusedMap3353_checked
    DegreeTwoThreeFiniteComparisons.comparison3353
#print axioms sourceMap3353_checked
#print axioms fusedMap3353_checked
#print axioms certified3353
def sourceMap3353swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3353swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3353swap_checked : acceptsGraphIso
    (source (graph core3353) (root 9) 5 0) DegreeTwoThreeSpectrum6311.graph sourceMap3353swap=true := by decide +kernel
theorem fusedMap3353swap_checked : acceptsGraphIso
    (fused (graph core3353) (root 9) 5 0) DegreeTwoThreeSpectrum5273.graph fusedMap3353swap=true := by decide +kernel
theorem certified3353swap : Certified (graph core3353) (root 9) 5 0 :=
  of_native_maps core3353 DegreeTwoThreeSpectrum6311.graph DegreeTwoThreeSpectrum5273.graph
    sourceMap3353swap fusedMap3353swap sourceMap3353swap_checked fusedMap3353swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3353
#print axioms sourceMap3353swap_checked
#print axioms fusedMap3353swap_checked
#print axioms certified3353swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

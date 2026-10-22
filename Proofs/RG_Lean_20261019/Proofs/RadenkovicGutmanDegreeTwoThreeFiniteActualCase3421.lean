/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3421 : Family 9 := level9.get ⟨547,by decide⟩
def sourceMap3421 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3421 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3421_checked : acceptsGraphIso
    (source (graph core3421) (root 9) 0 5) DegreeTwoThreeSpectrum5978.graph sourceMap3421=true := by decide +kernel
theorem fusedMap3421_checked : acceptsGraphIso
    (fused (graph core3421) (root 9) 0 5) DegreeTwoThreeSpectrum5979.graph fusedMap3421=true := by decide +kernel
theorem certified3421 : Certified (graph core3421) (root 9) 0 5 :=
  of_native_maps core3421 DegreeTwoThreeSpectrum5978.graph DegreeTwoThreeSpectrum5979.graph
    sourceMap3421 fusedMap3421 sourceMap3421_checked fusedMap3421_checked
    DegreeTwoThreeFiniteComparisons.comparison3421
#print axioms sourceMap3421_checked
#print axioms fusedMap3421_checked
#print axioms certified3421
def sourceMap3421swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3421swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3421swap_checked : acceptsGraphIso
    (source (graph core3421) (root 9) 5 0) DegreeTwoThreeSpectrum5978.graph sourceMap3421swap=true := by decide +kernel
theorem fusedMap3421swap_checked : acceptsGraphIso
    (fused (graph core3421) (root 9) 5 0) DegreeTwoThreeSpectrum5979.graph fusedMap3421swap=true := by decide +kernel
theorem certified3421swap : Certified (graph core3421) (root 9) 5 0 :=
  of_native_maps core3421 DegreeTwoThreeSpectrum5978.graph DegreeTwoThreeSpectrum5979.graph
    sourceMap3421swap fusedMap3421swap sourceMap3421swap_checked fusedMap3421swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3421
#print axioms sourceMap3421swap_checked
#print axioms fusedMap3421swap_checked
#print axioms certified3421swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

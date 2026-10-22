/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1177 : Family 8 := level8.get ⟨233,by decide⟩
def sourceMap1177 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1177 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1177_checked : acceptsGraphIso
    (source (graph core1177) (root 8) 0 2) DegreeOneSmallSpectrum1907.graph sourceMap1177=true := by decide +kernel
theorem fusedMap1177_checked : acceptsGraphIso
    (fused (graph core1177) (root 8) 0 2) DegreeOneSmallSpectrum1298.graph fusedMap1177=true := by decide +kernel
theorem certified1177 : Certified (graph core1177) (root 8) 0 2 :=
  of_native_maps core1177 DegreeOneSmallSpectrum1907.graph DegreeOneSmallSpectrum1298.graph
    sourceMap1177 fusedMap1177 sourceMap1177_checked fusedMap1177_checked
    DegreeTwoThreeFiniteComparisons.comparison1177
#print axioms sourceMap1177_checked
#print axioms fusedMap1177_checked
#print axioms certified1177
def sourceMap1177swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1177swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1177swap_checked : acceptsGraphIso
    (source (graph core1177) (root 8) 2 0) DegreeOneSmallSpectrum1907.graph sourceMap1177swap=true := by decide +kernel
theorem fusedMap1177swap_checked : acceptsGraphIso
    (fused (graph core1177) (root 8) 2 0) DegreeOneSmallSpectrum1298.graph fusedMap1177swap=true := by decide +kernel
theorem certified1177swap : Certified (graph core1177) (root 8) 2 0 :=
  of_native_maps core1177 DegreeOneSmallSpectrum1907.graph DegreeOneSmallSpectrum1298.graph
    sourceMap1177swap fusedMap1177swap sourceMap1177swap_checked fusedMap1177swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1177
#print axioms sourceMap1177swap_checked
#print axioms fusedMap1177swap_checked
#print axioms certified1177swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

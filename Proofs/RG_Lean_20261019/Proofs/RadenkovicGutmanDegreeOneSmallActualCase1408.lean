/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1408 : Family 9 := level9.get ⟨151,by decide⟩
def sourceMap1408 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1408 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1408_checked : acceptsGraphIso
    (source (graph core1408) (root 9) 0 1) DegreeOneSmallSpectrum1070.graph sourceMap1408=true := by decide +kernel
theorem fusedMap1408_checked : acceptsGraphIso
    (fused (graph core1408) (root 9) 0 1) DegreeOneSmallSpectrum1081.graph fusedMap1408=true := by decide +kernel
theorem certified1408 : Certified (graph core1408) (root 9) 0 1 :=
  of_native_maps core1408 DegreeOneSmallSpectrum1070.graph DegreeOneSmallSpectrum1081.graph
    sourceMap1408 fusedMap1408 sourceMap1408_checked fusedMap1408_checked
    DegreeOneSmallComparisons.comparison1408
#print axioms sourceMap1408_checked
#print axioms fusedMap1408_checked
#print axioms certified1408
def sourceMap1408swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1408swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1408swap_checked : acceptsGraphIso
    (source (graph core1408) (root 9) 1 0) DegreeOneSmallSpectrum1070.graph sourceMap1408swap=true := by decide +kernel
theorem fusedMap1408swap_checked : acceptsGraphIso
    (fused (graph core1408) (root 9) 1 0) DegreeOneSmallSpectrum1081.graph fusedMap1408swap=true := by decide +kernel
theorem certified1408swap : Certified (graph core1408) (root 9) 1 0 :=
  of_native_maps core1408 DegreeOneSmallSpectrum1070.graph DegreeOneSmallSpectrum1081.graph
    sourceMap1408swap fusedMap1408swap sourceMap1408swap_checked fusedMap1408swap_checked
    DegreeOneSmallComparisons.comparison1408
#print axioms sourceMap1408swap_checked
#print axioms fusedMap1408swap_checked
#print axioms certified1408swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

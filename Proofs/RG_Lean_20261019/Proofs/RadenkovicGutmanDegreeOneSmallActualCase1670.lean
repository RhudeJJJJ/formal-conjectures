/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1670 : Family 9 := level9.get ⟨427,by decide⟩
def sourceMap1670 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1670 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1670_checked : acceptsGraphIso
    (source (graph core1670) (root 9) 0 1) DegreeOneSmallSpectrum1923.graph sourceMap1670=true := by decide +kernel
theorem fusedMap1670_checked : acceptsGraphIso
    (fused (graph core1670) (root 9) 0 1) DegreeOneSmallSpectrum1315.graph fusedMap1670=true := by decide +kernel
theorem certified1670 : Certified (graph core1670) (root 9) 0 1 :=
  of_native_maps core1670 DegreeOneSmallSpectrum1923.graph DegreeOneSmallSpectrum1315.graph
    sourceMap1670 fusedMap1670 sourceMap1670_checked fusedMap1670_checked
    DegreeOneSmallComparisons.comparison1670
#print axioms sourceMap1670_checked
#print axioms fusedMap1670_checked
#print axioms certified1670
def sourceMap1670swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1670swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1670swap_checked : acceptsGraphIso
    (source (graph core1670) (root 9) 1 0) DegreeOneSmallSpectrum1923.graph sourceMap1670swap=true := by decide +kernel
theorem fusedMap1670swap_checked : acceptsGraphIso
    (fused (graph core1670) (root 9) 1 0) DegreeOneSmallSpectrum1315.graph fusedMap1670swap=true := by decide +kernel
theorem certified1670swap : Certified (graph core1670) (root 9) 1 0 :=
  of_native_maps core1670 DegreeOneSmallSpectrum1923.graph DegreeOneSmallSpectrum1315.graph
    sourceMap1670swap fusedMap1670swap sourceMap1670swap_checked fusedMap1670swap_checked
    DegreeOneSmallComparisons.comparison1670
#print axioms sourceMap1670swap_checked
#print axioms fusedMap1670swap_checked
#print axioms certified1670swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

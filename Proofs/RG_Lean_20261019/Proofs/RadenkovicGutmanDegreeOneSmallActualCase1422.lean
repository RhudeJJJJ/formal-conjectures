/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1422 : Family 9 := level9.get ⟨162,by decide⟩
def sourceMap1422 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1422 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1422_checked : acceptsGraphIso
    (source (graph core1422) (root 9) 0 1) DegreeOneSmallSpectrum1122.graph sourceMap1422=true := by decide +kernel
theorem fusedMap1422_checked : acceptsGraphIso
    (fused (graph core1422) (root 9) 0 1) DegreeOneSmallSpectrum1124.graph fusedMap1422=true := by decide +kernel
theorem certified1422 : Certified (graph core1422) (root 9) 0 1 :=
  of_native_maps core1422 DegreeOneSmallSpectrum1122.graph DegreeOneSmallSpectrum1124.graph
    sourceMap1422 fusedMap1422 sourceMap1422_checked fusedMap1422_checked
    DegreeOneSmallComparisons.comparison1422
#print axioms sourceMap1422_checked
#print axioms fusedMap1422_checked
#print axioms certified1422
def sourceMap1422swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1422swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1422swap_checked : acceptsGraphIso
    (source (graph core1422) (root 9) 1 0) DegreeOneSmallSpectrum1122.graph sourceMap1422swap=true := by decide +kernel
theorem fusedMap1422swap_checked : acceptsGraphIso
    (fused (graph core1422) (root 9) 1 0) DegreeOneSmallSpectrum1124.graph fusedMap1422swap=true := by decide +kernel
theorem certified1422swap : Certified (graph core1422) (root 9) 1 0 :=
  of_native_maps core1422 DegreeOneSmallSpectrum1122.graph DegreeOneSmallSpectrum1124.graph
    sourceMap1422swap fusedMap1422swap sourceMap1422swap_checked fusedMap1422swap_checked
    DegreeOneSmallComparisons.comparison1422
#print axioms sourceMap1422swap_checked
#print axioms fusedMap1422swap_checked
#print axioms certified1422swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

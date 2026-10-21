/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1508 : Family 9 := level9.get ⟨235,by decide⟩
def sourceMap1508 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1508 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1508_checked : acceptsGraphIso
    (source (graph core1508) (root 9) 0 1) DegreeOneSmallSpectrum1419.graph sourceMap1508=true := by decide +kernel
theorem fusedMap1508_checked : acceptsGraphIso
    (fused (graph core1508) (root 9) 0 1) DegreeOneSmallSpectrum1435.graph fusedMap1508=true := by decide +kernel
theorem certified1508 : Certified (graph core1508) (root 9) 0 1 :=
  of_native_maps core1508 DegreeOneSmallSpectrum1419.graph DegreeOneSmallSpectrum1435.graph
    sourceMap1508 fusedMap1508 sourceMap1508_checked fusedMap1508_checked
    DegreeOneSmallComparisons.comparison1508
#print axioms sourceMap1508_checked
#print axioms fusedMap1508_checked
#print axioms certified1508
def sourceMap1508swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1508swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1508swap_checked : acceptsGraphIso
    (source (graph core1508) (root 9) 1 0) DegreeOneSmallSpectrum1419.graph sourceMap1508swap=true := by decide +kernel
theorem fusedMap1508swap_checked : acceptsGraphIso
    (fused (graph core1508) (root 9) 1 0) DegreeOneSmallSpectrum1435.graph fusedMap1508swap=true := by decide +kernel
theorem certified1508swap : Certified (graph core1508) (root 9) 1 0 :=
  of_native_maps core1508 DegreeOneSmallSpectrum1419.graph DegreeOneSmallSpectrum1435.graph
    sourceMap1508swap fusedMap1508swap sourceMap1508swap_checked fusedMap1508swap_checked
    DegreeOneSmallComparisons.comparison1508
#print axioms sourceMap1508swap_checked
#print axioms fusedMap1508swap_checked
#print axioms certified1508swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

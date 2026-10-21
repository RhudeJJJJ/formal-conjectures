/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1404 : Family 9 := level9.get ⟨148,by decide⟩
def sourceMap1404 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1404 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1404_checked : acceptsGraphIso
    (source (graph core1404) (root 9) 0 1) DegreeOneSmallSpectrum1047.graph sourceMap1404=true := by decide +kernel
theorem fusedMap1404_checked : acceptsGraphIso
    (fused (graph core1404) (root 9) 0 1) DegreeOneSmallSpectrum1049.graph fusedMap1404=true := by decide +kernel
theorem certified1404 : Certified (graph core1404) (root 9) 0 1 :=
  of_native_maps core1404 DegreeOneSmallSpectrum1047.graph DegreeOneSmallSpectrum1049.graph
    sourceMap1404 fusedMap1404 sourceMap1404_checked fusedMap1404_checked
    DegreeOneSmallComparisons.comparison1404
#print axioms sourceMap1404_checked
#print axioms fusedMap1404_checked
#print axioms certified1404
def sourceMap1404swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1404swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1404swap_checked : acceptsGraphIso
    (source (graph core1404) (root 9) 1 0) DegreeOneSmallSpectrum1047.graph sourceMap1404swap=true := by decide +kernel
theorem fusedMap1404swap_checked : acceptsGraphIso
    (fused (graph core1404) (root 9) 1 0) DegreeOneSmallSpectrum1049.graph fusedMap1404swap=true := by decide +kernel
theorem certified1404swap : Certified (graph core1404) (root 9) 1 0 :=
  of_native_maps core1404 DegreeOneSmallSpectrum1047.graph DegreeOneSmallSpectrum1049.graph
    sourceMap1404swap fusedMap1404swap sourceMap1404swap_checked fusedMap1404swap_checked
    DegreeOneSmallComparisons.comparison1404
#print axioms sourceMap1404swap_checked
#print axioms fusedMap1404swap_checked
#print axioms certified1404swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

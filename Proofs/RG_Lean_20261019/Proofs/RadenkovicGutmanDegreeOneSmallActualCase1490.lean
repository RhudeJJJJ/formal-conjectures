/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1490 : Family 9 := level9.get ⟨221,by decide⟩
def sourceMap1490 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1490 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1490_checked : acceptsGraphIso
    (source (graph core1490) (root 9) 0 1) DegreeOneSmallSpectrum1381.graph sourceMap1490=true := by decide +kernel
theorem fusedMap1490_checked : acceptsGraphIso
    (fused (graph core1490) (root 9) 0 1) DegreeOneSmallSpectrum1392.graph fusedMap1490=true := by decide +kernel
theorem certified1490 : Certified (graph core1490) (root 9) 0 1 :=
  of_native_maps core1490 DegreeOneSmallSpectrum1381.graph DegreeOneSmallSpectrum1392.graph
    sourceMap1490 fusedMap1490 sourceMap1490_checked fusedMap1490_checked
    DegreeOneSmallComparisons.comparison1490
#print axioms sourceMap1490_checked
#print axioms fusedMap1490_checked
#print axioms certified1490
def sourceMap1490swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1490swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1490swap_checked : acceptsGraphIso
    (source (graph core1490) (root 9) 1 0) DegreeOneSmallSpectrum1381.graph sourceMap1490swap=true := by decide +kernel
theorem fusedMap1490swap_checked : acceptsGraphIso
    (fused (graph core1490) (root 9) 1 0) DegreeOneSmallSpectrum1392.graph fusedMap1490swap=true := by decide +kernel
theorem certified1490swap : Certified (graph core1490) (root 9) 1 0 :=
  of_native_maps core1490 DegreeOneSmallSpectrum1381.graph DegreeOneSmallSpectrum1392.graph
    sourceMap1490swap fusedMap1490swap sourceMap1490swap_checked fusedMap1490swap_checked
    DegreeOneSmallComparisons.comparison1490
#print axioms sourceMap1490swap_checked
#print axioms fusedMap1490swap_checked
#print axioms certified1490swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

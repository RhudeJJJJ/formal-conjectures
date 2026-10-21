/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1584 : Family 9 := level9.get ⟨325,by decide⟩
def sourceMap1584 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1584 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1584_checked : acceptsGraphIso
    (source (graph core1584) (root 9) 0 1) DegreeOneSmallSpectrum1595.graph sourceMap1584=true := by decide +kernel
theorem fusedMap1584_checked : acceptsGraphIso
    (fused (graph core1584) (root 9) 0 1) DegreeOneSmallSpectrum993.graph fusedMap1584=true := by decide +kernel
theorem certified1584 : Certified (graph core1584) (root 9) 0 1 :=
  of_native_maps core1584 DegreeOneSmallSpectrum1595.graph DegreeOneSmallSpectrum993.graph
    sourceMap1584 fusedMap1584 sourceMap1584_checked fusedMap1584_checked
    DegreeOneSmallComparisons.comparison1584
#print axioms sourceMap1584_checked
#print axioms fusedMap1584_checked
#print axioms certified1584
def sourceMap1584swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1584swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1584swap_checked : acceptsGraphIso
    (source (graph core1584) (root 9) 1 0) DegreeOneSmallSpectrum1595.graph sourceMap1584swap=true := by decide +kernel
theorem fusedMap1584swap_checked : acceptsGraphIso
    (fused (graph core1584) (root 9) 1 0) DegreeOneSmallSpectrum993.graph fusedMap1584swap=true := by decide +kernel
theorem certified1584swap : Certified (graph core1584) (root 9) 1 0 :=
  of_native_maps core1584 DegreeOneSmallSpectrum1595.graph DegreeOneSmallSpectrum993.graph
    sourceMap1584swap fusedMap1584swap sourceMap1584swap_checked fusedMap1584swap_checked
    DegreeOneSmallComparisons.comparison1584
#print axioms sourceMap1584swap_checked
#print axioms fusedMap1584swap_checked
#print axioms certified1584swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

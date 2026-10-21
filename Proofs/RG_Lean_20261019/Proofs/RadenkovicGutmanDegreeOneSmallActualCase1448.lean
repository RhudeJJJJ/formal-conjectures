/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1448 : Family 9 := level9.get ⟨182,by decide⟩
def sourceMap1448 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1448 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1448_checked : acceptsGraphIso
    (source (graph core1448) (root 9) 0 1) DegreeOneSmallSpectrum1235.graph sourceMap1448=true := by decide +kernel
theorem fusedMap1448_checked : acceptsGraphIso
    (fused (graph core1448) (root 9) 0 1) DegreeOneSmallSpectrum1246.graph fusedMap1448=true := by decide +kernel
theorem certified1448 : Certified (graph core1448) (root 9) 0 1 :=
  of_native_maps core1448 DegreeOneSmallSpectrum1235.graph DegreeOneSmallSpectrum1246.graph
    sourceMap1448 fusedMap1448 sourceMap1448_checked fusedMap1448_checked
    DegreeOneSmallComparisons.comparison1448
#print axioms sourceMap1448_checked
#print axioms fusedMap1448_checked
#print axioms certified1448
def sourceMap1448swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1448swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1448swap_checked : acceptsGraphIso
    (source (graph core1448) (root 9) 1 0) DegreeOneSmallSpectrum1235.graph sourceMap1448swap=true := by decide +kernel
theorem fusedMap1448swap_checked : acceptsGraphIso
    (fused (graph core1448) (root 9) 1 0) DegreeOneSmallSpectrum1246.graph fusedMap1448swap=true := by decide +kernel
theorem certified1448swap : Certified (graph core1448) (root 9) 1 0 :=
  of_native_maps core1448 DegreeOneSmallSpectrum1235.graph DegreeOneSmallSpectrum1246.graph
    sourceMap1448swap fusedMap1448swap sourceMap1448swap_checked fusedMap1448swap_checked
    DegreeOneSmallComparisons.comparison1448
#print axioms sourceMap1448swap_checked
#print axioms fusedMap1448swap_checked
#print axioms certified1448swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

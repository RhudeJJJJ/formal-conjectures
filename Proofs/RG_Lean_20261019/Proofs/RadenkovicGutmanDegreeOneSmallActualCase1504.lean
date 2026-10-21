/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1504 : Family 9 := level9.get ⟨232,by decide⟩
def sourceMap1504 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1504 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1504_checked : acceptsGraphIso
    (source (graph core1504) (root 9) 0 1) DegreeOneSmallSpectrum1419.graph sourceMap1504=true := by decide +kernel
theorem fusedMap1504_checked : acceptsGraphIso
    (fused (graph core1504) (root 9) 0 1) DegreeOneSmallSpectrum1424.graph fusedMap1504=true := by decide +kernel
theorem certified1504 : Certified (graph core1504) (root 9) 0 1 :=
  of_native_maps core1504 DegreeOneSmallSpectrum1419.graph DegreeOneSmallSpectrum1424.graph
    sourceMap1504 fusedMap1504 sourceMap1504_checked fusedMap1504_checked
    DegreeOneSmallComparisons.comparison1504
#print axioms sourceMap1504_checked
#print axioms fusedMap1504_checked
#print axioms certified1504
def sourceMap1504swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1504swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1504swap_checked : acceptsGraphIso
    (source (graph core1504) (root 9) 1 0) DegreeOneSmallSpectrum1419.graph sourceMap1504swap=true := by decide +kernel
theorem fusedMap1504swap_checked : acceptsGraphIso
    (fused (graph core1504) (root 9) 1 0) DegreeOneSmallSpectrum1424.graph fusedMap1504swap=true := by decide +kernel
theorem certified1504swap : Certified (graph core1504) (root 9) 1 0 :=
  of_native_maps core1504 DegreeOneSmallSpectrum1419.graph DegreeOneSmallSpectrum1424.graph
    sourceMap1504swap fusedMap1504swap sourceMap1504swap_checked fusedMap1504swap_checked
    DegreeOneSmallComparisons.comparison1504
#print axioms sourceMap1504swap_checked
#print axioms fusedMap1504swap_checked
#print axioms certified1504swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

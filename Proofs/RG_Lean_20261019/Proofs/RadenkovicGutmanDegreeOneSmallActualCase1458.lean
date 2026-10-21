/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1458 : Family 9 := level9.get ⟨191,by decide⟩
def sourceMap1458 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1458 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1458_checked : acceptsGraphIso
    (source (graph core1458) (root 9) 0 1) DegreeOneSmallSpectrum1269.graph sourceMap1458=true := by decide +kernel
theorem fusedMap1458_checked : acceptsGraphIso
    (fused (graph core1458) (root 9) 0 1) DegreeOneSmallSpectrum1291.graph fusedMap1458=true := by decide +kernel
theorem certified1458 : Certified (graph core1458) (root 9) 0 1 :=
  of_native_maps core1458 DegreeOneSmallSpectrum1269.graph DegreeOneSmallSpectrum1291.graph
    sourceMap1458 fusedMap1458 sourceMap1458_checked fusedMap1458_checked
    DegreeOneSmallComparisons.comparison1458
#print axioms sourceMap1458_checked
#print axioms fusedMap1458_checked
#print axioms certified1458
def sourceMap1458swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1458swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1458swap_checked : acceptsGraphIso
    (source (graph core1458) (root 9) 1 0) DegreeOneSmallSpectrum1269.graph sourceMap1458swap=true := by decide +kernel
theorem fusedMap1458swap_checked : acceptsGraphIso
    (fused (graph core1458) (root 9) 1 0) DegreeOneSmallSpectrum1291.graph fusedMap1458swap=true := by decide +kernel
theorem certified1458swap : Certified (graph core1458) (root 9) 1 0 :=
  of_native_maps core1458 DegreeOneSmallSpectrum1269.graph DegreeOneSmallSpectrum1291.graph
    sourceMap1458swap fusedMap1458swap sourceMap1458swap_checked fusedMap1458swap_checked
    DegreeOneSmallComparisons.comparison1458
#print axioms sourceMap1458swap_checked
#print axioms fusedMap1458swap_checked
#print axioms certified1458swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

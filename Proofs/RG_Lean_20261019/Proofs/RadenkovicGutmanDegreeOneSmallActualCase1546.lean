/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1546 : Family 9 := level9.get ⟨275,by decide⟩
def sourceMap1546 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1546 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1546_checked : acceptsGraphIso
    (source (graph core1546) (root 9) 0 1) DegreeOneSmallSpectrum1397.graph sourceMap1546=true := by decide +kernel
theorem fusedMap1546_checked : acceptsGraphIso
    (fused (graph core1546) (root 9) 0 1) DegreeOneSmallSpectrum1504.graph fusedMap1546=true := by decide +kernel
theorem certified1546 : Certified (graph core1546) (root 9) 0 1 :=
  of_native_maps core1546 DegreeOneSmallSpectrum1397.graph DegreeOneSmallSpectrum1504.graph
    sourceMap1546 fusedMap1546 sourceMap1546_checked fusedMap1546_checked
    DegreeOneSmallComparisons.comparison1546
#print axioms sourceMap1546_checked
#print axioms fusedMap1546_checked
#print axioms certified1546
def sourceMap1546swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1546swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1546swap_checked : acceptsGraphIso
    (source (graph core1546) (root 9) 1 0) DegreeOneSmallSpectrum1397.graph sourceMap1546swap=true := by decide +kernel
theorem fusedMap1546swap_checked : acceptsGraphIso
    (fused (graph core1546) (root 9) 1 0) DegreeOneSmallSpectrum1504.graph fusedMap1546swap=true := by decide +kernel
theorem certified1546swap : Certified (graph core1546) (root 9) 1 0 :=
  of_native_maps core1546 DegreeOneSmallSpectrum1397.graph DegreeOneSmallSpectrum1504.graph
    sourceMap1546swap fusedMap1546swap sourceMap1546swap_checked fusedMap1546swap_checked
    DegreeOneSmallComparisons.comparison1546
#print axioms sourceMap1546swap_checked
#print axioms fusedMap1546swap_checked
#print axioms certified1546swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

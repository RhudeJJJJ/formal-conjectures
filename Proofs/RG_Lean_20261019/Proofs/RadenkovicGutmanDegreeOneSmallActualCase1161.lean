/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1161 : Family 8 := level8.get ⟨199,by decide⟩
def sourceMap1161 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1161 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1161_checked : acceptsGraphIso
    (source (graph core1161) (root 8) 0 2) DegreeOneSmallSpectrum1646.graph sourceMap1161=true := by decide +kernel
theorem fusedMap1161_checked : acceptsGraphIso
    (fused (graph core1161) (root 8) 0 2) DegreeOneSmallSpectrum1016.graph fusedMap1161=true := by decide +kernel
theorem certified1161 : Certified (graph core1161) (root 8) 0 2 :=
  of_native_maps core1161 DegreeOneSmallSpectrum1646.graph DegreeOneSmallSpectrum1016.graph
    sourceMap1161 fusedMap1161 sourceMap1161_checked fusedMap1161_checked
    DegreeOneSmallComparisons.comparison1161
#print axioms sourceMap1161_checked
#print axioms fusedMap1161_checked
#print axioms certified1161
def sourceMap1161swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1161swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1161swap_checked : acceptsGraphIso
    (source (graph core1161) (root 8) 2 0) DegreeOneSmallSpectrum1646.graph sourceMap1161swap=true := by decide +kernel
theorem fusedMap1161swap_checked : acceptsGraphIso
    (fused (graph core1161) (root 8) 2 0) DegreeOneSmallSpectrum1016.graph fusedMap1161swap=true := by decide +kernel
theorem certified1161swap : Certified (graph core1161) (root 8) 2 0 :=
  of_native_maps core1161 DegreeOneSmallSpectrum1646.graph DegreeOneSmallSpectrum1016.graph
    sourceMap1161swap fusedMap1161swap sourceMap1161swap_checked fusedMap1161swap_checked
    DegreeOneSmallComparisons.comparison1161
#print axioms sourceMap1161swap_checked
#print axioms fusedMap1161swap_checked
#print axioms certified1161swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

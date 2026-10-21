/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1081 : Family 8 := level8.get ⟨141,by decide⟩
def sourceMap1081 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1081 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1081_checked : acceptsGraphIso
    (source (graph core1081) (root 8) 0 2) DegreeOneSmallSpectrum1352.graph sourceMap1081=true := by decide +kernel
theorem fusedMap1081_checked : acceptsGraphIso
    (fused (graph core1081) (root 8) 0 2) DegreeOneSmallSpectrum1353.graph fusedMap1081=true := by decide +kernel
theorem certified1081 : Certified (graph core1081) (root 8) 0 2 :=
  of_native_maps core1081 DegreeOneSmallSpectrum1352.graph DegreeOneSmallSpectrum1353.graph
    sourceMap1081 fusedMap1081 sourceMap1081_checked fusedMap1081_checked
    DegreeOneSmallComparisons.comparison1081
#print axioms sourceMap1081_checked
#print axioms fusedMap1081_checked
#print axioms certified1081
def sourceMap1081swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1081swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1081swap_checked : acceptsGraphIso
    (source (graph core1081) (root 8) 2 0) DegreeOneSmallSpectrum1352.graph sourceMap1081swap=true := by decide +kernel
theorem fusedMap1081swap_checked : acceptsGraphIso
    (fused (graph core1081) (root 8) 2 0) DegreeOneSmallSpectrum1353.graph fusedMap1081swap=true := by decide +kernel
theorem certified1081swap : Certified (graph core1081) (root 8) 2 0 :=
  of_native_maps core1081 DegreeOneSmallSpectrum1352.graph DegreeOneSmallSpectrum1353.graph
    sourceMap1081swap fusedMap1081swap sourceMap1081swap_checked fusedMap1081swap_checked
    DegreeOneSmallComparisons.comparison1081
#print axioms sourceMap1081swap_checked
#print axioms fusedMap1081swap_checked
#print axioms certified1081swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

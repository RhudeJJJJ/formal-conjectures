/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1125 : Family 8 := level8.get ⟨166,by decide⟩
def sourceMap1125 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1125 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1125_checked : acceptsGraphIso
    (source (graph core1125) (root 8) 0 2) DegreeOneSmallSpectrum1477.graph sourceMap1125=true := by decide +kernel
theorem fusedMap1125_checked : acceptsGraphIso
    (fused (graph core1125) (root 8) 0 2) DegreeOneSmallSpectrum1478.graph fusedMap1125=true := by decide +kernel
theorem certified1125 : Certified (graph core1125) (root 8) 0 2 :=
  of_native_maps core1125 DegreeOneSmallSpectrum1477.graph DegreeOneSmallSpectrum1478.graph
    sourceMap1125 fusedMap1125 sourceMap1125_checked fusedMap1125_checked
    DegreeOneSmallComparisons.comparison1125
#print axioms sourceMap1125_checked
#print axioms fusedMap1125_checked
#print axioms certified1125
def sourceMap1125swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1125swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1125swap_checked : acceptsGraphIso
    (source (graph core1125) (root 8) 2 0) DegreeOneSmallSpectrum1477.graph sourceMap1125swap=true := by decide +kernel
theorem fusedMap1125swap_checked : acceptsGraphIso
    (fused (graph core1125) (root 8) 2 0) DegreeOneSmallSpectrum1478.graph fusedMap1125swap=true := by decide +kernel
theorem certified1125swap : Certified (graph core1125) (root 8) 2 0 :=
  of_native_maps core1125 DegreeOneSmallSpectrum1477.graph DegreeOneSmallSpectrum1478.graph
    sourceMap1125swap fusedMap1125swap sourceMap1125swap_checked fusedMap1125swap_checked
    DegreeOneSmallComparisons.comparison1125
#print axioms sourceMap1125swap_checked
#print axioms fusedMap1125swap_checked
#print axioms certified1125swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

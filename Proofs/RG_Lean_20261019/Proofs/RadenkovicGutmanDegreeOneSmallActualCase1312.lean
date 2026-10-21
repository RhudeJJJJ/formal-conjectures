/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1312 : Family 9 := level9.get ⟨75,by decide⟩
def sourceMap1312 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1312 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1312_checked : acceptsGraphIso
    (source (graph core1312) (root 9) 0 1) DegreeOneSmallSpectrum1376.graph sourceMap1312=true := by decide +kernel
theorem fusedMap1312_checked : acceptsGraphIso
    (fused (graph core1312) (root 9) 0 1) DegreeOneSmallSpectrum917.graph fusedMap1312=true := by decide +kernel
theorem certified1312 : Certified (graph core1312) (root 9) 0 1 :=
  of_native_maps core1312 DegreeOneSmallSpectrum1376.graph DegreeOneSmallSpectrum917.graph
    sourceMap1312 fusedMap1312 sourceMap1312_checked fusedMap1312_checked
    DegreeOneSmallComparisons.comparison1312
#print axioms sourceMap1312_checked
#print axioms fusedMap1312_checked
#print axioms certified1312
def sourceMap1312swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1312swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1312swap_checked : acceptsGraphIso
    (source (graph core1312) (root 9) 1 0) DegreeOneSmallSpectrum1376.graph sourceMap1312swap=true := by decide +kernel
theorem fusedMap1312swap_checked : acceptsGraphIso
    (fused (graph core1312) (root 9) 1 0) DegreeOneSmallSpectrum917.graph fusedMap1312swap=true := by decide +kernel
theorem certified1312swap : Certified (graph core1312) (root 9) 1 0 :=
  of_native_maps core1312 DegreeOneSmallSpectrum1376.graph DegreeOneSmallSpectrum917.graph
    sourceMap1312swap fusedMap1312swap sourceMap1312swap_checked fusedMap1312swap_checked
    DegreeOneSmallComparisons.comparison1312
#print axioms sourceMap1312swap_checked
#print axioms fusedMap1312swap_checked
#print axioms certified1312swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

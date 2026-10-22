/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1084 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap1084 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap1084 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1084_checked : acceptsGraphIso
    (source (graph core1084) (root 7) 0 2) DegreeOneSmallSpectrum765.graph sourceMap1084=true := by decide +kernel
theorem fusedMap1084_checked : acceptsGraphIso
    (fused (graph core1084) (root 7) 0 2) DegreeOneSmallSpectrum458.graph fusedMap1084=true := by decide +kernel
theorem certified1084 : Certified (graph core1084) (root 7) 0 2 :=
  of_native_maps core1084 DegreeOneSmallSpectrum765.graph DegreeOneSmallSpectrum458.graph
    sourceMap1084 fusedMap1084 sourceMap1084_checked fusedMap1084_checked
    DegreeTwoThreeFiniteComparisons.comparison1084
#print axioms sourceMap1084_checked
#print axioms fusedMap1084_checked
#print axioms certified1084
def sourceMap1084swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap1084swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1084swap_checked : acceptsGraphIso
    (source (graph core1084) (root 7) 2 0) DegreeOneSmallSpectrum765.graph sourceMap1084swap=true := by decide +kernel
theorem fusedMap1084swap_checked : acceptsGraphIso
    (fused (graph core1084) (root 7) 2 0) DegreeOneSmallSpectrum458.graph fusedMap1084swap=true := by decide +kernel
theorem certified1084swap : Certified (graph core1084) (root 7) 2 0 :=
  of_native_maps core1084 DegreeOneSmallSpectrum765.graph DegreeOneSmallSpectrum458.graph
    sourceMap1084swap fusedMap1084swap sourceMap1084swap_checked fusedMap1084swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1084
#print axioms sourceMap1084swap_checked
#print axioms fusedMap1084swap_checked
#print axioms certified1084swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1078 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap1078 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1078 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1078_checked : acceptsGraphIso
    (source (graph core1078) (root 7) 0 2) DegreeOneSmallSpectrum625.graph sourceMap1078=true := by decide +kernel
theorem fusedMap1078_checked : acceptsGraphIso
    (fused (graph core1078) (root 7) 0 2) DegreeOneSmallSpectrum400.graph fusedMap1078=true := by decide +kernel
theorem certified1078 : Certified (graph core1078) (root 7) 0 2 :=
  of_native_maps core1078 DegreeOneSmallSpectrum625.graph DegreeOneSmallSpectrum400.graph
    sourceMap1078 fusedMap1078 sourceMap1078_checked fusedMap1078_checked
    DegreeTwoThreeFiniteComparisons.comparison1078
#print axioms sourceMap1078_checked
#print axioms fusedMap1078_checked
#print axioms certified1078
def sourceMap1078swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1078swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1078swap_checked : acceptsGraphIso
    (source (graph core1078) (root 7) 2 0) DegreeOneSmallSpectrum625.graph sourceMap1078swap=true := by decide +kernel
theorem fusedMap1078swap_checked : acceptsGraphIso
    (fused (graph core1078) (root 7) 2 0) DegreeOneSmallSpectrum400.graph fusedMap1078swap=true := by decide +kernel
theorem certified1078swap : Certified (graph core1078) (root 7) 2 0 :=
  of_native_maps core1078 DegreeOneSmallSpectrum625.graph DegreeOneSmallSpectrum400.graph
    sourceMap1078swap fusedMap1078swap sourceMap1078swap_checked fusedMap1078swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1078
#print axioms sourceMap1078swap_checked
#print axioms fusedMap1078swap_checked
#print axioms certified1078swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1052 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap1052 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8] (sourceLabel 6 0 2 v)
def fusedMap1052 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1052_checked : acceptsGraphIso
    (source (graph core1052) (root 6) 0 2) DegreeOneSmallSpectrum338.graph sourceMap1052=true := by decide +kernel
theorem fusedMap1052_checked : acceptsGraphIso
    (fused (graph core1052) (root 6) 0 2) DegreeOneSmallSpectrum204.graph fusedMap1052=true := by decide +kernel
theorem certified1052 : Certified (graph core1052) (root 6) 0 2 :=
  of_native_maps core1052 DegreeOneSmallSpectrum338.graph DegreeOneSmallSpectrum204.graph
    sourceMap1052 fusedMap1052 sourceMap1052_checked fusedMap1052_checked
    DegreeTwoThreeFiniteComparisons.comparison1052
#print axioms sourceMap1052_checked
#print axioms fusedMap1052_checked
#print axioms certified1052
def sourceMap1052swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8,10] (sourceLabel 6 2 0 v)
def fusedMap1052swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1052swap_checked : acceptsGraphIso
    (source (graph core1052) (root 6) 2 0) DegreeOneSmallSpectrum338.graph sourceMap1052swap=true := by decide +kernel
theorem fusedMap1052swap_checked : acceptsGraphIso
    (fused (graph core1052) (root 6) 2 0) DegreeOneSmallSpectrum204.graph fusedMap1052swap=true := by decide +kernel
theorem certified1052swap : Certified (graph core1052) (root 6) 2 0 :=
  of_native_maps core1052 DegreeOneSmallSpectrum338.graph DegreeOneSmallSpectrum204.graph
    sourceMap1052swap fusedMap1052swap sourceMap1052swap_checked fusedMap1052swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1052
#print axioms sourceMap1052swap_checked
#print axioms fusedMap1052swap_checked
#print axioms certified1052swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

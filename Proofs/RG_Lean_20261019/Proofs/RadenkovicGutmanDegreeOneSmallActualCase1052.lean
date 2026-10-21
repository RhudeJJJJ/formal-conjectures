/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1052 : Family 8 := level8.get ⟨122,by decide⟩
def sourceMap1052 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,8,6,7] (sourceLabel 8 0 1 v)
def fusedMap1052 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1052_checked : acceptsGraphIso
    (source (graph core1052) (root 8) 0 1) DegreeOneSmallSpectrum763.graph sourceMap1052=true := by decide +kernel
theorem fusedMap1052_checked : acceptsGraphIso
    (fused (graph core1052) (root 8) 0 1) DegreeOneSmallSpectrum460.graph fusedMap1052=true := by decide +kernel
theorem certified1052 : Certified (graph core1052) (root 8) 0 1 :=
  of_native_maps core1052 DegreeOneSmallSpectrum763.graph DegreeOneSmallSpectrum460.graph
    sourceMap1052 fusedMap1052 sourceMap1052_checked fusedMap1052_checked
    DegreeOneSmallComparisons.comparison1052
#print axioms sourceMap1052_checked
#print axioms fusedMap1052_checked
#print axioms certified1052
def sourceMap1052swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8] (sourceLabel 8 1 0 v)
def fusedMap1052swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1052swap_checked : acceptsGraphIso
    (source (graph core1052) (root 8) 1 0) DegreeOneSmallSpectrum763.graph sourceMap1052swap=true := by decide +kernel
theorem fusedMap1052swap_checked : acceptsGraphIso
    (fused (graph core1052) (root 8) 1 0) DegreeOneSmallSpectrum460.graph fusedMap1052swap=true := by decide +kernel
theorem certified1052swap : Certified (graph core1052) (root 8) 1 0 :=
  of_native_maps core1052 DegreeOneSmallSpectrum763.graph DegreeOneSmallSpectrum460.graph
    sourceMap1052swap fusedMap1052swap sourceMap1052swap_checked fusedMap1052swap_checked
    DegreeOneSmallComparisons.comparison1052
#print axioms sourceMap1052swap_checked
#print axioms fusedMap1052swap_checked
#print axioms certified1052swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

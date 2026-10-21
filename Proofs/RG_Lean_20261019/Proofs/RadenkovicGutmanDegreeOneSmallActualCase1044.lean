/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1044 : Family 8 := level8.get ⟨120,by decide⟩
def sourceMap1044 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,8,6,7] (sourceLabel 8 0 1 v)
def fusedMap1044 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1044_checked : acceptsGraphIso
    (source (graph core1044) (root 8) 0 1) DegreeOneSmallSpectrum761.graph sourceMap1044=true := by decide +kernel
theorem fusedMap1044_checked : acceptsGraphIso
    (fused (graph core1044) (root 8) 0 1) DegreeOneSmallSpectrum458.graph fusedMap1044=true := by decide +kernel
theorem certified1044 : Certified (graph core1044) (root 8) 0 1 :=
  of_native_maps core1044 DegreeOneSmallSpectrum761.graph DegreeOneSmallSpectrum458.graph
    sourceMap1044 fusedMap1044 sourceMap1044_checked fusedMap1044_checked
    DegreeOneSmallComparisons.comparison1044
#print axioms sourceMap1044_checked
#print axioms fusedMap1044_checked
#print axioms certified1044
def sourceMap1044swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8] (sourceLabel 8 1 0 v)
def fusedMap1044swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1044swap_checked : acceptsGraphIso
    (source (graph core1044) (root 8) 1 0) DegreeOneSmallSpectrum761.graph sourceMap1044swap=true := by decide +kernel
theorem fusedMap1044swap_checked : acceptsGraphIso
    (fused (graph core1044) (root 8) 1 0) DegreeOneSmallSpectrum458.graph fusedMap1044swap=true := by decide +kernel
theorem certified1044swap : Certified (graph core1044) (root 8) 1 0 :=
  of_native_maps core1044 DegreeOneSmallSpectrum761.graph DegreeOneSmallSpectrum458.graph
    sourceMap1044swap fusedMap1044swap sourceMap1044swap_checked fusedMap1044swap_checked
    DegreeOneSmallComparisons.comparison1044
#print axioms sourceMap1044swap_checked
#print axioms fusedMap1044swap_checked
#print axioms certified1044swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

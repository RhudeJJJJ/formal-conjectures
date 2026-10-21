/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1092 : Family 8 := level8.get ⟨145,by decide⟩
def sourceMap1092 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap1092 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1092_checked : acceptsGraphIso
    (source (graph core1092) (root 8) 0 1) DegreeOneSmallSpectrum807.graph sourceMap1092=true := by decide +kernel
theorem fusedMap1092_checked : acceptsGraphIso
    (fused (graph core1092) (root 8) 0 1) DegreeOneSmallSpectrum525.graph fusedMap1092=true := by decide +kernel
theorem certified1092 : Certified (graph core1092) (root 8) 0 1 :=
  of_native_maps core1092 DegreeOneSmallSpectrum807.graph DegreeOneSmallSpectrum525.graph
    sourceMap1092 fusedMap1092 sourceMap1092_checked fusedMap1092_checked
    DegreeOneSmallComparisons.comparison1092
#print axioms sourceMap1092_checked
#print axioms fusedMap1092_checked
#print axioms certified1092
def sourceMap1092swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap1092swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1092swap_checked : acceptsGraphIso
    (source (graph core1092) (root 8) 1 0) DegreeOneSmallSpectrum807.graph sourceMap1092swap=true := by decide +kernel
theorem fusedMap1092swap_checked : acceptsGraphIso
    (fused (graph core1092) (root 8) 1 0) DegreeOneSmallSpectrum525.graph fusedMap1092swap=true := by decide +kernel
theorem certified1092swap : Certified (graph core1092) (root 8) 1 0 :=
  of_native_maps core1092 DegreeOneSmallSpectrum807.graph DegreeOneSmallSpectrum525.graph
    sourceMap1092swap fusedMap1092swap sourceMap1092swap_checked fusedMap1092swap_checked
    DegreeOneSmallComparisons.comparison1092
#print axioms sourceMap1092swap_checked
#print axioms fusedMap1092swap_checked
#print axioms certified1092swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

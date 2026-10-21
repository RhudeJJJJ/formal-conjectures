/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1210 : Family 9 := level9.get ⟨7,by decide⟩
def sourceMap1210 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (sourceLabel 9 0 1 v)
def fusedMap1210 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (fusedLabel 9 0 1 v)
theorem sourceMap1210_checked : acceptsGraphIso
    (source (graph core1210) (root 9) 0 1) DegreeOneSmallSpectrum929.graph sourceMap1210=true := by decide +kernel
theorem fusedMap1210_checked : acceptsGraphIso
    (fused (graph core1210) (root 9) 0 1) DegreeOneSmallSpectrum859.graph fusedMap1210=true := by decide +kernel
theorem certified1210 : Certified (graph core1210) (root 9) 0 1 :=
  of_native_maps core1210 DegreeOneSmallSpectrum929.graph DegreeOneSmallSpectrum859.graph
    sourceMap1210 fusedMap1210 sourceMap1210_checked fusedMap1210_checked
    DegreeOneSmallComparisons.comparison1210
#print axioms sourceMap1210_checked
#print axioms fusedMap1210_checked
#print axioms certified1210
def sourceMap1210swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 9 1 0 v)
def fusedMap1210swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (fusedLabel 9 1 0 v)
theorem sourceMap1210swap_checked : acceptsGraphIso
    (source (graph core1210) (root 9) 1 0) DegreeOneSmallSpectrum929.graph sourceMap1210swap=true := by decide +kernel
theorem fusedMap1210swap_checked : acceptsGraphIso
    (fused (graph core1210) (root 9) 1 0) DegreeOneSmallSpectrum859.graph fusedMap1210swap=true := by decide +kernel
theorem certified1210swap : Certified (graph core1210) (root 9) 1 0 :=
  of_native_maps core1210 DegreeOneSmallSpectrum929.graph DegreeOneSmallSpectrum859.graph
    sourceMap1210swap fusedMap1210swap sourceMap1210swap_checked fusedMap1210swap_checked
    DegreeOneSmallComparisons.comparison1210
#print axioms sourceMap1210swap_checked
#print axioms fusedMap1210swap_checked
#print axioms certified1210swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

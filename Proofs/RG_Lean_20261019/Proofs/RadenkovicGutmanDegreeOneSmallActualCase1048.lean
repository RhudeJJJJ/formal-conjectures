/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1048 : Family 8 := level8.get ⟨121,by decide⟩
def sourceMap1048 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,8,6,7] (sourceLabel 8 0 1 v)
def fusedMap1048 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1048_checked : acceptsGraphIso
    (source (graph core1048) (root 8) 0 1) DegreeOneSmallSpectrum762.graph sourceMap1048=true := by decide +kernel
theorem fusedMap1048_checked : acceptsGraphIso
    (fused (graph core1048) (root 8) 0 1) DegreeOneSmallSpectrum459.graph fusedMap1048=true := by decide +kernel
theorem certified1048 : Certified (graph core1048) (root 8) 0 1 :=
  of_native_maps core1048 DegreeOneSmallSpectrum762.graph DegreeOneSmallSpectrum459.graph
    sourceMap1048 fusedMap1048 sourceMap1048_checked fusedMap1048_checked
    DegreeOneSmallComparisons.comparison1048
#print axioms sourceMap1048_checked
#print axioms fusedMap1048_checked
#print axioms certified1048
def sourceMap1048swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8] (sourceLabel 8 1 0 v)
def fusedMap1048swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1048swap_checked : acceptsGraphIso
    (source (graph core1048) (root 8) 1 0) DegreeOneSmallSpectrum762.graph sourceMap1048swap=true := by decide +kernel
theorem fusedMap1048swap_checked : acceptsGraphIso
    (fused (graph core1048) (root 8) 1 0) DegreeOneSmallSpectrum459.graph fusedMap1048swap=true := by decide +kernel
theorem certified1048swap : Certified (graph core1048) (root 8) 1 0 :=
  of_native_maps core1048 DegreeOneSmallSpectrum762.graph DegreeOneSmallSpectrum459.graph
    sourceMap1048swap fusedMap1048swap sourceMap1048swap_checked fusedMap1048swap_checked
    DegreeOneSmallComparisons.comparison1048
#print axioms sourceMap1048swap_checked
#print axioms fusedMap1048swap_checked
#print axioms certified1048swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

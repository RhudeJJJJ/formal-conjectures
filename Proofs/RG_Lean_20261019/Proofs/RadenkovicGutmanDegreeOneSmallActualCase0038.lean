/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0038 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0038 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (sourceLabel 2 0 8 v)
def fusedMap0038 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 0 8 v)
theorem sourceMap0038_checked : acceptsGraphIso
    (source (graph core0038) (root 2) 0 8) DegreeOneSmallSpectrum857.graph sourceMap0038=true := by decide +kernel
theorem fusedMap0038_checked : acceptsGraphIso
    (fused (graph core0038) (root 2) 0 8) DegreeOneSmallSpectrum861.graph fusedMap0038=true := by decide +kernel
theorem certified0038 : Certified (graph core0038) (root 2) 0 8 :=
  of_native_maps core0038 DegreeOneSmallSpectrum857.graph DegreeOneSmallSpectrum861.graph
    sourceMap0038 fusedMap0038 sourceMap0038_checked fusedMap0038_checked
    DegreeOneSmallComparisons.comparison0038
#print axioms sourceMap0038_checked
#print axioms fusedMap0038_checked
#print axioms certified0038
def sourceMap0038swap : (Vertices 2 ⊕ Fin 9 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,4,5,2,1,0,7,8,9,10,11,12,6] (sourceLabel 2 8 0 v)
def fusedMap0038swap : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 8 0 v)
theorem sourceMap0038swap_checked : acceptsGraphIso
    (source (graph core0038) (root 2) 8 0) DegreeOneSmallSpectrum857.graph sourceMap0038swap=true := by decide +kernel
theorem fusedMap0038swap_checked : acceptsGraphIso
    (fused (graph core0038) (root 2) 8 0) DegreeOneSmallSpectrum861.graph fusedMap0038swap=true := by decide +kernel
theorem certified0038swap : Certified (graph core0038) (root 2) 8 0 :=
  of_native_maps core0038 DegreeOneSmallSpectrum857.graph DegreeOneSmallSpectrum861.graph
    sourceMap0038swap fusedMap0038swap sourceMap0038swap_checked fusedMap0038swap_checked
    DegreeOneSmallComparisons.comparison0038
#print axioms sourceMap0038swap_checked
#print axioms fusedMap0038swap_checked
#print axioms certified0038swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

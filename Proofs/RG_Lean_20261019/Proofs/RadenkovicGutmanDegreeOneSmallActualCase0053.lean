/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0053 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0053 : (Vertices 2 ⊕ Fin 4 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,6,7,2,3,4,5,0,8,9,10,11,12] (sourceLabel 2 3 5 v)
def fusedMap0053 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 3 5 v)
theorem sourceMap0053_checked : acceptsGraphIso
    (source (graph core0053) (root 2) 3 5) DegreeOneSmallSpectrum971.graph sourceMap0053=true := by decide +kernel
theorem fusedMap0053_checked : acceptsGraphIso
    (fused (graph core0053) (root 2) 3 5) DegreeOneSmallSpectrum861.graph fusedMap0053=true := by decide +kernel
theorem certified0053 : Certified (graph core0053) (root 2) 3 5 :=
  of_native_maps core0053 DegreeOneSmallSpectrum971.graph DegreeOneSmallSpectrum861.graph
    sourceMap0053 fusedMap0053 sourceMap0053_checked fusedMap0053_checked
    DegreeOneSmallComparisons.comparison0053
#print axioms sourceMap0053_checked
#print axioms fusedMap0053_checked
#print axioms certified0053
def sourceMap0053swap : (Vertices 2 ⊕ Fin 6 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,6,7,0,8,9,10,11,12,2,3,4,5] (sourceLabel 2 5 3 v)
def fusedMap0053swap : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 5 3 v)
theorem sourceMap0053swap_checked : acceptsGraphIso
    (source (graph core0053) (root 2) 5 3) DegreeOneSmallSpectrum971.graph sourceMap0053swap=true := by decide +kernel
theorem fusedMap0053swap_checked : acceptsGraphIso
    (fused (graph core0053) (root 2) 5 3) DegreeOneSmallSpectrum861.graph fusedMap0053swap=true := by decide +kernel
theorem certified0053swap : Certified (graph core0053) (root 2) 5 3 :=
  of_native_maps core0053 DegreeOneSmallSpectrum971.graph DegreeOneSmallSpectrum861.graph
    sourceMap0053swap fusedMap0053swap sourceMap0053swap_checked fusedMap0053swap_checked
    DegreeOneSmallComparisons.comparison0053
#print axioms sourceMap0053swap_checked
#print axioms fusedMap0053swap_checked
#print axioms certified0053swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

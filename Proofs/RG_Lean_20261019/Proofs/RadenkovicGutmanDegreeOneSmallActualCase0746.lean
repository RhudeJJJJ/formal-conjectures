/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0746 : Family 8 := level8.get ⟨2,by decide⟩
def sourceMap0746 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0746 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0746_checked : acceptsGraphIso
    (source (graph core0746) (root 8) 1 1) DegreeOneSmallSpectrum912.graph sourceMap0746=true := by decide +kernel
theorem fusedMap0746_checked : acceptsGraphIso
    (fused (graph core0746) (root 8) 1 1) DegreeOneSmallSpectrum857.graph fusedMap0746=true := by decide +kernel
theorem certified0746 : Certified (graph core0746) (root 8) 1 1 :=
  of_native_maps core0746 DegreeOneSmallSpectrum912.graph DegreeOneSmallSpectrum857.graph
    sourceMap0746 fusedMap0746 sourceMap0746_checked fusedMap0746_checked
    DegreeOneSmallComparisons.comparison0746
#print axioms sourceMap0746_checked
#print axioms fusedMap0746_checked
#print axioms certified0746
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

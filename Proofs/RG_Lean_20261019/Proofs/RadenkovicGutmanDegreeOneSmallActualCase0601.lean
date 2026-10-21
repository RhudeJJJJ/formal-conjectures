/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0601 : Family 7 := level7.get ⟨34,by decide⟩
def sourceMap0601 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,10,11,6,7,8,9] (sourceLabel 7 1 1 v)
def fusedMap0601 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0601_checked : acceptsGraphIso
    (source (graph core0601) (root 7) 1 1) DegreeOneSmallSpectrum754.graph sourceMap0601=true := by decide +kernel
theorem fusedMap0601_checked : acceptsGraphIso
    (fused (graph core0601) (root 7) 1 1) DegreeOneSmallSpectrum464.graph fusedMap0601=true := by decide +kernel
theorem certified0601 : Certified (graph core0601) (root 7) 1 1 :=
  of_native_maps core0601 DegreeOneSmallSpectrum754.graph DegreeOneSmallSpectrum464.graph
    sourceMap0601 fusedMap0601 sourceMap0601_checked fusedMap0601_checked
    DegreeOneSmallComparisons.comparison0601
#print axioms sourceMap0601_checked
#print axioms fusedMap0601_checked
#print axioms certified0601
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

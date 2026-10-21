/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0529 : Family 7 := level7.get ⟨15,by decide⟩
def sourceMap0529 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0529 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0529_checked : acceptsGraphIso
    (source (graph core0529) (root 7) 1 1) DegreeOneSmallSpectrum508.graph sourceMap0529=true := by decide +kernel
theorem fusedMap0529_checked : acceptsGraphIso
    (fused (graph core0529) (root 7) 1 1) DegreeOneSmallSpectrum382.graph fusedMap0529=true := by decide +kernel
theorem certified0529 : Certified (graph core0529) (root 7) 1 1 :=
  of_native_maps core0529 DegreeOneSmallSpectrum508.graph DegreeOneSmallSpectrum382.graph
    sourceMap0529 fusedMap0529 sourceMap0529_checked fusedMap0529_checked
    DegreeOneSmallComparisons.comparison0529
#print axioms sourceMap0529_checked
#print axioms fusedMap0529_checked
#print axioms certified0529
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

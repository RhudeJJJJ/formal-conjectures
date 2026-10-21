/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0107 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0107 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 4 2 2 v)
def fusedMap0107 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 2 2 v)
theorem sourceMap0107_checked : acceptsGraphIso
    (source (graph core0107) (root 4) 2 2) DegreeOneSmallSpectrum218.graph sourceMap0107=true := by decide +kernel
theorem fusedMap0107_checked : acceptsGraphIso
    (fused (graph core0107) (root 4) 2 2) DegreeOneSmallSpectrum168.graph fusedMap0107=true := by decide +kernel
theorem certified0107 : Certified (graph core0107) (root 4) 2 2 :=
  of_native_maps core0107 DegreeOneSmallSpectrum218.graph DegreeOneSmallSpectrum168.graph
    sourceMap0107 fusedMap0107 sourceMap0107_checked fusedMap0107_checked
    DegreeOneSmallComparisons.comparison0107
#print axioms sourceMap0107_checked
#print axioms fusedMap0107_checked
#print axioms certified0107
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

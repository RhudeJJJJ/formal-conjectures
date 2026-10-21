/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0272 : Family 6 := level6.get ⟨0,by decide⟩
def sourceMap0272 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,3,4,5,6] (sourceLabel 6 1 1 v)
def fusedMap0272 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 6 1 1 v)
theorem sourceMap0272_checked : acceptsGraphIso
    (source (graph core0272) (root 6) 1 1) DegreeOneSmallSpectrum202.graph sourceMap0272=true := by decide +kernel
theorem fusedMap0272_checked : acceptsGraphIso
    (fused (graph core0272) (root 6) 1 1) DegreeOneSmallSpectrum168.graph fusedMap0272=true := by decide +kernel
theorem certified0272 : Certified (graph core0272) (root 6) 1 1 :=
  of_native_maps core0272 DegreeOneSmallSpectrum202.graph DegreeOneSmallSpectrum168.graph
    sourceMap0272 fusedMap0272 sourceMap0272_checked fusedMap0272_checked
    DegreeOneSmallComparisons.comparison0272
#print axioms sourceMap0272_checked
#print axioms fusedMap0272_checked
#print axioms certified0272
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

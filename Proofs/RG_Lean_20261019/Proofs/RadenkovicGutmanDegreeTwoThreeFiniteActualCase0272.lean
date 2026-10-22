/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0272 : Family 9 := level9.get ⟨368,by decide⟩
def sourceMap0272 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0272 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0272_checked : acceptsGraphIso
    (source (graph core0272) (root 9) 0 0) DegreeOneSmallSpectrum661.graph sourceMap0272=true := by decide +kernel
theorem fusedMap0272_checked : acceptsGraphIso
    (fused (graph core0272) (root 9) 0 0) DegreeOneSmallSpectrum717.graph fusedMap0272=true := by decide +kernel
theorem certified0272 : Certified (graph core0272) (root 9) 0 0 :=
  of_native_maps core0272 DegreeOneSmallSpectrum661.graph DegreeOneSmallSpectrum717.graph
    sourceMap0272 fusedMap0272 sourceMap0272_checked fusedMap0272_checked
    DegreeTwoThreeFiniteComparisons.comparison0272
#print axioms sourceMap0272_checked
#print axioms fusedMap0272_checked
#print axioms certified0272
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

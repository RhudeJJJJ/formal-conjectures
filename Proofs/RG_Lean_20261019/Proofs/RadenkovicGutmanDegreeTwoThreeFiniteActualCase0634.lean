/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0634 : Family 10 := level10.get ⟨793,by decide⟩
def sourceMap0634 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0634 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0634_checked : acceptsGraphIso
    (source (graph core0634) (root 10) 0 0) DegreeOneSmallSpectrum1652.graph sourceMap0634=true := by decide +kernel
theorem fusedMap0634_checked : acceptsGraphIso
    (fused (graph core0634) (root 10) 0 0) DegreeOneSmallSpectrum1419.graph fusedMap0634=true := by decide +kernel
theorem certified0634 : Certified (graph core0634) (root 10) 0 0 :=
  of_native_maps core0634 DegreeOneSmallSpectrum1652.graph DegreeOneSmallSpectrum1419.graph
    sourceMap0634 fusedMap0634 sourceMap0634_checked fusedMap0634_checked
    DegreeTwoThreeFiniteComparisons.comparison0634
#print axioms sourceMap0634_checked
#print axioms fusedMap0634_checked
#print axioms certified0634
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

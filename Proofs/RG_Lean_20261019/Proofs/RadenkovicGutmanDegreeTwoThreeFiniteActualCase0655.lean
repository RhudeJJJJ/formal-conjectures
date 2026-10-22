/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0655 : Family 10 := level10.get ⟨849,by decide⟩
def sourceMap0655 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0655 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0655_checked : acceptsGraphIso
    (source (graph core0655) (root 10) 0 0) DegreeOneSmallSpectrum1667.graph sourceMap0655=true := by decide +kernel
theorem fusedMap0655_checked : acceptsGraphIso
    (fused (graph core0655) (root 10) 0 0) DegreeOneSmallSpectrum1428.graph fusedMap0655=true := by decide +kernel
theorem certified0655 : Certified (graph core0655) (root 10) 0 0 :=
  of_native_maps core0655 DegreeOneSmallSpectrum1667.graph DegreeOneSmallSpectrum1428.graph
    sourceMap0655 fusedMap0655 sourceMap0655_checked fusedMap0655_checked
    DegreeTwoThreeFiniteComparisons.comparison0655
#print axioms sourceMap0655_checked
#print axioms fusedMap0655_checked
#print axioms certified0655
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

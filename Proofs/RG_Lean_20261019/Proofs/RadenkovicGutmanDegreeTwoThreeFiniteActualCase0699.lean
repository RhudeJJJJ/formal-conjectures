/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0699 : Family 10 := level10.get ⟨959,by decide⟩
def sourceMap0699 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,10,11,12,6,7,8,9,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0699 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0699_checked : acceptsGraphIso
    (source (graph core0699) (root 10) 0 0) DegreeOneSmallSpectrum1641.graph sourceMap0699=true := by decide +kernel
theorem fusedMap0699_checked : acceptsGraphIso
    (fused (graph core0699) (root 10) 0 0) DegreeOneSmallSpectrum1415.graph fusedMap0699=true := by decide +kernel
theorem certified0699 : Certified (graph core0699) (root 10) 0 0 :=
  of_native_maps core0699 DegreeOneSmallSpectrum1641.graph DegreeOneSmallSpectrum1415.graph
    sourceMap0699 fusedMap0699 sourceMap0699_checked fusedMap0699_checked
    DegreeTwoThreeFiniteComparisons.comparison0699
#print axioms sourceMap0699_checked
#print axioms fusedMap0699_checked
#print axioms certified0699
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

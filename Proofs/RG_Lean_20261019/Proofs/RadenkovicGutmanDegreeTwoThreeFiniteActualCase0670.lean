/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0670 : Family 10 := level10.get ⟨888,by decide⟩
def sourceMap0670 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0670 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0670_checked : acceptsGraphIso
    (source (graph core0670) (root 10) 0 0) DegreeOneSmallSpectrum1654.graph sourceMap0670=true := by decide +kernel
theorem fusedMap0670_checked : acceptsGraphIso
    (fused (graph core0670) (root 10) 0 0) DegreeOneSmallSpectrum1422.graph fusedMap0670=true := by decide +kernel
theorem certified0670 : Certified (graph core0670) (root 10) 0 0 :=
  of_native_maps core0670 DegreeOneSmallSpectrum1654.graph DegreeOneSmallSpectrum1422.graph
    sourceMap0670 fusedMap0670 sourceMap0670_checked fusedMap0670_checked
    DegreeTwoThreeFiniteComparisons.comparison0670
#print axioms sourceMap0670_checked
#print axioms fusedMap0670_checked
#print axioms certified0670
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

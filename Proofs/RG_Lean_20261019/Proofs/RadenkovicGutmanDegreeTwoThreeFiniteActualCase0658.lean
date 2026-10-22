/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0658 : Family 10 := level10.get ⟨857,by decide⟩
def sourceMap0658 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0658 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0658_checked : acceptsGraphIso
    (source (graph core0658) (root 10) 0 0) DegreeOneSmallSpectrum1695.graph sourceMap0658=true := by decide +kernel
theorem fusedMap0658_checked : acceptsGraphIso
    (fused (graph core0658) (root 10) 0 0) DegreeOneSmallSpectrum1444.graph fusedMap0658=true := by decide +kernel
theorem certified0658 : Certified (graph core0658) (root 10) 0 0 :=
  of_native_maps core0658 DegreeOneSmallSpectrum1695.graph DegreeOneSmallSpectrum1444.graph
    sourceMap0658 fusedMap0658 sourceMap0658_checked fusedMap0658_checked
    DegreeTwoThreeFiniteComparisons.comparison0658
#print axioms sourceMap0658_checked
#print axioms fusedMap0658_checked
#print axioms certified0658
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

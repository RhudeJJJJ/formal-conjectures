/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0895 : Family 10 := level10.get ⟨1438,by decide⟩
def sourceMap0895 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,5,6,7,8,9,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0895 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0895_checked : acceptsGraphIso
    (source (graph core0895) (root 10) 0 0) DegreeOneSmallSpectrum1617.graph sourceMap0895=true := by decide +kernel
theorem fusedMap0895_checked : acceptsGraphIso
    (fused (graph core0895) (root 10) 0 0) DegreeOneSmallSpectrum1969.graph fusedMap0895=true := by decide +kernel
theorem certified0895 : Certified (graph core0895) (root 10) 0 0 :=
  of_native_maps core0895 DegreeOneSmallSpectrum1617.graph DegreeOneSmallSpectrum1969.graph
    sourceMap0895 fusedMap0895 sourceMap0895_checked fusedMap0895_checked
    DegreeTwoThreeFiniteComparisons.comparison0895
#print axioms sourceMap0895_checked
#print axioms fusedMap0895_checked
#print axioms certified0895
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

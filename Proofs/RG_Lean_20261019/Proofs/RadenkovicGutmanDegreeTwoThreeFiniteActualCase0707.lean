/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0707 : Family 10 := level10.get ⟨975,by decide⟩
def sourceMap0707 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0707 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0707_checked : acceptsGraphIso
    (source (graph core0707) (root 10) 0 0) DegreeOneSmallSpectrum978.graph sourceMap0707=true := by decide +kernel
theorem fusedMap0707_checked : acceptsGraphIso
    (fused (graph core0707) (root 10) 0 0) DegreeOneSmallSpectrum977.graph fusedMap0707=true := by decide +kernel
theorem certified0707 : Certified (graph core0707) (root 10) 0 0 :=
  of_native_maps core0707 DegreeOneSmallSpectrum978.graph DegreeOneSmallSpectrum977.graph
    sourceMap0707 fusedMap0707 sourceMap0707_checked fusedMap0707_checked
    DegreeTwoThreeFiniteComparisons.comparison0707
#print axioms sourceMap0707_checked
#print axioms fusedMap0707_checked
#print axioms certified0707
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

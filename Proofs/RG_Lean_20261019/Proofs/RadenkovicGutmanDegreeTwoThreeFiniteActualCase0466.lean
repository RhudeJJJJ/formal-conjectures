/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0466 : Family 10 := level10.get ⟨280,by decide⟩
def sourceMap0466 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0466 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0466_checked : acceptsGraphIso
    (source (graph core0466) (root 10) 0 0) DegreeOneSmallSpectrum902.graph sourceMap0466=true := by decide +kernel
theorem fusedMap0466_checked : acceptsGraphIso
    (fused (graph core0466) (root 10) 0 0) DegreeOneSmallSpectrum901.graph fusedMap0466=true := by decide +kernel
theorem certified0466 : Certified (graph core0466) (root 10) 0 0 :=
  of_native_maps core0466 DegreeOneSmallSpectrum902.graph DegreeOneSmallSpectrum901.graph
    sourceMap0466 fusedMap0466 sourceMap0466_checked fusedMap0466_checked
    DegreeTwoThreeFiniteComparisons.comparison0466
#print axioms sourceMap0466_checked
#print axioms fusedMap0466_checked
#print axioms certified0466
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

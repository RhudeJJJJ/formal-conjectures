/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0514 : Family 10 := level10.get ⟨444,by decide⟩
def sourceMap0514 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0514 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0514_checked : acceptsGraphIso
    (source (graph core0514) (root 10) 0 0) DegreeOneSmallSpectrum1022.graph sourceMap0514=true := by decide +kernel
theorem fusedMap0514_checked : acceptsGraphIso
    (fused (graph core0514) (root 10) 0 0) DegreeOneSmallSpectrum1434.graph fusedMap0514=true := by decide +kernel
theorem certified0514 : Certified (graph core0514) (root 10) 0 0 :=
  of_native_maps core0514 DegreeOneSmallSpectrum1022.graph DegreeOneSmallSpectrum1434.graph
    sourceMap0514 fusedMap0514 sourceMap0514_checked fusedMap0514_checked
    DegreeTwoThreeFiniteComparisons.comparison0514
#print axioms sourceMap0514_checked
#print axioms fusedMap0514_checked
#print axioms certified0514
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

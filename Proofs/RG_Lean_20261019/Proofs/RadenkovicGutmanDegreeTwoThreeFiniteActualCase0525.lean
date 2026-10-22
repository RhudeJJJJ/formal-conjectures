/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0525 : Family 10 := level10.get ⟨474,by decide⟩
def sourceMap0525 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0525 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0525_checked : acceptsGraphIso
    (source (graph core0525) (root 10) 0 0) DegreeOneSmallSpectrum1009.graph sourceMap0525=true := by decide +kernel
theorem fusedMap0525_checked : acceptsGraphIso
    (fused (graph core0525) (root 10) 0 0) DegreeOneSmallSpectrum1403.graph fusedMap0525=true := by decide +kernel
theorem certified0525 : Certified (graph core0525) (root 10) 0 0 :=
  of_native_maps core0525 DegreeOneSmallSpectrum1009.graph DegreeOneSmallSpectrum1403.graph
    sourceMap0525 fusedMap0525 sourceMap0525_checked fusedMap0525_checked
    DegreeTwoThreeFiniteComparisons.comparison0525
#print axioms sourceMap0525_checked
#print axioms fusedMap0525_checked
#print axioms certified0525
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

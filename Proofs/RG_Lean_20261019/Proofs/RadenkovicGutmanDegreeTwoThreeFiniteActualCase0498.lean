/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0498 : Family 10 := level10.get ⟨393,by decide⟩
def sourceMap0498 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0498 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0498_checked : acceptsGraphIso
    (source (graph core0498) (root 10) 0 0) DegreeOneSmallSpectrum1078.graph sourceMap0498=true := by decide +kernel
theorem fusedMap0498_checked : acceptsGraphIso
    (fused (graph core0498) (root 10) 0 0) DegreeOneSmallSpectrum1448.graph fusedMap0498=true := by decide +kernel
theorem certified0498 : Certified (graph core0498) (root 10) 0 0 :=
  of_native_maps core0498 DegreeOneSmallSpectrum1078.graph DegreeOneSmallSpectrum1448.graph
    sourceMap0498 fusedMap0498 sourceMap0498_checked fusedMap0498_checked
    DegreeTwoThreeFiniteComparisons.comparison0498
#print axioms sourceMap0498_checked
#print axioms fusedMap0498_checked
#print axioms certified0498
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

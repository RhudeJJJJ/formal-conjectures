/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0650 : Family 10 := level10.get ⟨833,by decide⟩
def sourceMap0650 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0650 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0650_checked : acceptsGraphIso
    (source (graph core0650) (root 10) 0 0) DegreeOneSmallSpectrum1691.graph sourceMap0650=true := by decide +kernel
theorem fusedMap0650_checked : acceptsGraphIso
    (fused (graph core0650) (root 10) 0 0) DegreeOneSmallSpectrum1438.graph fusedMap0650=true := by decide +kernel
theorem certified0650 : Certified (graph core0650) (root 10) 0 0 :=
  of_native_maps core0650 DegreeOneSmallSpectrum1691.graph DegreeOneSmallSpectrum1438.graph
    sourceMap0650 fusedMap0650 sourceMap0650_checked fusedMap0650_checked
    DegreeTwoThreeFiniteComparisons.comparison0650
#print axioms sourceMap0650_checked
#print axioms fusedMap0650_checked
#print axioms certified0650
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0610 : Family 10 := level10.get ⟨721,by decide⟩
def sourceMap0610 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0610 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0610_checked : acceptsGraphIso
    (source (graph core0610) (root 10) 0 0) DegreeOneSmallSpectrum1345.graph sourceMap0610=true := by decide +kernel
theorem fusedMap0610_checked : acceptsGraphIso
    (fused (graph core0610) (root 10) 0 0) DegreeOneSmallSpectrum1343.graph fusedMap0610=true := by decide +kernel
theorem certified0610 : Certified (graph core0610) (root 10) 0 0 :=
  of_native_maps core0610 DegreeOneSmallSpectrum1345.graph DegreeOneSmallSpectrum1343.graph
    sourceMap0610 fusedMap0610 sourceMap0610_checked fusedMap0610_checked
    DegreeTwoThreeFiniteComparisons.comparison0610
#print axioms sourceMap0610_checked
#print axioms fusedMap0610_checked
#print axioms certified0610
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

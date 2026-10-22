/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0605 : Family 10 := level10.get ⟨710,by decide⟩
def sourceMap0605 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0605 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0605_checked : acceptsGraphIso
    (source (graph core0605) (root 10) 0 0) DegreeOneSmallSpectrum1663.graph sourceMap0605=true := by decide +kernel
theorem fusedMap0605_checked : acceptsGraphIso
    (fused (graph core0605) (root 10) 0 0) DegreeOneSmallSpectrum1326.graph fusedMap0605=true := by decide +kernel
theorem certified0605 : Certified (graph core0605) (root 10) 0 0 :=
  of_native_maps core0605 DegreeOneSmallSpectrum1663.graph DegreeOneSmallSpectrum1326.graph
    sourceMap0605 fusedMap0605 sourceMap0605_checked fusedMap0605_checked
    DegreeTwoThreeFiniteComparisons.comparison0605
#print axioms sourceMap0605_checked
#print axioms fusedMap0605_checked
#print axioms certified0605
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0649 : Family 10 := level10.get ⟨825,by decide⟩
def sourceMap0649 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0649 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0649_checked : acceptsGraphIso
    (source (graph core0649) (root 10) 0 0) DegreeOneSmallSpectrum1019.graph sourceMap0649=true := by decide +kernel
theorem fusedMap0649_checked : acceptsGraphIso
    (fused (graph core0649) (root 10) 0 0) DegreeOneSmallSpectrum1013.graph fusedMap0649=true := by decide +kernel
theorem certified0649 : Certified (graph core0649) (root 10) 0 0 :=
  of_native_maps core0649 DegreeOneSmallSpectrum1019.graph DegreeOneSmallSpectrum1013.graph
    sourceMap0649 fusedMap0649 sourceMap0649_checked fusedMap0649_checked
    DegreeTwoThreeFiniteComparisons.comparison0649
#print axioms sourceMap0649_checked
#print axioms fusedMap0649_checked
#print axioms certified0649
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

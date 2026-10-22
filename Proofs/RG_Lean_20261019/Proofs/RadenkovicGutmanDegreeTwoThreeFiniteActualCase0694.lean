/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0694 : Family 10 := level10.get ⟨949,by decide⟩
def sourceMap0694 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,10,11,12,6,7,8,9,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0694 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0694_checked : acceptsGraphIso
    (source (graph core0694) (root 10) 0 0) DegreeOneSmallSpectrum1620.graph sourceMap0694=true := by decide +kernel
theorem fusedMap0694_checked : acceptsGraphIso
    (fused (graph core0694) (root 10) 0 0) DegreeOneSmallSpectrum1404.graph fusedMap0694=true := by decide +kernel
theorem certified0694 : Certified (graph core0694) (root 10) 0 0 :=
  of_native_maps core0694 DegreeOneSmallSpectrum1620.graph DegreeOneSmallSpectrum1404.graph
    sourceMap0694 fusedMap0694 sourceMap0694_checked fusedMap0694_checked
    DegreeTwoThreeFiniteComparisons.comparison0694
#print axioms sourceMap0694_checked
#print axioms fusedMap0694_checked
#print axioms certified0694
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

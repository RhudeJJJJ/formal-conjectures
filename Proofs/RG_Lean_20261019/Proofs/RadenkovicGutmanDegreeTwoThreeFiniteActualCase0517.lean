/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0517 : Family 10 := level10.get ⟨452,by decide⟩
def sourceMap0517 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0517 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0517_checked : acceptsGraphIso
    (source (graph core0517) (root 10) 0 0) DegreeOneSmallSpectrum1023.graph sourceMap0517=true := by decide +kernel
theorem fusedMap0517_checked : acceptsGraphIso
    (fused (graph core0517) (root 10) 0 0) DegreeOneSmallSpectrum1435.graph fusedMap0517=true := by decide +kernel
theorem certified0517 : Certified (graph core0517) (root 10) 0 0 :=
  of_native_maps core0517 DegreeOneSmallSpectrum1023.graph DegreeOneSmallSpectrum1435.graph
    sourceMap0517 fusedMap0517 sourceMap0517_checked fusedMap0517_checked
    DegreeTwoThreeFiniteComparisons.comparison0517
#print axioms sourceMap0517_checked
#print axioms fusedMap0517_checked
#print axioms certified0517
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0566 : Family 10 := level10.get ⟨600,by decide⟩
def sourceMap0566 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0566 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0566_checked : acceptsGraphIso
    (source (graph core0566) (root 10) 0 0) DegreeOneSmallSpectrum1660.graph sourceMap0566=true := by decide +kernel
theorem fusedMap0566_checked : acceptsGraphIso
    (fused (graph core0566) (root 10) 0 0) DegreeOneSmallSpectrum1153.graph fusedMap0566=true := by decide +kernel
theorem certified0566 : Certified (graph core0566) (root 10) 0 0 :=
  of_native_maps core0566 DegreeOneSmallSpectrum1660.graph DegreeOneSmallSpectrum1153.graph
    sourceMap0566 fusedMap0566 sourceMap0566_checked fusedMap0566_checked
    DegreeTwoThreeFiniteComparisons.comparison0566
#print axioms sourceMap0566_checked
#print axioms fusedMap0566_checked
#print axioms certified0566
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

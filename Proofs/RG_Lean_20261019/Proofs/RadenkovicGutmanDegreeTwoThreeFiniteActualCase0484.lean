/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0484 : Family 10 := level10.get ⟨349,by decide⟩
def sourceMap0484 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0484 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0484_checked : acceptsGraphIso
    (source (graph core0484) (root 10) 0 0) DegreeOneSmallSpectrum1047.graph sourceMap0484=true := by decide +kernel
theorem fusedMap0484_checked : acceptsGraphIso
    (fused (graph core0484) (root 10) 0 0) DegreeOneSmallSpectrum1437.graph fusedMap0484=true := by decide +kernel
theorem certified0484 : Certified (graph core0484) (root 10) 0 0 :=
  of_native_maps core0484 DegreeOneSmallSpectrum1047.graph DegreeOneSmallSpectrum1437.graph
    sourceMap0484 fusedMap0484 sourceMap0484_checked fusedMap0484_checked
    DegreeTwoThreeFiniteComparisons.comparison0484
#print axioms sourceMap0484_checked
#print axioms fusedMap0484_checked
#print axioms certified0484
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

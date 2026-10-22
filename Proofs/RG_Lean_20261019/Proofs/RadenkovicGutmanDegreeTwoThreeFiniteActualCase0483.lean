/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0483 : Family 10 := level10.get ⟨346,by decide⟩
def sourceMap0483 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0483 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0483_checked : acceptsGraphIso
    (source (graph core0483) (root 10) 0 0) DegreeOneSmallSpectrum1042.graph sourceMap0483=true := by decide +kernel
theorem fusedMap0483_checked : acceptsGraphIso
    (fused (graph core0483) (root 10) 0 0) DegreeOneSmallSpectrum1436.graph fusedMap0483=true := by decide +kernel
theorem certified0483 : Certified (graph core0483) (root 10) 0 0 :=
  of_native_maps core0483 DegreeOneSmallSpectrum1042.graph DegreeOneSmallSpectrum1436.graph
    sourceMap0483 fusedMap0483 sourceMap0483_checked fusedMap0483_checked
    DegreeTwoThreeFiniteComparisons.comparison0483
#print axioms sourceMap0483_checked
#print axioms fusedMap0483_checked
#print axioms certified0483
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

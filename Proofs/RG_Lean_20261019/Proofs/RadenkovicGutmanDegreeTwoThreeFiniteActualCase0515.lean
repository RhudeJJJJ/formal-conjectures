/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0515 : Family 10 := level10.get ⟨445,by decide⟩
def sourceMap0515 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0515 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0515_checked : acceptsGraphIso
    (source (graph core0515) (root 10) 0 0) DegreeOneSmallSpectrum1392.graph sourceMap0515=true := by decide +kernel
theorem fusedMap0515_checked : acceptsGraphIso
    (fused (graph core0515) (root 10) 0 0) DegreeOneSmallSpectrum1347.graph fusedMap0515=true := by decide +kernel
theorem certified0515 : Certified (graph core0515) (root 10) 0 0 :=
  of_native_maps core0515 DegreeOneSmallSpectrum1392.graph DegreeOneSmallSpectrum1347.graph
    sourceMap0515 fusedMap0515 sourceMap0515_checked fusedMap0515_checked
    DegreeTwoThreeFiniteComparisons.comparison0515
#print axioms sourceMap0515_checked
#print axioms fusedMap0515_checked
#print axioms certified0515
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

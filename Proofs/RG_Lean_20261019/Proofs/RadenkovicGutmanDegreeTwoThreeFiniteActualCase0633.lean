/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0633 : Family 10 := level10.get ⟨791,by decide⟩
def sourceMap0633 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0633 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0633_checked : acceptsGraphIso
    (source (graph core0633) (root 10) 0 0) DegreeOneSmallSpectrum1635.graph sourceMap0633=true := by decide +kernel
theorem fusedMap0633_checked : acceptsGraphIso
    (fused (graph core0633) (root 10) 0 0) DegreeOneSmallSpectrum1409.graph fusedMap0633=true := by decide +kernel
theorem certified0633 : Certified (graph core0633) (root 10) 0 0 :=
  of_native_maps core0633 DegreeOneSmallSpectrum1635.graph DegreeOneSmallSpectrum1409.graph
    sourceMap0633 fusedMap0633 sourceMap0633_checked fusedMap0633_checked
    DegreeTwoThreeFiniteComparisons.comparison0633
#print axioms sourceMap0633_checked
#print axioms fusedMap0633_checked
#print axioms certified0633
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

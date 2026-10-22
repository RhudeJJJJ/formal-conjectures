/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0659 : Family 10 := level10.get ⟨860,by decide⟩
def sourceMap0659 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0659 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0659_checked : acceptsGraphIso
    (source (graph core0659) (root 10) 0 0) DegreeOneSmallSpectrum1668.graph sourceMap0659=true := by decide +kernel
theorem fusedMap0659_checked : acceptsGraphIso
    (fused (graph core0659) (root 10) 0 0) DegreeOneSmallSpectrum1429.graph fusedMap0659=true := by decide +kernel
theorem certified0659 : Certified (graph core0659) (root 10) 0 0 :=
  of_native_maps core0659 DegreeOneSmallSpectrum1668.graph DegreeOneSmallSpectrum1429.graph
    sourceMap0659 fusedMap0659 sourceMap0659_checked fusedMap0659_checked
    DegreeTwoThreeFiniteComparisons.comparison0659
#print axioms sourceMap0659_checked
#print axioms fusedMap0659_checked
#print axioms certified0659
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0674 : Family 10 := level10.get ⟨899,by decide⟩
def sourceMap0674 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,0,8,9,10,11,12,1,2,3,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0674 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0674_checked : acceptsGraphIso
    (source (graph core0674) (root 10) 0 0) DegreeOneSmallSpectrum1466.graph sourceMap0674=true := by decide +kernel
theorem fusedMap0674_checked : acceptsGraphIso
    (fused (graph core0674) (root 10) 0 0) DegreeOneSmallSpectrum1397.graph fusedMap0674=true := by decide +kernel
theorem certified0674 : Certified (graph core0674) (root 10) 0 0 :=
  of_native_maps core0674 DegreeOneSmallSpectrum1466.graph DegreeOneSmallSpectrum1397.graph
    sourceMap0674 fusedMap0674 sourceMap0674_checked fusedMap0674_checked
    DegreeTwoThreeFiniteComparisons.comparison0674
#print axioms sourceMap0674_checked
#print axioms fusedMap0674_checked
#print axioms certified0674
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0661 : Family 10 := level10.get ⟨866,by decide⟩
def sourceMap0661 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0661 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0661_checked : acceptsGraphIso
    (source (graph core0661) (root 10) 0 0) DegreeOneSmallSpectrum1636.graph sourceMap0661=true := by decide +kernel
theorem fusedMap0661_checked : acceptsGraphIso
    (fused (graph core0661) (root 10) 0 0) DegreeOneSmallSpectrum1411.graph fusedMap0661=true := by decide +kernel
theorem certified0661 : Certified (graph core0661) (root 10) 0 0 :=
  of_native_maps core0661 DegreeOneSmallSpectrum1636.graph DegreeOneSmallSpectrum1411.graph
    sourceMap0661 fusedMap0661 sourceMap0661_checked fusedMap0661_checked
    DegreeTwoThreeFiniteComparisons.comparison0661
#print axioms sourceMap0661_checked
#print axioms fusedMap0661_checked
#print axioms certified0661
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

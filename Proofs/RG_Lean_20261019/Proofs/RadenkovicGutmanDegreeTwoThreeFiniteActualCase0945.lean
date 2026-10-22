/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0945 : Family 10 := level10.get ⟨1570,by decide⟩
def sourceMap0945 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0945 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0945_checked : acceptsGraphIso
    (source (graph core0945) (root 10) 0 0) DegreeOneSmallSpectrum2003.graph sourceMap0945=true := by decide +kernel
theorem fusedMap0945_checked : acceptsGraphIso
    (fused (graph core0945) (root 10) 0 0) DegreeOneSmallSpectrum1608.graph fusedMap0945=true := by decide +kernel
theorem certified0945 : Certified (graph core0945) (root 10) 0 0 :=
  of_native_maps core0945 DegreeOneSmallSpectrum2003.graph DegreeOneSmallSpectrum1608.graph
    sourceMap0945 fusedMap0945 sourceMap0945_checked fusedMap0945_checked
    DegreeTwoThreeFiniteComparisons.comparison0945
#print axioms sourceMap0945_checked
#print axioms fusedMap0945_checked
#print axioms certified0945
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0675 : Family 10 := level10.get ⟨902,by decide⟩
def sourceMap0675 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0675 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0675_checked : acceptsGraphIso
    (source (graph core0675) (root 10) 0 0) DegreeOneSmallSpectrum1616.graph sourceMap0675=true := by decide +kernel
theorem fusedMap0675_checked : acceptsGraphIso
    (fused (graph core0675) (root 10) 0 0) DegreeOneSmallSpectrum1402.graph fusedMap0675=true := by decide +kernel
theorem certified0675 : Certified (graph core0675) (root 10) 0 0 :=
  of_native_maps core0675 DegreeOneSmallSpectrum1616.graph DegreeOneSmallSpectrum1402.graph
    sourceMap0675 fusedMap0675 sourceMap0675_checked fusedMap0675_checked
    DegreeTwoThreeFiniteComparisons.comparison0675
#print axioms sourceMap0675_checked
#print axioms fusedMap0675_checked
#print axioms certified0675
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

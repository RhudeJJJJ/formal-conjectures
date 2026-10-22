/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0679 : Family 10 := level10.get ⟨910,by decide⟩
def sourceMap0679 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0679 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0679_checked : acceptsGraphIso
    (source (graph core0679) (root 10) 0 0) DegreeOneSmallSpectrum1373.graph sourceMap0679=true := by decide +kernel
theorem fusedMap0679_checked : acceptsGraphIso
    (fused (graph core0679) (root 10) 0 0) DegreeOneSmallSpectrum1322.graph fusedMap0679=true := by decide +kernel
theorem certified0679 : Certified (graph core0679) (root 10) 0 0 :=
  of_native_maps core0679 DegreeOneSmallSpectrum1373.graph DegreeOneSmallSpectrum1322.graph
    sourceMap0679 fusedMap0679 sourceMap0679_checked fusedMap0679_checked
    DegreeTwoThreeFiniteComparisons.comparison0679
#print axioms sourceMap0679_checked
#print axioms fusedMap0679_checked
#print axioms certified0679
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

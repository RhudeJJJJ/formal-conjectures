/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0583 : Family 10 := level10.get ⟨647,by decide⟩
def sourceMap0583 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0583 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0583_checked : acceptsGraphIso
    (source (graph core0583) (root 10) 0 0) DegreeOneSmallSpectrum1233.graph sourceMap0583=true := by decide +kernel
theorem fusedMap0583_checked : acceptsGraphIso
    (fused (graph core0583) (root 10) 0 0) DegreeOneSmallSpectrum1230.graph fusedMap0583=true := by decide +kernel
theorem certified0583 : Certified (graph core0583) (root 10) 0 0 :=
  of_native_maps core0583 DegreeOneSmallSpectrum1233.graph DegreeOneSmallSpectrum1230.graph
    sourceMap0583 fusedMap0583 sourceMap0583_checked fusedMap0583_checked
    DegreeTwoThreeFiniteComparisons.comparison0583
#print axioms sourceMap0583_checked
#print axioms fusedMap0583_checked
#print axioms certified0583
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

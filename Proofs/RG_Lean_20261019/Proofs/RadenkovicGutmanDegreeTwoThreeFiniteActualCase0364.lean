/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0364 : Family 9 := level9.get ⟨591,by decide⟩
def sourceMap0364 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0364 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0364_checked : acceptsGraphIso
    (source (graph core0364) (root 9) 0 0) DegreeOneSmallSpectrum844.graph sourceMap0364=true := by decide +kernel
theorem fusedMap0364_checked : acceptsGraphIso
    (fused (graph core0364) (root 9) 0 0) DegreeOneSmallSpectrum686.graph fusedMap0364=true := by decide +kernel
theorem certified0364 : Certified (graph core0364) (root 9) 0 0 :=
  of_native_maps core0364 DegreeOneSmallSpectrum844.graph DegreeOneSmallSpectrum686.graph
    sourceMap0364 fusedMap0364 sourceMap0364_checked fusedMap0364_checked
    DegreeTwoThreeFiniteComparisons.comparison0364
#print axioms sourceMap0364_checked
#print axioms fusedMap0364_checked
#print axioms certified0364
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

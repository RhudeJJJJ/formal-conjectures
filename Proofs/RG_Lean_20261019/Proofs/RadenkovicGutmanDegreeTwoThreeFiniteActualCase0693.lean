/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0693 : Family 10 := level10.get ⟨946,by decide⟩
def sourceMap0693 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0693 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0693_checked : acceptsGraphIso
    (source (graph core0693) (root 10) 0 0) DegreeOneSmallSpectrum1366.graph sourceMap0693=true := by decide +kernel
theorem fusedMap0693_checked : acceptsGraphIso
    (fused (graph core0693) (root 10) 0 0) DegreeOneSmallSpectrum1315.graph fusedMap0693=true := by decide +kernel
theorem certified0693 : Certified (graph core0693) (root 10) 0 0 :=
  of_native_maps core0693 DegreeOneSmallSpectrum1366.graph DegreeOneSmallSpectrum1315.graph
    sourceMap0693 fusedMap0693 sourceMap0693_checked fusedMap0693_checked
    DegreeTwoThreeFiniteComparisons.comparison0693
#print axioms sourceMap0693_checked
#print axioms fusedMap0693_checked
#print axioms certified0693
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

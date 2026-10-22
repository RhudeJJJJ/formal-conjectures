/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0532 : Family 10 := level10.get ⟨488,by decide⟩
def sourceMap0532 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0532 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0532_checked : acceptsGraphIso
    (source (graph core0532) (root 10) 0 0) DegreeOneSmallSpectrum974.graph sourceMap0532=true := by decide +kernel
theorem fusedMap0532_checked : acceptsGraphIso
    (fused (graph core0532) (root 10) 0 0) DegreeOneSmallSpectrum971.graph fusedMap0532=true := by decide +kernel
theorem certified0532 : Certified (graph core0532) (root 10) 0 0 :=
  of_native_maps core0532 DegreeOneSmallSpectrum974.graph DegreeOneSmallSpectrum971.graph
    sourceMap0532 fusedMap0532 sourceMap0532_checked fusedMap0532_checked
    DegreeTwoThreeFiniteComparisons.comparison0532
#print axioms sourceMap0532_checked
#print axioms fusedMap0532_checked
#print axioms certified0532
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

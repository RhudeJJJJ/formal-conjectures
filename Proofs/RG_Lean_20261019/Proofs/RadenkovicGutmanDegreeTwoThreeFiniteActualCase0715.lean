/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0715 : Family 10 := level10.get ⟨988,by decide⟩
def sourceMap0715 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0715 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0715_checked : acceptsGraphIso
    (source (graph core0715) (root 10) 0 0) DegreeOneSmallSpectrum987.graph sourceMap0715=true := by decide +kernel
theorem fusedMap0715_checked : acceptsGraphIso
    (fused (graph core0715) (root 10) 0 0) DegreeOneSmallSpectrum986.graph fusedMap0715=true := by decide +kernel
theorem certified0715 : Certified (graph core0715) (root 10) 0 0 :=
  of_native_maps core0715 DegreeOneSmallSpectrum987.graph DegreeOneSmallSpectrum986.graph
    sourceMap0715 fusedMap0715 sourceMap0715_checked fusedMap0715_checked
    DegreeTwoThreeFiniteComparisons.comparison0715
#print axioms sourceMap0715_checked
#print axioms fusedMap0715_checked
#print axioms certified0715
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

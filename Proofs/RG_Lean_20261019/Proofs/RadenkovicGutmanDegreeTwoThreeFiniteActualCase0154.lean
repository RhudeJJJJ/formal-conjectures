/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0154 : Family 8 := level8.get ⟨250,by decide⟩
def sourceMap0154 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0154 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap0154_checked : acceptsGraphIso
    (source (graph core0154) (root 8) 0 0) DegreeOneSmallSpectrum252.graph sourceMap0154=true := by decide +kernel
theorem fusedMap0154_checked : acceptsGraphIso
    (fused (graph core0154) (root 8) 0 0) DegreeOneSmallSpectrum248.graph fusedMap0154=true := by decide +kernel
theorem certified0154 : Certified (graph core0154) (root 8) 0 0 :=
  of_native_maps core0154 DegreeOneSmallSpectrum252.graph DegreeOneSmallSpectrum248.graph
    sourceMap0154 fusedMap0154 sourceMap0154_checked fusedMap0154_checked
    DegreeTwoThreeFiniteComparisons.comparison0154
#print axioms sourceMap0154_checked
#print axioms fusedMap0154_checked
#print axioms certified0154
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

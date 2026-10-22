/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0170 : Family 9 := level9.get ⟨59,by decide⟩
def sourceMap0170 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0170 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0170_checked : acceptsGraphIso
    (source (graph core0170) (root 9) 0 0) DegreeOneSmallSpectrum419.graph sourceMap0170=true := by decide +kernel
theorem fusedMap0170_checked : acceptsGraphIso
    (fused (graph core0170) (root 9) 0 0) DegreeOneSmallSpectrum475.graph fusedMap0170=true := by decide +kernel
theorem certified0170 : Certified (graph core0170) (root 9) 0 0 :=
  of_native_maps core0170 DegreeOneSmallSpectrum419.graph DegreeOneSmallSpectrum475.graph
    sourceMap0170 fusedMap0170 sourceMap0170_checked fusedMap0170_checked
    DegreeTwoThreeFiniteComparisons.comparison0170
#print axioms sourceMap0170_checked
#print axioms fusedMap0170_checked
#print axioms certified0170
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0334 : Family 9 := level9.get ⟨514,by decide⟩
def sourceMap0334 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0334 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0334_checked : acceptsGraphIso
    (source (graph core0334) (root 9) 0 0) DegreeOneSmallSpectrum728.graph sourceMap0334=true := by decide +kernel
theorem fusedMap0334_checked : acceptsGraphIso
    (fused (graph core0334) (root 9) 0 0) DegreeOneSmallSpectrum708.graph fusedMap0334=true := by decide +kernel
theorem certified0334 : Certified (graph core0334) (root 9) 0 0 :=
  of_native_maps core0334 DegreeOneSmallSpectrum728.graph DegreeOneSmallSpectrum708.graph
    sourceMap0334 fusedMap0334 sourceMap0334_checked fusedMap0334_checked
    DegreeTwoThreeFiniteComparisons.comparison0334
#print axioms sourceMap0334_checked
#print axioms fusedMap0334_checked
#print axioms certified0334
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

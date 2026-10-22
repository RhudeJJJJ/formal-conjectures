/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0384 : Family 9 := level9.get ⟨639,by decide⟩
def sourceMap0384 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0384 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0384_checked : acceptsGraphIso
    (source (graph core0384) (root 9) 0 0) DegreeOneSmallSpectrum722.graph sourceMap0384=true := by decide +kernel
theorem fusedMap0384_checked : acceptsGraphIso
    (fused (graph core0384) (root 9) 0 0) DegreeOneSmallSpectrum702.graph fusedMap0384=true := by decide +kernel
theorem certified0384 : Certified (graph core0384) (root 9) 0 0 :=
  of_native_maps core0384 DegreeOneSmallSpectrum722.graph DegreeOneSmallSpectrum702.graph
    sourceMap0384 fusedMap0384 sourceMap0384_checked fusedMap0384_checked
    DegreeTwoThreeFiniteComparisons.comparison0384
#print axioms sourceMap0384_checked
#print axioms fusedMap0384_checked
#print axioms certified0384
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

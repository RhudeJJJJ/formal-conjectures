/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0540 : Family 10 := level10.get ⟨514,by decide⟩
def sourceMap0540 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0540 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0540_checked : acceptsGraphIso
    (source (graph core0540) (root 10) 0 0) DegreeTwoThreeSpectrum841.graph sourceMap0540=true := by decide +kernel
theorem fusedMap0540_checked : acceptsGraphIso
    (fused (graph core0540) (root 10) 0 0) DegreeOneSmallSpectrum1002.graph fusedMap0540=true := by decide +kernel
theorem certified0540 : Certified (graph core0540) (root 10) 0 0 :=
  of_native_maps core0540 DegreeTwoThreeSpectrum841.graph DegreeOneSmallSpectrum1002.graph
    sourceMap0540 fusedMap0540 sourceMap0540_checked fusedMap0540_checked
    DegreeTwoThreeFiniteComparisons.comparison0540
#print axioms sourceMap0540_checked
#print axioms fusedMap0540_checked
#print axioms certified0540
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

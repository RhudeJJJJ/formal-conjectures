/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0341 : Family 9 := level9.get ⟨530,by decide⟩
def sourceMap0341 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0341 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0341_checked : acceptsGraphIso
    (source (graph core0341) (root 9) 0 0) DegreeOneSmallSpectrum507.graph sourceMap0341=true := by decide +kernel
theorem fusedMap0341_checked : acceptsGraphIso
    (fused (graph core0341) (root 9) 0 0) DegreeOneSmallSpectrum506.graph fusedMap0341=true := by decide +kernel
theorem certified0341 : Certified (graph core0341) (root 9) 0 0 :=
  of_native_maps core0341 DegreeOneSmallSpectrum507.graph DegreeOneSmallSpectrum506.graph
    sourceMap0341 fusedMap0341 sourceMap0341_checked fusedMap0341_checked
    DegreeTwoThreeFiniteComparisons.comparison0341
#print axioms sourceMap0341_checked
#print axioms fusedMap0341_checked
#print axioms certified0341
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

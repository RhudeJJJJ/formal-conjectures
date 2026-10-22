/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0376 : Family 9 := level9.get ⟨617,by decide⟩
def sourceMap0376 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0376 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0376_checked : acceptsGraphIso
    (source (graph core0376) (root 9) 0 0) DegreeOneSmallSpectrum755.graph sourceMap0376=true := by decide +kernel
theorem fusedMap0376_checked : acceptsGraphIso
    (fused (graph core0376) (root 9) 0 0) DegreeOneSmallSpectrum754.graph fusedMap0376=true := by decide +kernel
theorem certified0376 : Certified (graph core0376) (root 9) 0 0 :=
  of_native_maps core0376 DegreeOneSmallSpectrum755.graph DegreeOneSmallSpectrum754.graph
    sourceMap0376 fusedMap0376 sourceMap0376_checked fusedMap0376_checked
    DegreeTwoThreeFiniteComparisons.comparison0376
#print axioms sourceMap0376_checked
#print axioms fusedMap0376_checked
#print axioms certified0376
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

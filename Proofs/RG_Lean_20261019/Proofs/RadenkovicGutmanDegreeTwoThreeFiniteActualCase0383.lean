/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0383 : Family 9 := level9.get ⟨638,by decide⟩
def sourceMap0383 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0383 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0383_checked : acceptsGraphIso
    (source (graph core0383) (root 9) 0 0) DegreeOneSmallSpectrum787.graph sourceMap0383=true := by decide +kernel
theorem fusedMap0383_checked : acceptsGraphIso
    (fused (graph core0383) (root 9) 0 0) DegreeOneSmallSpectrum786.graph fusedMap0383=true := by decide +kernel
theorem certified0383 : Certified (graph core0383) (root 9) 0 0 :=
  of_native_maps core0383 DegreeOneSmallSpectrum787.graph DegreeOneSmallSpectrum786.graph
    sourceMap0383 fusedMap0383 sourceMap0383_checked fusedMap0383_checked
    DegreeTwoThreeFiniteComparisons.comparison0383
#print axioms sourceMap0383_checked
#print axioms fusedMap0383_checked
#print axioms certified0383
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

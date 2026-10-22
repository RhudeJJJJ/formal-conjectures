/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0383 : Family 9 := level9.get ⟨295,by decide⟩
def sourceMap0383 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0383 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0383_checked : acceptsGraphIso
    (source (graph core0383) (root 9) 2 2) DegreeOneMiddleResidualSpectrum903.graph sourceMap0383=true := by decide +kernel
theorem fusedMap0383_checked : acceptsGraphIso
    (fused (graph core0383) (root 9) 2 2) DegreeTwoThreeSpectrum4125.graph fusedMap0383=true := by decide +kernel
theorem certified0383 : Certified (graph core0383) (root 9) 2 2 :=
  of_native_maps core0383 DegreeOneMiddleResidualSpectrum903.graph DegreeTwoThreeSpectrum4125.graph
    sourceMap0383 fusedMap0383 sourceMap0383_checked fusedMap0383_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0383
#print axioms sourceMap0383_checked
#print axioms fusedMap0383_checked
#print axioms certified0383
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

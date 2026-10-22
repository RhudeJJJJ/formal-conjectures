/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0271 : Family 9 := level9.get ⟨96,by decide⟩
def sourceMap0271 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0271 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0271_checked : acceptsGraphIso
    (source (graph core0271) (root 9) 2 2) DegreeOneMiddleResidualSpectrum711.graph sourceMap0271=true := by decide +kernel
theorem fusedMap0271_checked : acceptsGraphIso
    (fused (graph core0271) (root 9) 2 2) DegreeTwoThreeSpectrum4075.graph fusedMap0271=true := by decide +kernel
theorem certified0271 : Certified (graph core0271) (root 9) 2 2 :=
  of_native_maps core0271 DegreeOneMiddleResidualSpectrum711.graph DegreeTwoThreeSpectrum4075.graph
    sourceMap0271 fusedMap0271 sourceMap0271_checked fusedMap0271_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0271
#print axioms sourceMap0271_checked
#print axioms fusedMap0271_checked
#print axioms certified0271
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0281 : Family 9 := level9.get ⟨112,by decide⟩
def sourceMap0281 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0281 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0281_checked : acceptsGraphIso
    (source (graph core0281) (root 9) 2 2) DegreeOneMiddleResidualSpectrum720.graph sourceMap0281=true := by decide +kernel
theorem fusedMap0281_checked : acceptsGraphIso
    (fused (graph core0281) (root 9) 2 2) DegreeTwoThreeSpectrum4120.graph fusedMap0281=true := by decide +kernel
theorem certified0281 : Certified (graph core0281) (root 9) 2 2 :=
  of_native_maps core0281 DegreeOneMiddleResidualSpectrum720.graph DegreeTwoThreeSpectrum4120.graph
    sourceMap0281 fusedMap0281 sourceMap0281_checked fusedMap0281_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0281
#print axioms sourceMap0281_checked
#print axioms fusedMap0281_checked
#print axioms certified0281
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

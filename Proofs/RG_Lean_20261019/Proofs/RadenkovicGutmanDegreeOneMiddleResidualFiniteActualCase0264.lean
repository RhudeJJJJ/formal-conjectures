/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0264 : Family 9 := level9.get ⟨85,by decide⟩
def sourceMap0264 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0264 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0264_checked : acceptsGraphIso
    (source (graph core0264) (root 9) 2 2) DegreeOneMiddleResidualSpectrum681.graph sourceMap0264=true := by decide +kernel
theorem fusedMap0264_checked : acceptsGraphIso
    (fused (graph core0264) (root 9) 2 2) DegreeTwoThreeSpectrum4042.graph fusedMap0264=true := by decide +kernel
theorem certified0264 : Certified (graph core0264) (root 9) 2 2 :=
  of_native_maps core0264 DegreeOneMiddleResidualSpectrum681.graph DegreeTwoThreeSpectrum4042.graph
    sourceMap0264 fusedMap0264 sourceMap0264_checked fusedMap0264_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0264
#print axioms sourceMap0264_checked
#print axioms fusedMap0264_checked
#print axioms certified0264
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

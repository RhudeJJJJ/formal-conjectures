/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0415 : Family 9 := level9.get ⟨370,by decide⟩
def sourceMap0415 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0415 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0415_checked : acceptsGraphIso
    (source (graph core0415) (root 9) 2 2) DegreeOneMiddleResidualSpectrum784.graph sourceMap0415=true := by decide +kernel
theorem fusedMap0415_checked : acceptsGraphIso
    (fused (graph core0415) (root 9) 2 2) DegreeTwoThreeSpectrum4296.graph fusedMap0415=true := by decide +kernel
theorem certified0415 : Certified (graph core0415) (root 9) 2 2 :=
  of_native_maps core0415 DegreeOneMiddleResidualSpectrum784.graph DegreeTwoThreeSpectrum4296.graph
    sourceMap0415 fusedMap0415 sourceMap0415_checked fusedMap0415_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0415
#print axioms sourceMap0415_checked
#print axioms fusedMap0415_checked
#print axioms certified0415
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

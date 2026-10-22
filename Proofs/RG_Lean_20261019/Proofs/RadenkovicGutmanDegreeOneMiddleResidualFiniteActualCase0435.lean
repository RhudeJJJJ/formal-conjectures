/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0435 : Family 9 := level9.get ⟨427,by decide⟩
def sourceMap0435 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0435 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0435_checked : acceptsGraphIso
    (source (graph core0435) (root 9) 2 2) DegreeOneMiddleResidualSpectrum827.graph sourceMap0435=true := by decide +kernel
theorem fusedMap0435_checked : acceptsGraphIso
    (fused (graph core0435) (root 9) 2 2) DegreeTwoThreeSpectrum4419.graph fusedMap0435=true := by decide +kernel
theorem certified0435 : Certified (graph core0435) (root 9) 2 2 :=
  of_native_maps core0435 DegreeOneMiddleResidualSpectrum827.graph DegreeTwoThreeSpectrum4419.graph
    sourceMap0435 fusedMap0435 sourceMap0435_checked fusedMap0435_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0435
#print axioms sourceMap0435_checked
#print axioms fusedMap0435_checked
#print axioms certified0435
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

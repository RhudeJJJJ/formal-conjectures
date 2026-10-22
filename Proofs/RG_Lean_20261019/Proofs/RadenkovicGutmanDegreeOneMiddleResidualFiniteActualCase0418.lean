/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0418 : Family 9 := level9.get ⟨376,by decide⟩
def sourceMap0418 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0418 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0418_checked : acceptsGraphIso
    (source (graph core0418) (root 9) 2 2) DegreeOneMiddleResidualSpectrum789.graph sourceMap0418=true := by decide +kernel
theorem fusedMap0418_checked : acceptsGraphIso
    (fused (graph core0418) (root 9) 2 2) DegreeTwoThreeSpectrum4311.graph fusedMap0418=true := by decide +kernel
theorem certified0418 : Certified (graph core0418) (root 9) 2 2 :=
  of_native_maps core0418 DegreeOneMiddleResidualSpectrum789.graph DegreeTwoThreeSpectrum4311.graph
    sourceMap0418 fusedMap0418 sourceMap0418_checked fusedMap0418_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0418
#print axioms sourceMap0418_checked
#print axioms fusedMap0418_checked
#print axioms certified0418
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0396 : Family 9 := level9.get ⟨332,by decide⟩
def sourceMap0396 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0396 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0396_checked : acceptsGraphIso
    (source (graph core0396) (root 9) 2 2) DegreeOneMiddleResidualSpectrum751.graph sourceMap0396=true := by decide +kernel
theorem fusedMap0396_checked : acceptsGraphIso
    (fused (graph core0396) (root 9) 2 2) DegreeTwoThreeSpectrum4213.graph fusedMap0396=true := by decide +kernel
theorem certified0396 : Certified (graph core0396) (root 9) 2 2 :=
  of_native_maps core0396 DegreeOneMiddleResidualSpectrum751.graph DegreeTwoThreeSpectrum4213.graph
    sourceMap0396 fusedMap0396 sourceMap0396_checked fusedMap0396_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0396
#print axioms sourceMap0396_checked
#print axioms fusedMap0396_checked
#print axioms certified0396
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

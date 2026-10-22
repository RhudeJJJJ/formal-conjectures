/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0210 : Family 9 := level9.get ⟨13,by decide⟩
def sourceMap0210 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0210 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0210_checked : acceptsGraphIso
    (source (graph core0210) (root 9) 2 2) DegreeOneMiddleResidualSpectrum635.graph sourceMap0210=true := by decide +kernel
theorem fusedMap0210_checked : acceptsGraphIso
    (fused (graph core0210) (root 9) 2 2) DegreeTwoThreeSpectrum3858.graph fusedMap0210=true := by decide +kernel
theorem certified0210 : Certified (graph core0210) (root 9) 2 2 :=
  of_native_maps core0210 DegreeOneMiddleResidualSpectrum635.graph DegreeTwoThreeSpectrum3858.graph
    sourceMap0210 fusedMap0210 sourceMap0210_checked fusedMap0210_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0210
#print axioms sourceMap0210_checked
#print axioms fusedMap0210_checked
#print axioms certified0210
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

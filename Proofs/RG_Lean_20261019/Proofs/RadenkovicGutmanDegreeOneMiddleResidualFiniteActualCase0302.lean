/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0302 : Family 9 := level9.get ⟨148,by decide⟩
def sourceMap0302 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0302 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0302_checked : acceptsGraphIso
    (source (graph core0302) (root 9) 2 2) DegreeOneMiddleResidualSpectrum765.graph sourceMap0302=true := by decide +kernel
theorem fusedMap0302_checked : acceptsGraphIso
    (fused (graph core0302) (root 9) 2 2) DegreeTwoThreeSpectrum3904.graph fusedMap0302=true := by decide +kernel
theorem certified0302 : Certified (graph core0302) (root 9) 2 2 :=
  of_native_maps core0302 DegreeOneMiddleResidualSpectrum765.graph DegreeTwoThreeSpectrum3904.graph
    sourceMap0302 fusedMap0302 sourceMap0302_checked fusedMap0302_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0302
#print axioms sourceMap0302_checked
#print axioms fusedMap0302_checked
#print axioms certified0302
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

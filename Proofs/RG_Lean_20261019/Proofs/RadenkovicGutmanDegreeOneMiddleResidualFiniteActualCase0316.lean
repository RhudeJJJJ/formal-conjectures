/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0316 : Family 9 := level9.get ⟨169,by decide⟩
def sourceMap0316 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0316 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0316_checked : acceptsGraphIso
    (source (graph core0316) (root 9) 2 2) DegreeOneMiddleResidualSpectrum794.graph sourceMap0316=true := by decide +kernel
theorem fusedMap0316_checked : acceptsGraphIso
    (fused (graph core0316) (root 9) 2 2) DegreeTwoThreeSpectrum3932.graph fusedMap0316=true := by decide +kernel
theorem certified0316 : Certified (graph core0316) (root 9) 2 2 :=
  of_native_maps core0316 DegreeOneMiddleResidualSpectrum794.graph DegreeTwoThreeSpectrum3932.graph
    sourceMap0316 fusedMap0316 sourceMap0316_checked fusedMap0316_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0316
#print axioms sourceMap0316_checked
#print axioms fusedMap0316_checked
#print axioms certified0316
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

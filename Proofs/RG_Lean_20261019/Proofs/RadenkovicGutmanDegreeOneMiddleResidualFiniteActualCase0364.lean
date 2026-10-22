/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0364 : Family 9 := level9.get ⟨258,by decide⟩
def sourceMap0364 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0364 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0364_checked : acceptsGraphIso
    (source (graph core0364) (root 9) 2 2) DegreeOneMiddleResidualSpectrum882.graph sourceMap0364=true := by decide +kernel
theorem fusedMap0364_checked : acceptsGraphIso
    (fused (graph core0364) (root 9) 2 2) DegreeTwoThreeSpectrum4068.graph fusedMap0364=true := by decide +kernel
theorem certified0364 : Certified (graph core0364) (root 9) 2 2 :=
  of_native_maps core0364 DegreeOneMiddleResidualSpectrum882.graph DegreeTwoThreeSpectrum4068.graph
    sourceMap0364 fusedMap0364 sourceMap0364_checked fusedMap0364_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0364
#print axioms sourceMap0364_checked
#print axioms fusedMap0364_checked
#print axioms certified0364
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
